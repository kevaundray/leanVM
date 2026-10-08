#!/usr/bin/env python3
"""Temporary missing-rate and aggregation confirmation for the selected conversion."""
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path.cwd()
OUT = ROOT / 'round1-evidence'
OUT.mkdir(exist_ok=True)
BASE = os.environ.get('BASE') or 'f52bd991c8623894e7b03a2e50bede6c248ea1ad'
HEAD = 'f19e7b084abad98b6e9d7fc51f07c5e96532c004'
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=16G', '-p', 'MemorySwapMax=0']
ENV = dict(os.environ, CARGO_BUILD_JOBS='4', CARGO_TERM_COLOR='never', RUSTFLAGS='-C target-cpu=native')

def command(args, name, cwd=ROOT, env=None):
    with (OUT / name).open('w') as output:
        p = subprocess.run(list(map(str, args)), cwd=cwd, env=env or ENV, stdout=output, stderr=subprocess.STDOUT)
    if p.returncode:
        print((OUT / name).read_text()[-20000:], flush=True)
        raise RuntimeError(f'{name}: {p.returncode}')

def insert(path, needle, addition):
    source = path.read_text()
    assert source.count(needle) == 1, (path, needle)
    path.write_text(source.replace(needle, needle + addition))

def dump(value, filename, indent=4):
    space = ' ' * indent
    return '\n' + space + 'if let Some(dir) = std::env::var_os("ROUND1_PROOF_DIR") {\n' + space + f'    std::fs::write(std::path::Path::new(&dir).join({filename}), {value}.to_bytes()).unwrap();\n' + space + '}\n'

metadata = dict(base=BASE, head=HEAD, flags=ENV['RUSTFLAGS'], affinity=sorted(os.sched_getaffinity(0)), files={})
for path in ['/proc/cpuinfo', '/proc/sys/kernel/perf_event_paranoid', '/proc/meminfo', '/sys/fs/cgroup/cpu.max']:
    if Path(path).exists():
        metadata['files'][path] = Path(path).read_text()
command(['rustc', '+1.99.0', '-vV'], 'rustc.txt')
command(['lscpu'], 'lscpu.txt')
worker_source = OUT / 'worker-count.rs'
worker_source.write_text('fn main() { println!("{}", std::thread::available_parallelism().unwrap()); }\n')
command(SCOPE + ['rustc', '+1.99.0', worker_source, '-o', OUT / 'worker-count'], 'worker-build.log')
command(SCOPE + [OUT / 'worker-count'], 'worker-count.txt')
metadata['default_workers'] = int((OUT / 'worker-count.txt').read_text().strip())
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2))

binaries = {}
for side, revision in [('base', BASE), ('head', HEAD)]:
    tree = Path('/tmp/round1-confirm-' + side)
    command(['git', 'worktree', 'add', '--detach', tree, revision], f'checkout-{side}.log')
    # Identical serialization hooks execute after timed proving and verification.
    path = tree / 'bins/leanvm/src/workload.rs'
    insert(path, '        let proof_bytes = proof.to_bytes().len();', dump('proof', '"leaf.bin"', 8))
    path = tree / 'bins/leanvm/src/aggregate.rs'
    insert(path, '    let (proof, output) = (&proved.proof, proved.output);', dump('proof', '"leaf.bin"'))
    insert(path, '    let stats = tree.stats(kind);', dump('proof', 'format!("{}.bin", name.replace(\' \', "_"))'))
    insert(path, '    let (_, root_verify) = quiet.measure_quiet(|_| tree.verify(&root, &outputs).expect("the root verifies"));', dump('root', '"root.bin"'))
    target = Path('/tmp/round1-confirm-native-' + side)
    env = dict(ENV, CARGO_TARGET_DIR=str(target))
    if os.environ.get('ROUND1_PREPARE_ONLY'):
        continue
    command(SCOPE + ['cargo', '+1.99.0', 'build', '--release', '-p', 'leanvm-cli'], f'build-{side}.log', tree, env)
    binaries[side] = target / 'release/leanvm'
    command(['objdump', '-d', '-C', binaries[side]], f'assembly-{side}.txt')
    command(['nm', '-C', binaries[side]], f'symbols-{side}.txt')
if os.environ.get('ROUND1_PREPARE_ONLY'):
    raise SystemExit(0)

records = []
references = {}

def measured(side, case, pair, workers, args, timed=True):
    name = f'{case}-w{workers}-p{pair}-{side}'
    proof_dir = OUT / 'proofs' / name
    proof_dir.mkdir(parents=True)
    with open('/tmp/leanvm-bench.lock', 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        deadline = time.monotonic() + 600
        while os.getloadavg()[0] >= 12:
            if time.monotonic() > deadline:
                raise RuntimeError('load remained above 12')
            time.sleep(5)
        before = os.getloadavg()
        env = dict(ENV, ROUND1_PROOF_DIR=str(proof_dir))
        env.pop('LEANVM_NUM_THREADS', None)
        if workers != 'default':
            env['LEANVM_NUM_THREADS'] = str(workers)
        command(SCOPE + ['/usr/bin/time', '-v', binaries[side]] + args + ['--repeat', '1', '--cooldown', '0', '--tracing'], name + '.log', env=env)
        after = os.getloadavg()
        record = dict(name=name, case=case, pair=pair, side=side, workers=workers, timed=timed, load_before=before, load_after=after, accepted=max(before[0], after[0]) <= 20, proofs={})
        files = sorted(proof_dir.glob('*.bin'))
        assert len(files) == (4 if case.startswith('tree') else 1), (case, files)
        for path in files:
            data = path.read_bytes()
            key = (case, path.name)
            if key in references:
                assert data == references[key], f'literal proof mismatch: {name}/{path.name}'
            else:
                references[key] = data
            record['proofs'][path.name] = dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
        records.append(record)
        (OUT / 'records.json').write_text(json.dumps(records, indent=2))
        print(json.dumps(record), flush=True)
        if not record['accepted']:
            raise RuntimeError('overloaded sample discarded')

# The already-measured rate-one leaf matrix is not repeated.
cases = [
    ('leaf-rate2', ['leanxmss', '--n', '100', '--log-inv-rate', '2']),
    ('tree-rate2', ['aggregate', '--program', 'leanxmss', '--n', '2', '--leaves', '4', '--arity0', '2', '--arity', '2', '--leaf-log-inv-rate', '2', '--log-inv-rate', '2']),
]
for case, args in cases:
    for workers in [1, 4, 8, 'default']:
        for pair in range(5):
            for side in (['base', 'head'] if pair % 2 == 0 else ['head', 'base']):
                measured(side, case, pair, workers, args)

# Boundary rates are correctness/byte-identity smokes, not timing distributions.
for rate in [1, 3, 4]:
    for side in ['base', 'head']:
        measured(side, f'leaf-smoke-rate{rate}', 0, 4, ['leanxmss', '--n', '2', '--log-inv-rate', str(rate)], timed=False)
        measured(side, f'tree-smoke-rate{rate}', 0, 4, ['aggregate', '--program', 'leanxmss', '--n', '2', '--leaves', '4', '--arity0', '2', '--arity', '2', '--leaf-log-inv-rate', str(rate), '--log-inv-rate', str(rate)], timed=False)

(OUT / 'proof-equality.json').write_text(json.dumps(dict(files=sum(len(r['proofs']) for r in records), cases=len(references), literal_equal=True), indent=2))
print('All leaf, first-node, higher-node and root proofs literally equal per case; production verification passed.', flush=True)
