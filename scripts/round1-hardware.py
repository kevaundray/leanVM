#!/usr/bin/env python3
"""Temporary paired Round1 experiment, removed before shipping."""
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
HEAD = os.environ.get('CANDIDATE') or '721c4ce1'
SCOPE = ['systemd-run', '--user', '--scope', '-q', '-p', 'MemoryMax=16G', '-p', 'MemorySwapMax=0']
ENV = dict(os.environ, CARGO_BUILD_JOBS='4', CARGO_TERM_COLOR='never', RUSTFLAGS='-C target-cpu=native')

def command(args, name, cwd=ROOT, env=None):
    with (OUT / name).open('w') as output:
        p = subprocess.run(list(map(str, args)), cwd=cwd, env=env or ENV, stdout=output, stderr=subprocess.STDOUT)
    if p.returncode:
        print((OUT / name).read_text()[-20000:], flush=True)
        raise RuntimeError(f'{name}: {p.returncode}')

metadata = dict(base=BASE, head=HEAD, flags=ENV['RUSTFLAGS'], affinity=sorted(os.sched_getaffinity(0)), files={})
for path in ['/proc/cpuinfo', '/proc/sys/kernel/perf_event_paranoid', '/proc/meminfo']:
    metadata['files'][path] = Path(path).read_text()
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2))
command(['rustc', '+1.99.0', '-vV'], 'rustc.txt')
command(['lscpu'], 'lscpu.txt')
binaries = {}
tests = {}
for side, revision in [('base', BASE), ('head', HEAD)]:
    tree = Path('/tmp/round1-hardware-' + side)
    command(['git', 'worktree', 'add', '--detach', tree, revision], f'checkout-{side}.log')
    # Both variants receive identical capture code outside timed proof spans.
    path = tree / 'bins/leanvm/src/workload.rs'
    source = path.read_text()
    needle = '        let proof_bytes = proof.to_bytes().len();'
    assert source.count(needle) == 1
    source = source.replace(needle, '        if let Some(path) = std::env::var_os("ARM_ATTRIBUTION_PROOF") {\n            std::fs::write(path, proof.to_bytes()).unwrap();\n        }\n' + needle)
    path.write_text(source)
    path = tree / 'crates/flock/src/zerocheck.rs'
    source = path.read_text()
    needle = '    ps.add_scalars(&round1);'
    assert source.count(needle) == 1
    source = source.replace(needle, (ROOT / 'scripts/round1-capture-hook.rs').read_text() + needle)
    path.write_text(source)
    path = tree / 'crates/flock/src/zerocheck/round1.rs'
    source = path.read_text()
    assert source.rstrip().endswith('}')
    source = source.rstrip()[:-1] + (ROOT / 'scripts/round1-captured.rs').read_text() + '\n}\n'
    path.write_text(source)
    target = Path('/tmp/round1-native-' + side)
    env = dict(ENV, CARGO_TARGET_DIR=str(target))
    command(SCOPE + ['cargo', '+1.99.0', 'build', '--release', '-p', 'leanvm-cli'], f'build-{side}.log', tree, env)
    binaries[side] = target / 'release/leanvm'
    command(['objdump', '-d', '-C', binaries[side]], f'assembly-{side}.txt')
    command(['nm', '-C', binaries[side]], f'symbols-{side}.txt')
    command(SCOPE + ['cargo', '+1.99.0', 'test', '--release', '-p', 'flock', '--lib', '--no-run', '--message-format=json'], f'build-test-{side}.log', tree, env)
    artifacts = [json.loads(line) for line in (OUT / f'build-test-{side}.log').read_text().splitlines() if line.startswith('{')]
    tests[side], = [a['executable'] for a in artifacts if a.get('reason') == 'compiler-artifact' and a.get('executable') and a['profile']['test']]
    command(SCOPE + [tests[side], 'zerocheck::round1::tests', '--test-threads=4'], f'correctness-{side}.log', env=dict(env, LEANVM_NUM_THREADS='4'))

records = []

def measured(side, name, workers, args, extra=None, proof=True):
    with open('/tmp/leanvm-bench.lock', 'a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        deadline = time.monotonic() + 600
        while os.getloadavg()[0] >= 12:
            if time.monotonic() > deadline:
                raise RuntimeError('load remained above 12')
            time.sleep(5)
        before = os.getloadavg()
        env = dict(ENV)
        env.pop('LEANVM_NUM_THREADS', None)
        if workers != 'default':
            env['LEANVM_NUM_THREADS'] = str(workers)
        if proof:
            env['ARM_ATTRIBUTION_PROOF'] = str(OUT / (name + '.bin'))
        env.update(extra or {})
        command(SCOPE + ['/usr/bin/time', '-v'] + args, name + '.log', env=env)
        after = os.getloadavg()
        record = dict(name=name, side=side, workers=workers, load_before=before, load_after=after, accepted=max(before[0], after[0]) <= 20)
        if proof:
            data = (OUT / (name + '.bin')).read_bytes()
            record.update(proof_bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
        records.append(record)
        (OUT / 'records.json').write_text(json.dumps(records, indent=2))
        print(json.dumps(record), flush=True)
        if not record['accepted']:
            raise RuntimeError('overloaded sample discarded')

for workers in [1, 4, 8, 'default']:
    for pair in range(5):
        for side in (['base', 'head'] if pair % 2 == 0 else ['head', 'base']):
            measured(side, f'proof-w{workers}-p{pair}-{side}', workers, [binaries[side], 'leanxmss', '--n', '100', '--repeat', '1', '--cooldown', '0', '--tracing'])

capture = OUT / 'round1-inputs'
measured('base', 'capture', 1, [binaries['base'], 'leanxmss', '--n', '100', '--repeat', '1', '--cooldown', '0'], {'ARM_ATTRIBUTION_INPUT_DIR': str(capture)})
for cls in [9, 0, 19]:
    for pair in range(5):
        for side in (['base', 'head'] if pair % 2 == 0 else ['head', 'base']):
            measured(side, f'components-class{cls}-p{pair}-{side}', 1,
                     [tests[side], 'zerocheck::round1::tests::diagnostic_round1_components', '--exact', '--ignored', '--nocapture'],
                     {'ROUND1_INPUT_DIR': str(capture / f'class{cls}'), 'ROUND1_REPEATS': '3', 'ROUND1_SAMPLE_WINDOWS': '64'}, proof=False)

proofs = [OUT / (r['name'] + '.bin') for r in records if 'sha256' in r]
expected = proofs[0].read_bytes()
assert all(p.read_bytes() == expected for p in proofs), 'literal proof byte mismatch'
(OUT / 'proof-equality.json').write_text(json.dumps(dict(files=len(proofs), bytes=len(expected), sha256=hashlib.sha256(expected).hexdigest(), literal_equal=True)))
print('Literal equality and production verification passed for every paired proof.', flush=True)
