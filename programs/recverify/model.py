"""Model the guest's cycles and committed words per inner proof under field-multiply options (README.md).

`python3 programs/recverify/model.py programs/recverify/measured.json`, from the workspace root, after building the host and the guest.

    cycles_X = plumbing (+ soft float, unless counted as removed) + sum_op n_op * c_X(op)
    rows_X   = the same per table, the new classes CLMUL and GF192 aside
    words_X  = stack_sizes(rows_X of the eight tables, log_ram 21, log_advice 16) + new-class rows * words per row

`measured.json` holds, per run, the measured cycles and rows (`recverify-host`), the operation counts (`profile.py ops` on the counting build) and the plumbing and soft float split (`profile.py classes`). `shared` (core runs) is what k proofs of one program would share: building the circuits (`initialize` under `replay`) and everything outside `replay` (the program's setup, reading the advice, committing). CLMUL and GF192 are hypothetical classes; their words per row are estimates.
"""

import json
import math
import subprocess
import sys
from pathlib import Path

ELF = "programs/recverify/guest/target/riscv64im-leanvm-zkvm/release/recverify"
TABLES = ["ALU", "LOAD", "STORE", "SHIFT", "MUL", "MULH", "DIV", "HASH"]
NEW_WORDS = {"CLMUL": 34, "GF192": 170}
OPS = ["Emul", "ExK", "Esq", "Kmul", "Ksq"]
# Cycles, rows per table (net of the loop) per operation. `sw` is `prim` runs of this guest. `clmul` and `gf192` were priced with
# stand-ins not carried here (a carry-less multiply pair, and a block instruction in place of a GF(2^192) product), so they are
# estimates. Ksq is estimated as a third of Esq (software) or a Kmul (Zbc).
COST = {
    "sw": {
        "Emul": (1240, {"ALU": 674, "LOAD": 115, "STORE": 100, "SHIFT": 63, "MUL": 288}),
        "ExK": (630, {"ALU": 341, "LOAD": 56, "STORE": 50, "SHIFT": 39, "MUL": 144}),
        "Esq": (140, {"ALU": 82, "LOAD": 8, "STORE": 2, "SHIFT": 48}),
        "Kmul": (206, {"ALU": 112, "LOAD": 17, "STORE": 16, "SHIFT": 13, "MUL": 48}),
        "Ksq": (47, {"ALU": 27, "LOAD": 3, "STORE": 1, "SHIFT": 16}),
    },
    "clmul": {
        "Emul": (76, {"ALU": 39, "LOAD": 5, "STORE": 2, "SHIFT": 18, "CLMUL": 12}),
        "ExK": (51, {"ALU": 23, "LOAD": 2, "STORE": 2, "SHIFT": 18, "CLMUL": 6}),
        "Esq": (52, {"ALU": 24, "LOAD": 2, "STORE": 2, "SHIFT": 18, "CLMUL": 6}),
        "Kmul": (15, {"ALU": 7, "SHIFT": 6, "CLMUL": 2}),
        "Ksq": (15, {"ALU": 7, "SHIFT": 6, "CLMUL": 2}),
    },
    "gf192": {op: (14, {"LOAD": 5, "STORE": 8, "GF192": 1}) for op in OPS},
}
LIMIT = 1 << 28


def words(rows):
    heights = [str(max(0, round(rows.get(t, 0)))) for t in TABLES]
    out = subprocess.run(["target/release/recverify-host", ELF, "words", "21", "16", *heights], capture_output=True, text=True, check=True).stdout
    base = int(out.split()[1])
    return base + sum(rows.get(c, 0) * w for c, w in NEW_WORDS.items())


def model(run, option, no_float):
    # Measured plumbing (and soft float), plus every field operation at the option's cost.
    cycles = run["plumbing"]["T"]
    rows = dict(run["plumbing"]["rows"])
    if not no_float:
        cycles += run["float"]["T"]
        for t, r in run["float"]["rows"].items():
            rows[t] = rows.get(t, 0) + r
    for op in OPS:
        n = run["ops"][op]
        c_x, r_x = COST[option][op]
        cycles += n * c_x
        for t, r in r_x.items():
            rows[t] = rows.get(t, 0) + n * r
    w = words(rows)
    per_row = (w - words({})) / cycles
    return cycles, rows, w, per_row


runs = json.loads(Path(sys.argv[1]).read_text())
for name, run in runs.items():
    for no_float in (False, True):
        for option in ("sw", "clmul", "gf192"):
            cycles, rows, w, per_row = model(run, option, no_float)
            fit = (LIMIT - words({})) / per_row
            new = {c: round(rows.get(c, 0)) for c in NEW_WORDS if rows.get(c, 0)}
            print(
                f"{name:24} {option:6} {'no float' if no_float else 'float   '} cycles {cycles / 1e6:9.2f}M (2^{math.log2(cycles):.2f}) "
                f"words {w / 1e6:10.1f}M (2^{math.log2(w):.2f}) {per_row:5.1f} w/cycle, one proof holds {fit / 1e6:5.2f}M cycles, "
                f"x{cycles / fit:6.2f} {new}"
            )

# k inner proofs of one program in one guest run: the circuits' construction and the program's setup once, the rest per proof.
for name, run in runs.items():
    if "shared" not in run:
        continue
    for option in ("sw", "clmul", "gf192"):
        cycles, _, w, per_row = model(run, option, True)
        per_proof = cycles - run["shared"]
        fit = (LIMIT - words({})) / per_row
        for k in (1, 2):
            total = run["shared"] + k * per_proof
            print(
                f"{name:24} {option:6} no float k={k} cycles {total / 1e6:8.2f}M words {(total * per_row + words({})) / 1e6:9.1f}M "
                f"x{total / fit:5.2f} of one proof"
            )
