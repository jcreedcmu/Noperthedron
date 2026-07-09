#!/usr/bin/env python3
"""Generate the VerifiedKernel chunk tree: load modules (literal row chunks),
the dispatch/getter module, validation modules (ChunkOk theorems), the
ChunkOkBelow combine chain, and the final capstone. Run from the repo root.

Phases (pass as argv[1]):
  load      - VerifiedKernel/Gen/LoadNNN.lean (8192 rows each, 512-row chunks)
  dispatch  - VerifiedKernel/Gen/Dispatch.lean
  validate  - VerifiedKernel/Gen/ValidateNNN.lean (8 ChunkOk theorems each)
  combine   - VerifiedKernel/Gen/CombineNN.lean + Final.lean
"""
import sys, os

N = 2051521
C = 512
ROWS_PER_LOAD = 8192
NCHUNKS = (N + C - 1) // C          # 4007
NLOAD = (N + ROWS_PER_LOAD - 1) // ROWS_PER_LOAD  # 251
CHUNKS_PER_VALIDATE = 8
NVAL = (NCHUNKS + CHUNKS_PER_VALIDATE - 1) // CHUNKS_PER_VALIDATE  # 501

os.makedirs('VerifiedKernel/Gen', exist_ok=True)

def gen_load(only=None):
    for i in range(NLOAD):
        if only is not None and i != only:
            continue
        a = i * ROWS_PER_LOAD
        b = min((i + 1) * ROWS_PER_LOAD, N)
        with open(f'VerifiedKernel/Gen/Load{i:03}.lean', 'w') as f:
            f.write(f"""import Noperthedron.SolutionTable.Load

/-! GENERATED (scripts/gen_kernel_chunks.py): rows [{a}, {b}) of the solution
tree as literal 512-row chunks. Requires `solution_tree_v6.csv` at the repo
root. -/

namespace Noperthedron.Solution

load_csv_chunks "solution_tree_v6.csv" from {a} to {b} chunkSize {C}

end Noperthedron.Solution
""")

def gen_dispatch():
    imports = "\n".join(f"import VerifiedKernel.Gen.Load{i:03}" for i in range(NLOAD))
    with open('VerifiedKernel/Gen/Dispatch.lean', 'w') as f:
        f.write(f"""import Noperthedron.SolutionTable.Assemble
{imports}

/-! GENERATED (scripts/gen_kernel_chunks.py): the digit-curried dispatch over
all {NCHUNKS} loaded chunks and the row getter for the kernel run. -/

namespace Noperthedron.Solution

assemble_row_dispatch tableDispatch rows {N} chunkSize {C}

/-- The full-table row getter: dispatch walk ≤ 32 cells plus ≤ {C} list
cells per access. -/
noncomputable def getRow : ℕ → Row := rowGetter tableDispatch {C}

end Noperthedron.Solution
""")

def read_node_types():
    """Row cost classes: 1 = global, 2 = local, 3 = small split
    (nrChildren < 15), 4 = full split (nrChildren >= 15)."""
    types = []
    with open('solution_tree_v6.csv') as f:
        next(f)
        for line in f:
            parts = line.split(',', 3)
            t = int(parts[1])
            if t == 3 and parts[2] and int(parts[2]) >= 15:
                t = 4
            types.append(t)
    assert len(types) == N, len(types)
    return types

# per-row kernel memory (MB) and time (s) model, calibrated on probes
# 2026-07-08 (Validate0000 tree-top full splits; chunk 7877 binary splits;
# 24-row local range at row 1867264). Local recalibrated 2026-07-09 after
# the pythonVertexA kernel-walk fix (6501604): pure-local RangeOk probes at
# rows 1205362/1205370/1867263 measure 0.67-0.80 s and 138-155 MB per row;
# coefficients carry ~15% margin.
COST_MB = {1: 25, 2: 175, 3: 21, 4: 130}
COST_S  = {1: 0.30, 2: 0.85, 3: 0.08, 4: 0.35}
MB_BUDGET = 1600      # per-declaration term-cache budget
S_PER_FILE = 500      # target kernel seconds per file
MAX_RANGE = 1000

def make_ranges(types):
    ranges = []
    a = 0
    while a < N:
        mb = 0.0
        b = a
        while b < N and b - a < MAX_RANGE:
            mb += COST_MB[types[b]]
            if mb > MB_BUDGET and b > a:
                break
            b += 1
        ranges.append((a, b))
        a = b
    return ranges

def make_files(types, ranges):
    files = []
    cur, sec = [], 0.0
    for (a, b) in ranges:
        cost = sum(COST_S[types[i]] for i in range(a, b))
        cur.append((a, b))
        sec += cost
        if sec >= S_PER_FILE:
            files.append(cur)
            cur, sec = [], 0.0
    if cur:
        files.append(cur)
    return files

def gen_validate(only=None):
    types = read_node_types()
    ranges = make_ranges(types)
    files = make_files(types, ranges)
    print(f"{len(ranges)} ranges in {len(files)} files")
    spans = []
    for v, rs in enumerate(files):
        a0, bend = rs[0][0], rs[-1][1]
        spans.append((a0, bend))
        if only is not None and v != only:
            continue
        thms = []
        for (a, b) in rs:
            thms.append(f"private theorem r_{a} : RangeOk getRow {N} {a} {b} := by\n  decide +kernel")
        fold = [f"private theorem s_{rs[0][1]} : RangeOk getRow {N} {a0} {rs[0][1]} := r_{a0}"]
        for (a, b) in rs[1:]:
            prev = fold[-1].split()[2]
            pend = prev.split('_')[1]
            fold.append(f"private theorem s_{b} : RangeOk getRow {N} {a0} {b} :=\n"
                        f"  {prev}.append (by norm_num) r_{a}")
        body = "\n\n".join(thms) + "\n\n" + "\n".join(fold)
        with open(f'VerifiedKernel/Gen/Validate{v:04}.lean', 'w') as f:
            f.write(f"""import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[{a0}, {bend}). -/

namespace Noperthedron.Solution

set_option Elab.async false

{body}

/-- Rows `[{a0}, {bend})` are valid. -/
theorem rangeOk_{a0}_{bend} : RangeOk getRow {N} {a0} {bend} := s_{bend}

end Noperthedron.Solution
""")
    return spans

def gen_combine():
    types = read_node_types()
    spans = make_files(types, make_ranges(types))
    spans = [(rs[0][0], rs[-1][1]) for rs in spans]
    PER = 64
    ncomb = (len(spans) + PER - 1) // PER
    for m in range(ncomb):
        batch = spans[m*PER : (m+1)*PER]
        v0 = m * PER
        a0 = 0 if m == 0 else spans[0][0]
        start = spans[m*PER][0]
        imports = "\n".join(f"import VerifiedKernel.Gen.Validate{v0+i:04}" for i in range(len(batch)))
        prev = (f"import VerifiedKernel.Gen.Combine{m-1:02}\n" if m > 0 else "")
        steps = []
        if m == 0:
            steps.append(f"private theorem c_{batch[0][1]} : RangeOk getRow {N} 0 {batch[0][1]} := rangeOk_{batch[0][0]}_{batch[0][1]}")
            rest = batch[1:]
        else:
            steps.append(f"private theorem c_{batch[0][1]} : RangeOk getRow {N} 0 {batch[0][1]} :=\n"
                         f"  combined_{start}.append (by norm_num) rangeOk_{batch[0][0]}_{batch[0][1]}")
            rest = batch[1:]
        for (a, b) in rest:
            prev_end = steps[-1].split()[2].split('_')[1]
            steps.append(f"private theorem c_{b} : RangeOk getRow {N} 0 {b} :=\n"
                         f"  c_{prev_end}.append (by norm_num) rangeOk_{a}_{b}")
        endb = batch[-1][1]
        with open(f'VerifiedKernel/Gen/Combine{m:02}.lean', 'w') as f:
            f.write(f"""{prev}{imports}

/-! GENERATED (scripts/gen_kernel_chunks.py): fold rows [0, {endb}). -/

namespace Noperthedron.Solution

{chr(10).join(steps)}

/-- Rows `[0, {endb})` are valid. -/
theorem combined_{endb} : RangeOk getRow {N} 0 {endb} := c_{endb}

end Noperthedron.Solution
""")
    with open('VerifiedKernel/Gen/Final.lean', 'w') as f:
        f.write(f"""import VerifiedKernel.Gen.Combine{ncomb-1:02}

/-! GENERATED (scripts/gen_kernel_chunks.py): every index of the full table
satisfies `Row.ValidIxAt`, and row 0 carries `rowZero.interval`. -/

namespace Noperthedron.Solution

theorem allRows_validIxAt : ∀ i : Fin {N}, Row.ValidIxAt getRow {N} i :=
  validIxAt_of_rangeOk combined_{N}

theorem row0_interval : (getRow 0).interval = rowZero.interval := by
  decide +kernel

end Noperthedron.Solution
""")

phase = sys.argv[1] if len(sys.argv) > 1 else 'all'
only = int(sys.argv[2]) if len(sys.argv) > 2 else None
if phase in ('load', 'all'): gen_load(only)
if phase in ('dispatch', 'all'): gen_dispatch()
if phase in ('validate', 'all'): gen_validate(only)
if phase in ('combine', 'all'): gen_combine()
print("generated phase:", phase, "only:", only)
