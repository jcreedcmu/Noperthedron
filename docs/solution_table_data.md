# Solution tree data (Rupert repo)

This repo currently contains the mathematical framework for validating a *solution table* (a large split tree over pose parameter space), but it does **not** yet ship a checked-in table.

To experiment with the authors’ published data, we download their dataset into `external/` (gitignored) and optionally convert it into smaller, Lean-friendly formats.

## Fetch

Run:

```bash
./scripts/fetch-rupert-data.sh
```

This downloads (and pins) a specific upstream commit into:

- `external/rupert/REVISION` (commit hash)
- `external/rupert/data/solution_tree.parquet`
- `external/rupert/data/mapping.csv`
- `external/rupert/data/Ck.csv`

## Inspect

```bash
external/pyvenv/bin/python ./scripts/solution_tree_stats.py
```

## Validate split semantics (best-effort)

This checks that `nodeType=3` split nodes have child intervals matching the intended split scheme.

```bash
external/pyvenv/bin/python ./scripts/check_solution_tree_splits.py --progress
```

## Convert parquet → CSV (skinny)

```bash
apt-get install -y python3-venv
python3 -m venv external/pyvenv
external/pyvenv/bin/pip install pyarrow
python3 ./scripts/parquet_to_csv.py
```

This produces:

- `external/rupert/data/solution_tree.skinny.csv`

## How this connects to the Lean proof

Today, `Solution.Row.ValidGlobal` / `Solution.Row.ValidLocal` are **certificate-carrying** predicates used to drive the logical proof that a *valid* table implies “no Rupert pose exists”.

The next step toward a full end-to-end proof is to introduce a *decidable checker layer* derived from the downloaded dataset (row fields + rational inequalities), and prove:

- `checked_global row = true → row.ValidGlobal tab`
- `checked_local row = true → row.ValidLocal tab`

so that a future `exists_solution_table` can be discharged by a verified (or compiler-trusted) generator/checker pipeline.

## Notes on the upstream schema (observed)

From `solution_tree.parquet` (commit pinned in `external/rupert/REVISION`):

- `ID` is sequential `0..num_rows-1` (so `row.ID = i` is plausible for an `Array Row` encoding).
- `nodeType` row counts:
  - `nodeType=1`: 17,492,530 rows (global leaves)
  - `nodeType=2`: 622,715 rows (local leaves)
  - `nodeType=3`: 585,200 rows (split nodes)
- Interval endpoints:
  - `T1_*`, `V1_*`, `T2_*`, `V2_*` are nonnegative.
  - `A_*` (α) can be negative; a signed integer representation is needed in Lean.
- Split nodes (`nodeType=3`) use the following `split`/`nrChildren` combinations:
  - `split=1` → `nrChildren=4`
  - `split=2` → `nrChildren=30`
  - `split=3` → `nrChildren=4`
  - `split=4` → `nrChildren=15`
  - `split=5` → `nrChildren=30`
  - `split=6` → `nrChildren=32` (matches `2^5`, i.e. halving each parameter)
- Global leaves (`nodeType=1`) have `wx_nominator`, `wy_nominator`, `w_denominator` present, and satisfy a Pythagorean identity:
  - `wx^2 + wy^2 = w_denominator^2` (so `w = (wx,wy)/w_denominator` is a unit vector)
- Several columns are null depending on `nodeType`:
  - `nodeType=3`: `nrChildren`, `IDfirstChild`, `split` present; `r`, `sigma_Q`, and `w*` are null.
  - `nodeType=1`: `w*` present; `nrChildren`, `IDfirstChild`, `split`, `r`, `sigma_Q` are null.
  - `nodeType=2`: `r`, `sigma_Q` present; `nrChildren`, `IDfirstChild`, `split`, `w*` are null.
- `mapping.csv` is a complete `700 × 2619` grid mapping `(i,j) → C_index`, where `C_index` indexes the rows of `Ck.csv`.
- `Ck.csv` has 3,535 data rows (plus a header), with indices `0..3534`.

## Algorithmic meaning (upstream verification notebook)

The upstream `Rupert` repo includes a notebook that verifies the published `solution_tree.parquet`
end-to-end (`src/noperthedron_verification.ipynb`). It clarifies what the row fields are used for:

- `nodeType=1` (“global theorem applications”):
  - Stores a unit covector `w` via integers `(wx_nominator, wy_nominator, w_denominator)` and a vertex index `S_index`.
  - The notebook recomputes:
    - `p̄` as the midpoint of the row’s 5D interval,
    - `ε` as half the maximum interval width,
    - and checks the **rational global theorem** inequality (the shape matches `RationalApprox.GlobalTheorem.Gℚ` vs `maxHℚ`)
      using the row’s `S_index` and `w`.
- `nodeType=2` (“local theorem applications”):
  - Stores two congruent triangles by vertex indices `(P1,P2,P3)` and `(Q1,Q2,Q3)`,
    plus a rational parameter `r = row.r / 1000` and a sign bit `sigma_Q ∈ {0,1}` (the notebook uses `sigma_P = 0`).
  - The notebook checks congruence and then checks the **rational local theorem** preconditions.

This is the intended bridge for a future *decidable checker layer* in Lean: re-express the above checks as
`Bool` predicates over integers/rationals and prove they imply `Row.ValidGlobal` / `Row.ValidLocal`.

## Local row congruence witness (dihedral, observed)

Empirically, every `nodeType=2` row’s `(P,Q)` indices admit a very simple *dihedral-style witness* over the
15-fold rotation index.

Decode a vertex index as:

- `idx = k + 15*i + 45*l`, where `k ∈ {0..14}`, `i ∈ {0,1,2}`, `l ∈ {0,1}`.

Then for each local row there exists:

- `dl ∈ {0,1}` (a global sign flip `(-I)` via `l ↦ l ⊕ dl`), and either
  - **rotation:** `kP = kQ + dk (mod 15)` for all three vertices, or
  - **reflection:** `kP = -kQ + dk (mod 15)` for all three vertices,

with `iP = iQ` position-wise.

The script below checks this property by streaming the parquet file:

```bash
external/pyvenv/bin/python ./scripts/check_solution_tree_local_congruence.py
```
