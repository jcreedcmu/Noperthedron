# Computational Step Formalization Plan

This is a plan for the remaining work to help Claude make progress. It
covers the remaining work of "the computational part" of the overall
proof.

## Context

The Noperthedron formalization proves that a specific convex polyhedron lacks Rupert's property.
The proof reduces to showing no "Rupert solution" exists anywhere in a 5D parameter space
(tightInterval). The parameter space is covered by a decision tree (~18M nodes) where each
leaf is either a "global" or "local" node, and the formalization must verify that every leaf
rules out Rupert solutions in its sub-region.

**What's done:** The continuous theorems (global_theorem, local_theorem), rational approximation
bridge (rational_global, rational_local), and the tree recursion (valid_imp_not_rupert_ix) are
all proven. The tree recursion dispatches to `valid_global_imp_no_rupert` and
`valid_local_imp_no_rupert` at leaves.

**What remains:** 4 sorry's connecting the row data to the rational theorems, plus data ingestion.

---

## Milestone Dependency Graph

```
M1: Global validity checker (Bool)
    |
    v
M2: valid_global_imp_no_rupert ──────┐
                                     |
M3: Local validity checker (Bool)    |
    |                                |
    v                                v
M4: valid_local_imp_no_rupert    M5: Data ingestion + exists_solution_table
    |                                ^
    └────────────────────────────────┘
```

M1 and M3 are independent of each other. M2 depends on M1. M4 depends on M3.
M5 depends on M2 and M4 (and on having the actual data file).

---

## M1: Global validity checker (Bool-returning)

**Files:** `SolutionTable/Basic.lean` (new defs), possibly a new `SolutionTable/GlobalCheck.lean`

**Goal:** Define `Row.checkGlobal : Table → Row → Bool` such that `checkGlobal` returns true
iff the row data constitutes a valid application of the rational global theorem.

**Key design:**
A global row's interval defines an axis-aligned box. The rational global theorem
(`rational_global`) needs:
- A center pose `pbar` (center of the box)
- A radius `ε` (max half-width across all 5 dimensions)
- `pbar ∈ fourInterval` (all params in [-4, 4])
- A vertex `S ∈ poly_` (looked up via `S_index` in `nopertList`)
- A unit vector `w` (from `wx_numerator`, `wy_numerator`, `w_denominator`)
- The inequality `Gℚ pbar ε S w > maxHℚ pbar poly_ ε w`

The checker computes all these from the row fields and checks:
1. `nodeType = 1`
2. `w` is a unit vector (wx² + wy² = w_denom²)
3. Center pose is in `fourInterval` (should always hold for tightInterval subboxes)
4. The `Gℚ > maxHℚ` inequality (a rational comparison after multiplying through)

Since `Gℚ` and `maxHℚ` involve `sinℚ`/`cosℚ` (degree-25 Taylor polynomials) applied to
rational arguments, and `κ = 10⁻¹⁰` is rational, all intermediate values are rational.
The checker can work entirely with `ℚ` (or `ℤ` with a common denominator).

**Performance note:** Each `sinℚ`/`cosℚ` evaluation is a degree-25 polynomial in ℚ. For
`native_decide`, this should be fast. For kernel `decide`, it would likely be too slow.

**Early Validation:** We should be able to extract a suitable row from
`data/solution_tree.csv`, manually convert it to a lean literal
`Table` consisting of just one `Row`, and confirm that the checker
accepts it.

---

## M2: valid_global_imp_no_rupert

**File:** `SolutionTable/Global.lean`

**Goal:** Prove `checkGlobal tab row = true → ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull`

**Proof sketch:**
1. Extract the decoded data from `checkGlobal = true`
2. Show `row.toPoseInterval ⊆ center.closed_ball ε` (axis-aligned box ⊆ sup-norm ball
   with ε = max half-width)
3. Show the center pose is in `fourInterval`
4. Build a `κApproxPoly` between `nopert.vertices` and the rational approximation `nopert_`
5. Build a `RationalGlobalTheoremPrecondition` from the extracted data
6. Apply `rational_global` to get `¬ ∃ p ∈ center.closed_ball ε, RupertPose p nopert.hull`
7. Conclude by the subset inclusion

**Key auxiliary lemmas needed:**
- `closed_ball_superset_of_max_halfwidth`: the axis-aligned box from a row is contained
  in a closed_ball centered at the box center with radius = max half-width
- `nopert_kapprox`: the noperthedron vertices have a κ-approximation (this is a concrete
  rational computation about the specific vertex coordinates C1, C2, C3)

---

## M3: Local validity checker (Bool-returning)

**File:** `SolutionTable/Basic.lean` or new `SolutionTable/LocalCheck.lean`

**Goal:** Define `Row.checkLocal : Table → Row → Bool`

Similar to M1 but checking the preconditions of `rational_local`:
1. `nodeType = 2`
2. Triangle congruence (`P.Congruent Q`) -- this is about specific noperthedron triangles
3. `Aεℚ` conditions (sign and inner product bounds for each triangle vertex)
4. `Bεℚ` conditions (angle cosine bounds involving `UpperSqrt`)
5. `BoundDeltaℚ` (midpoint distance bounds)
6. `BoundRℚ` (projection norm lower bounds via `LowerSqrt`)
7. `κSpanning` conditions (three inner product inequalities)

**UpperSqrt/LowerSqrt:** These are rational functions that over/under-approximate √x.
The row data may encode which specific rational approximant to use, or a fixed one
may suffice. Need to choose concrete `UpperSqrt` and `LowerSqrt` instances -- likely
a few Newton iterations of √x starting from a rational initial guess.

**Early Validation:** We should be able to extract a suitable row from
`data/solution_tree.csv`, manually convert it to a lean literal
`Table` consisting of just one `Row`, and confirm that the checker
accepts it.


---

## M4: valid_local_imp_no_rupert

**File:** `SolutionTable/Local.lean`

Same pattern as M2 but applying `rational_local`. Additionally needs:
- Triangle congruence proof for specific noperthedron triangle pairs
- Construction of `UpperSqrt`/`LowerSqrt` witnesses

---

## M5: Data ingestion + exists_solution_table

**File:** `ComputationalStep.lean` (and data files)

**Approach:**
1. Convert the CSV/parquet from the paper authors into a compact text format
2. Use `include_str` to embed it as a compile-time string constant
3. Write a parser `parseTable : String → Option (Array Solution.Row)`
4. Define `solutionTable : Solution.Table := (parseTable rawData).get!`
5. Prove `exists_solution_table` by:
   - `tab.Valid`: via `native_decide` (since `Row.Valid` is `Decidable`)
   - `tightInterval ⊆ tab[0].toPoseInterval`: needs π bounds to show the rational
     interval endpoints cover the irrational tightInterval bounds

**The π bound:** `tightInterval` uses `2π/15` and `π/2`. The table uses integer
multiples of `1/DENOM = 1/15360000`. Need to show e.g. `6434 / 15360000 ≥ 2π/15`
(or whatever the actual boundary values are). This requires an upper bound on π
like `π < 6434 * 15 / (2 * 15360000)`. Mathlib has `Real.pi_lt_3141593`.

**Performance testing plan:**
- Start with a hand-crafted 1-row table (a single global leaf)
- Test `native_decide` on `tab.Valid` for that 1-row table
- Scale to ~10, ~100, ~1000 rows to profile
- If `native_decide` on the full table is too slow, consider:
  - Splitting into multiple tables checked independently
  - Using a custom elaborator that checks validity at elaboration time and
    produces a proof term directly

---

## Suggested execution order

1. **M1** (global checker) -- most self-contained, establishes the pattern
2. **M2** (global soundness) -- validates that the checker design works end-to-end
3. **M5 partial** (data ingestion for 1 global row) -- test the full pipeline
4. **M3** (local checker) -- follows M1's pattern but more complex
5. **M4** (local soundness) -- follows M2's pattern
6. **M5 complete** (full table + native_decide)

---

## Key files to modify

| File | Change |
|------|--------|
| `SolutionTable/Basic.lean` | Add `checkGlobal`, `checkLocal` (Bool-returning); update `ValidGlobal`/`ValidLocal` to use them |
| `SolutionTable/Global.lean` | Prove `valid_global_imp_no_rupert` |
| `SolutionTable/Local.lean` | Prove `valid_local_imp_no_rupert` |
| `ComputationalStep.lean` | Data ingestion, table definition, `exists_solution_table` |
| `SolutionTable/NopertList.lean` | May need `nopertList`-indexed lookup lemmas |

## Key existing code to reuse

| What | Where |
|------|-------|
| `rational_global` | `RationalApprox/RationalGlobal.lean:130` |
| `rational_local` | `RationalApprox/RationalLocal.lean:56` |
| `Gℚ`, `Hℚ`, `maxHℚ`, `RationalGlobalTheoremPrecondition` | `RationalApprox/RationalGlobal.lean:16-49` |
| `Aεℚ`, `Bεℚ`, `BoundDeltaℚ`, `BoundRℚ` | `RationalApprox/RationalLocal.lean:17-51` |
| `κApproxPoly` | `RationalApprox/Basic.lean:63` |
| `sinℚ`, `cosℚ`, `rotMℚ`, `κ` | `RationalApprox/Basic.lean` |
| `nopertList`, `nopert_list_eq_nopert_verts` | `SolutionTable/NopertList.lean` |
| `DENOM`, `Interval.toPoseInterval` | `SolutionTable/Basic.lean:221-234` |
| `Pose.closed_ball` | `PoseInterval.lean:82-97` |
| `include_str` | Lean 4 built-in, for M5 data ingestion |

## Verification

- Each milestone can be tested independently by checking that the file compiles
- M5 partial: construct a 1-row table with a known global leaf, run `native_decide`
- M5 complete: `lake build` should succeed with no sorry's remaining
