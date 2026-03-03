# M2 Sub-Plan: valid_global_imp_no_rupert

## Goal

Prove the sorry in `SolutionTable/Global.lean`:
```lean
theorem valid_global_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull
```

where `row.ValidGlobal tab` is definitionally `Checker.checkGlobal row = true`.

---

## Strategy overview

Apply `rational_global` (from `RationalApprox/RationalGlobal.lean`) with:
- `poly := Nopert.poly` (the real noperthedron, a `GoodPoly`)
- `poly_ := approxPoly` (the 90 rational vertices as an `ApproxGoodPoly`)
- `happrox : κApproxPoly poly.vertices poly_.vertices`
- `pbar` := center pose extracted from the row
- `ε` := max half-width of the row's interval box
- `pc : RationalGlobalTheoremPrecondition` built from the checker data

Then show `row.toPoseInterval ⊆ pbar.closed_ball ε` to conclude.

---

## Sub-goals

### A. Computation agreement: sinQ = sinℚ over ℚ

**What:** Prove the computable Horner-form `sinQ`/`cosQ` in `Checker/Global.lean`
agree with the `Finset.sum`-form `sinℚ`/`cosℚ` in `RationalApprox/Basic.lean`.

```lean
theorem sinQ_eq_sinℚ (x : ℚ) : sinQ x = sinℚ (k := ℚ) x
theorem cosQ_eq_cosℚ (x : ℚ) : cosQ x = cosℚ (k := ℚ) x
```

Combined with the existing `sinℚ_match`/`cosℚ_match` (which say
`sinℚ (k := ℚ) x = sinℚ (k := ℝ) ↑x`), this gives:
```
↑(sinQ q) = sinℚ (k := ℝ) (↑q : ℝ)
```

**Approach:** Both sides are degree-25 (resp. 24) polynomials in `x` over
ℚ. The Horner form is a rearrangement of the Finset.sum form. Options:

1. **Direct `ring`**: Unfold both sides to raw polynomial expressions and
   let `ring` close it. May need `simp [sin_psum, sinQ, Finset.sum]`
   to evaluate the `Finset.range 13` sum concretely, then `ring`.

2. **Inductive Horner lemma**: Prove a general lemma that the Horner
   evaluation of the Taylor coefficients equals the Finset.sum form.
   Probably overkill for a one-off proof.

3. **`native_decide`**: Treat both as functions `ℚ → ℚ` and test equality
   at enough points (doesn't prove functional equality, not viable).

Approach 1 is most likely to work. The `Finset.range 13` sum will need
to be unfolded to 13 explicit terms, then `ring` should close the goal.

**Difficulty:** Low–medium. Tedious but mechanical.

**File:** New file `Checker/Agreement.lean` (imports both `Checker/Global`
and `RationalApprox/Basic`).

### B. Matrix/dot-product agreement

**What:** Show the checker's `applyM`, `applyR`, `dot2`, etc. agree with
the noncomputable `rotMℚ_mat`, `rotRℚ_mat`, inner product when all
inputs are rational.

```lean
-- For each matrix function:
theorem applyM_eq_rotMℚ (θ φ : ℚ) (v : Fin 3 → ℚ) :
    (fun i => (applyM θ φ v i : ℝ)) = rotMℚ_mat (↑θ) (↑φ) |>.mulVec (↑v ·)
-- (similarly for applyMθ, applyMφ, applyR, applyR')

-- For dot product:
theorem dot2_eq_inner (u w : Fin 2 → ℚ) :
    (dot2 u w : ℝ) = ⟪(↑u : ℝ²), (↑w : ℝ²)⟫
```

These follow from sub-goal A (sinQ = sinℚ) plus unfolding.

**Difficulty:** Low. Follows directly from A.

**File:** `Checker/Agreement.lean`

### C. Gℚ/Hℚ/maxHℚ agreement

**What:** Show the checker's computable `computeGQ`/`computeHQ`/`computeMaxHQ`
agree (under ℚ→ℝ cast) with the noncomputable `Gℚ`/`Hℚ`/`maxHℚ` from
`RationalGlobal.lean`.

```lean
theorem computeGQ_eq_Gℚ (θ₁ φ₁ α ε : ℚ) (S : Fin 3 → ℚ) (w : Fin 2 → ℚ) :
    (computeGQ θ₁ φ₁ α ε S w : ℝ) = Gℚ pbar ε (↑S) (↑w)
    -- where pbar has coordinates (↑θ₁, ↑φ₁, ↑θ₂, ↑φ₂, ↑α)
```

For `maxHℚ`, we also need the max-over-Array to equal the max-over-Finset:
```lean
-- The checker's Array.foldl max agrees with Finset.image.max'
theorem computeMaxHQ_eq_maxHℚ (θ₂ φ₂ ε : ℚ) (w : Fin 2 → ℚ) :
    (computeMaxHQ θ₂ φ₂ ε w : ℝ) = maxHℚ pbar poly_ ε (↑w)
```

This requires showing `nopertListQ` (the checker's Array) and
`poly_.vertices` (the Finset) represent the same set of vertices.

**Difficulty:** Medium. The individual G/H part follows from B. The max
agreement needs careful handling of Array↔Finset correspondence.

**File:** `Checker/Agreement.lean`

### D. κApproxPoly construction

**What:** Construct `κApproxPoly nopertVerts approxVerts` where
`approxVerts` is the Finset of rational vertex approximations (from
`nopertListQ`) cast to ℝ³.

```lean
def approxPoly : ApproxGoodPoly := { ... }
theorem nopert_kapprox : κApproxPoly nopertVerts approxPoly.vertices
```

This requires:
1. A bijection `nopertVerts ≃ approxVerts`
2. For each pair, `‖real_vertex - approx_vertex‖ ≤ κ`

**Sub-structure of the bound proof:**

For each vertex `v` in `nopertVerts` (defined via exact trig: `cos(2πk/15)`,
`sin(2πk/15)`, and rational base coordinates C1/C2/C3), the corresponding
rational approximation `v_` in `nopertListQ` satisfies `‖v - v_‖ ≤ κ`.

The error decomposes as:
```
‖v - v_‖ ≤ √3 · max_coord_error
```
where the per-coordinate error is:
```
|cos(2πk/15)·Cij - hardcoded_coord/10^16|
  ≤ |cos(2πk/15) - cosℚ(2πk/15)|·|Cij|     -- Taylor remainder
    + |cosℚ(2πk/15)·Cij - hardcoded/10^16|  -- truncation
```

The Taylor remainder `|cos(x) - cosℚ(x)| ≤ |x|^26/26!` at
`x = 2π ≈ 6.28` gives ~10⁻²⁵, and `|Cij| ≤ 1`, so the first
term is negligible. The truncation error is ≤ 10⁻¹⁶ by construction.
Total: `√3 · 10⁻¹⁶ ≈ 1.7 · 10⁻¹⁶ ≪ κ = 10⁻¹⁰`.

**Approach options:**

1. **Abstract bound**: Prove a general lemma that any floor-truncated
   Taylor-polynomial evaluation of a trig function at a real argument
   is within some explicit bound of the true value. Then instantiate
   for each vertex. This is clean but requires:
   - Taylor remainder bounds (may exist in Mathlib or in existing
     `TrigLemmas.lean`)
   - π bounds (Mathlib has `Real.pi_lt_3141593`)

2. **Per-vertex interval arithmetic**: For each of the 90 vertices,
   set up a computable rational bound check. E.g., show that for the
   kth vertex's x-coordinate:
   ```
   |cosℚ(2·piQ·k/15)·Cij - hardcoded/10^16| ≤ bound
   ```
   where `piQ` is a rational approximation of π, and `bound` is
   chosen so that `√3 · (Taylor_remainder + bound) ≤ κ`.
   This can be partly automated via `native_decide` on rational
   comparisons.

**Difficulty:** HIGH. This is the hardest sub-goal. The error analysis
is straightforward mathematically but the formal Lean proof requires
careful engineering.

**Possible simplification:** Since the BoundsKappa module already proves
`‖rotM θ φ - rotMℚ θ φ‖ ≤ κ_matrix` type bounds, maybe we can
leverage those to get per-vertex bounds more directly?

Actually, looking more carefully: the existing `BoundsKappa` bounds
relate `rotM` (real trig) to `rotMℚ` (Taylor polynomial, same angles).
These DON'T directly give us vertex approximation bounds, because
`κApproxPoly` is about the vertex positions themselves, not about
rotation matrices.

However, `nopertList` already provides `nopertList.toFinset = nopertVerts`
(from `NopertList.lean`). So the bijection part is handled: the real
vertices are enumerated by `nopertList`, and the rational vertices by
`nopertListQ`. We need `‖nopertList[i] - ↑(nopertListQ[i])‖ ≤ κ` for
each i ∈ [0,90).

**File:** New file, perhaps `Checker/KappaApprox.lean` or
`RationalApprox/NopertApprox.lean`.

### E. ApproxGoodPoly construction

**What:** Build `approxPoly : ApproxGoodPoly` from `nopertListQ`.

```lean
noncomputable def approxPoly : ApproxGoodPoly where
  vertices := (nopertListQ.toList.map (fun v => (↑(v ·) : ℝ³))).toFinset
  nonempty := by ...  -- 90 vertices, trivially nonempty
  nontriv := by ...   -- follows from κApproxPoly + real verts have norm ≥ 0.98
```

`nontriv` proof sketch: for any `v_ ∈ approxPoly.vertices`, the
corresponding `v ∈ nopertVerts` satisfies `‖v‖ ≥ 0.98` (provable
from the vertex definitions). Then `‖v_‖ ≥ ‖v‖ - ‖v - v_‖ ≥ 0.98 - κ > 0`.

**Difficulty:** Low, given D.

**File:** Same as D.

### F. Geometric lemmas

**F1. Interval containment:**
```lean
theorem interval_sub_closed_ball (row : Row) :
    row.toPoseInterval ⊆ pbar.closed_ball ε
```
where `pbar` is the center pose and `ε` is the max half-width. This is
a straightforward calculation: each axis-aligned half-width ≤ ε (the max),
so the box fits inside the sup-norm ball of radius ε.

**F2. fourInterval membership:**
```lean
theorem center_in_fourInterval (row : Row)
    (h : checkGlobal row = true) :
    fourInterval.contains pbar
```
From the checker's `(-4 ≤ θ₁) && (θ₁ ≤ 4) && ...` conditions.

**F3. Unit vector:**
```lean
theorem w_unit (row : Row) (h : checkGlobal row = true) :
    ‖w‖ = 1
```
From `wx² + wy² = wd²` and `wd > 0`.

**F4. ε > 0:**
```lean
theorem epsilon_pos (row : Row) (h : checkGlobal row = true) :
    epsilonQ row.interval > 0
```

**Difficulty:** Low. All straightforward arithmetic.

**File:** `SolutionTable/Global.lean` or `Checker/Agreement.lean`.

### G. Main proof assembly

Wire everything together in `SolutionTable/Global.lean`:

```lean
theorem valid_global_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  -- 1. Extract: checkGlobal row = true
  -- 2. Unfold checkGlobal, extract all Bool conjuncts as hypotheses
  -- 3. Construct pbar, ε, S, w from row data
  -- 4. Build approxPoly and κApproxPoly (from D, E)
  -- 5. Build RationalGlobalTheoremPrecondition:
  --    - S_in_poly: from S_index
  --    - p_in_4: from F2
  --    - w_unit: from F3
  --    - exceeds: from C (computation agreement) + checker's GQ > maxHQ
  -- 6. Apply rational_global
  -- 7. Show row.toPoseInterval ⊆ pbar.closed_ball ε (from F1)
  -- 8. Conclude
  sorry
```

**Difficulty:** Medium. The main challenge is cleanly extracting
hypotheses from the `checkGlobal` Bool chain.

---

## Key existing infrastructure to reuse

| What | Where | How |
|------|-------|-----|
| `rational_global` | `RationalApprox/RationalGlobal.lean:127` | The target theorem to apply |
| `Nopert.poly : GoodPoly` | `Nopert.lean:254` | The real noperthedron |
| `nopert_point_symmetric` | `Nopert.lean:199` | PointSym witness |
| `nopert_list_eq_nopert_verts` | `NopertList.lean:145` | `nopertList.toFinset = nopertVerts` |
| `sinℚ_match`/`cosℚ_match` | `RationalApprox/Basic.lean:38,46` | `sinℚ (k:=ℚ) x = sinℚ (k:=ℝ) ↑x` |
| `BoundsKappa` lemmas | `RationalApprox/BoundsKappa.lean` | κ-bounds on rotation matrices |
| `Gℚ_le_G`, `H_le_Hℚ` | `RationalApprox/RationalGlobal.lean:54+` | Rational ≤ real bounds |

---

## Suggested execution order

1. **A: sinQ/cosQ agreement** — Foundational, blocks B and C
2. **B: Matrix agreement** — Follows from A, blocks C
3. **F: Geometric lemmas** — Independent of A/B, can be done in parallel
4. **C: Gℚ/Hℚ/maxHℚ agreement** — Needs A+B
5. **D: κApproxPoly** — Independent of A/B/C, can be done in parallel.
   This is the hardest piece and should be started early.
6. **E: ApproxGoodPoly** — Needs D
7. **G: Assembly** — Needs everything

Parallelism: D can (and should) be developed concurrently with A→B→C.

---

## Risk assessment

| Sub-goal | Difficulty | Risk |
|----------|-----------|------|
| A: sinQ = sinℚ | Low–Medium | `ring` might choke on degree 25; may need manual steps |
| B: Matrix agreement | Low | Routine |
| C: G/H/maxH agreement | Medium | Array↔Finset max correspondence needs care |
| **D: κApproxPoly** | **High** | Main risk. 90 vertices × 3 coords = 270 bounds. May need automation or a helper that does interval arithmetic for individual coordinate bounds |
| E: ApproxGoodPoly | Low | Follows from D |
| F: Geometric lemmas | Low | Straightforward |
| G: Assembly | Medium | Extracting Bool conjuncts from checkGlobal needs clean handling |

---

## Open questions

1. **How to handle the 90 vertex bounds in D?** Options:
   - 90 individual lemmas (very tedious)
   - A single abstract bound lemma + `decide`/`native_decide` on
     the 90 rational comparisons
   - A tactic/elaborator that automates the bound checking

2. **π bounds for D:** Mathlib's `Real.pi_lt_3141593` gives ~7 digits.
   The error analysis needs π to ~16 digits accuracy (to bound the
   truncation). Do we have or can we get tighter π bounds?
   Alternatively, can we avoid needing tight π bounds by working with
   the abstract Taylor remainder directly?

3. **The Array↔Finset correspondence for maxHℚ in C:** The checker
   computes `max` via `Array.foldl`, while the theorem uses
   `Finset.image.max'`. We need to connect these. This might require
   proving `nopertListQ.toList.toFinset` equals `approxPoly.vertices`
   (after casting), and that the foldl-max equals the Finset max.
