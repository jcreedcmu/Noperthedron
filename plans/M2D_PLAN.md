# M2D Sub-Plan: κApproxPoly Construction

## Goal

Construct `κApproxPoly nopertVerts approxVerts` (sub-goal D of M2),
where `approxVerts` is the Finset of rational vertices from
`nopertListQ` cast to ℝ³.

Concretely, this requires:
1. A bijection `nopertVerts ≃ approxVerts`
2. For each pair, `‖real_vertex - approx_vertex‖ ≤ κ`

---

## Strategy: Triangle Inequality via Intermediate List

Define `nopertListℚ` — an intermediate list that replaces exact trig
in `nopertList` with Taylor-polynomial trig (`sinℚ`/`cosℚ`) at
rational angle arguments. Both `nopertListQ` and `nopertListℚ` are
rational, so their distance is decidable. And `nopertListℚ` is
provably close to `nopertList` by Taylor remainder bounds.

```
nopertListQ  <──calculate──>  nopertListℚ  <──prove──>  nopertList
(hard-coded ℚ)     (ℚ arithmetic)      (sinℚ/cosℚ at ℚ args)         (exact trig)
```

By the triangle inequality:
```
‖nopertListQ[j] - nopertList[j]‖
    ≤ ‖nopertListQ[j] - nopertListℚ[j]‖ + ‖nopertListℚ[j] - nopertList[j]‖
```

**Left leg** (nopertListQ vs nopertListℚ): Both sides are ℚ-valued.
The per-coordinate distance is a rational number, so the bound check
is decidable. For 90 vertices × 3 coordinates = 270 comparisons,
`norm_num` should be able to handle this.

**Right leg** (nopertListℚ vs nopertList): Proven via Taylor remainder
bounds + π approximation error. A single uniform bound covers all 90
vertices.

---

## Scoped-Down Goal: First Vertex, First Coordinate

To validate the approach, we start with the simplest possible case:
showing that the first coordinate of `nopertListQ[0]` is within
`κ/√3` of the first coordinate of `nopertList[0]`.

### Why this case is special (k = 0)

The first vertex has `k = 0, ℓ = 0, i = 0`:
```
nopertList[0] = nopertPt 0 0 0
              = (-1)^0 • RzL(2π·0/15)(C1R)
              = RzL(0)(C1R)
              = C1R
```
Since `Rz(0)` is the identity, the vertex IS the base point C1R.
And C1R has rational coordinates: `C1R = (152024884/259375205, 0,
210152163/259375205)`.

Similarly, `nopertListℚ[0]` would use `cosQ(0) = 1`, `sinQ(0) = 0`,
yielding the same C1R. So the right leg of the triangle inequality is
**zero** for this vertex.

The entire bound reduces to:
```
|nopertListQ[0][0] - C1R[0]| ≤ κ/√3
```
which is:
```
|5861195714524832/10^16 - 152024884/259375205| ≤ 1/(10^10 · √3)
```

This is a comparison of a rational number against an irrational bound.

### Proof sketch for the first coordinate

**Step 1: Compute the rational difference.**
Both `nopertListQ[0][0] = 5861195714524832/10^16` and
`C1[0] = 152024884/259375205` are rational. Their difference `d` is a
specific rational number with value approximately `r/10^16` where
`0 ≤ r < 1`. (The Python computed
`floor(152024884/259375205 · 10^16) = 5861195714524832`, so the
truncation error is `< 1/10^16`.)

**Step 2: Bound the difference.**
Show `|d| ≤ 1/10^16`. Since the hard-coded value comes from floor
truncation, `0 ≤ d < 1/10^16`. This can be verified by computing
`152024884 · 10^16` and `5861195714524832 · 259375205` and comparing
(exact integer arithmetic).

**Step 3: Show `1/10^16 ≤ κ/√3`.**
We need `1/10^16 ≤ 1/(10^10 · √3)`, i.e., `10^10 · √3 ≤ 10^16`.
Since `√3 < 2`, we have `10^10 · √3 < 2 · 10^10 < 10^16`. Done.

In Lean, step 3 can be handled by showing `1/10^16 ≤ κ/2` (since
`κ/2 ≤ κ/√3` because `√3 ≤ 2`), and `1/10^16 ≤ 1/(2 · 10^10)` is
a pure rational comparison.

### Lean proof structure (first coordinate)

```lean
-- In a new file, e.g. Checker/KappaApprox.lean

-- Step 1: nopertList[0] = C1R
-- (existing: nopert_list_test_0 says nopertList[0] = nopertPt 0 0 0)
-- Need: nopertPt 0 0 0 = C1R (from definition: Rz(0) is identity)

-- Step 2: Extract first coordinate
-- C1R 0 = (152024884 : ℚ) / 259375205  (from Nopert.lean line 15)
-- nopertListQ[0] 0 = (5861195714524832 : ℤ) / 10^16  (from Checker/Global.lean)

-- Step 3: Rational bound
-- |5861195714524832/10^16 - 152024884/259375205| < 1/10^16
-- This is decidable: norm_num

-- Step 4: 1/10^16 ≤ κ/√3
-- Use: κ/√3 ≥ κ/2 = 1/(2·10^10) > 1/10^16
```

### From first coordinate to first vertex

Once all three coordinates are bounded by `κ/√3`, the vertex norm
bound follows from:
```
‖v‖ = √(v₀² + v₁² + v₂²) ≤ √(3 · (κ/√3)²) = κ
```

For the first vertex, coordinate 1 has zero error (both are 0), and
coordinates 0 and 2 each have error `< 1/10^16 ≪ κ/√3`. So:
```
‖diff‖² = d₀² + 0² + d₂² ≤ 2/10^32 ≤ κ² = 1/10^20
```

Alternatively, skip `κ/√3` entirely and prove `‖diff‖² ≤ κ²`
directly, since `d₀² + d₂²` is rational and `κ² = 1/10^20` is
rational. This avoids dealing with `√3` in Lean.

---

## Definitions for the General Case

### `piQ : ℚ` — Rational approximation of π

We can use the 20-digit approximation of π implied by
mathlib's `Real.pi_gt_d20` and `Real.pi_lt_d20`

### `nopertPtℚ` — Rational vertex approximation via Taylor polynomials

```lean
def nopertPtℚ (k ℓ : ℕ) (i : Fin 3) : Fin 3 → ℚ :=
  let θ := 2 * piQ * k / 15
  let c := cosQ θ
  let s := sinQ θ
  let ci := C_rat i  -- rational base coordinates (C1, C2, C3)
  let sgn : ℚ := (-1)^ℓ
  fun
  | 0 => sgn * (c * ci 0 - s * ci 1)
  | 1 => sgn * (s * ci 0 + c * ci 1)
  | 2 => sgn * ci 2
```

where `C_rat : Fin 3 → (Fin 3 → ℚ)` gives the rational base
coordinates (C1, C2, C3 from `Nopert.lean` lines 15–17).

### `nopertListℚ` — The full intermediate list

```lean
def nopertListℚ : Array (Fin 3 → ℚ) :=
  -- Same iteration order as nopertList: ℓ ∈ [0,2), i ∈ [0,3), k ∈ [0,15)
  Array.ofFn fun (j : Fin 90) =>
    let ℓ := j / 45
    let i := (j % 45) / 15
    let k := j % 15
    nopertPtℚ k ℓ i
```

---

## Bounding the Right Leg (nopertListℚ vs nopertList)

For each vertex with parameters (k, ℓ, i), the per-coordinate error
decomposes as follows. Consider the x-coordinate (coordinate 0):

```
|nopertPtℚ k ℓ i 0 - nopertPt k ℓ i 0|
= |cosQ(θ')·Ci_x - sinQ(θ')·Ci_y - cos(θ)·Ci_x + sin(θ)·Ci_y|
= |[cosQ(θ') - cos(θ)]·Ci_x - [sinQ(θ') - sin(θ)]·Ci_y|
≤ |cosQ(θ') - cos(θ)|·|Ci_x| + |sinQ(θ') - sin(θ)|·|Ci_y|
```

where `θ = 2πk/15` (real) and `θ' = 2·piQ·k/15` (rational).

Each trig error decomposes via the triangle inequality:
```
|cosQ(θ') - cos(θ)|
  ≤ |cosQ(θ') - cos(θ')| + |cos(θ') - cos(θ)|
  ≤ |θ'|^26/26!           + |θ' - θ|
```

where:
- First term: Taylor remainder (existing `cosℚ_approx`), noting
  `cosQ = cosℚ(k:=ℚ)` under cast (sub-goal A of M2).
- Second term: `|cos(θ') - cos(θ)| ≤ |θ' - θ| = 2k/15 · |piQ - π|`
  by the mean value theorem (since `|cos'| = |sin| ≤ 1`).

### Uniform bound

For all vertices, `|θ| ≤ 2π·14/15 < 2π < 7` and
`|θ'| ≤ 2·piQ·14/15 < 7`. So:

```
Taylor remainder ≤ 7^26/26! ≈ 10^{-25}  (negligible)
```

And:
```
MVT term ≤ 2·14/15 · |piQ - π| ≈ 1.87 · |piQ - π|
```

With `|piQ - π| ≤ 10^{-19}`, the MVT term is `≤ 2 · 10^{-19}`.

Since `|Ci_x|, |Ci_y| ≤ 1` (the base coordinates have norm ≤ 1), the
per-coordinate error is:
```
≤ 2 · (10^{-25} + 2 · 10^{-19}) ≈ 4 · 10^{-19}
```

And the per-vertex norm error:
```
‖diff‖ ≤ √3 · 4 · 10^{-19} ≈ 7 · 10^{-19} ≪ κ = 10^{-10}
```

This gives generous room. The right-leg bound is proven **once** as a
uniform lemma:

```lean
theorem nopertListℚ_approx_nopertList (j : Fin 90) :
    ‖(↑(nopertListℚ[j]) : ℝ³) - nopertList[j]‖ ≤ κ / 2
```

(Using κ/2 as the budget for the right leg, leaving κ/2 for the left.)

### Key ingredients for the right-leg proof

1. **Taylor remainder** (existing):
   `sinℚ_approx`, `cosℚ_approx` from `TrigLemmas.lean`
2. **sinQ = sinℚ agreement** (sub-goal A of M2):
   `sinQ_eq_sinℚ` — needed to connect computable `sinQ` to the
   noncomputable `sinℚ` that has Taylor remainder bounds.
   For the sake of this goal we can declare `sinQ_eq_sinℚ` and leave its
   proof as a sorry.
3. **π approximation bound**: easy from mathlib lemmas.
4. **MVT for cos/sin** (Mathlib):
   `|cos(x) - cos(y)| ≤ |x - y|` — follows from `|cos'| ≤ 1`
5. **Base coordinate bounds** (existing):
   `c1_norm_one`, `c2_norm_bound`, `c3_norm_bound` from `Nopert.lean`

---

## Bounding the Left Leg (nopertListQ vs nopertListℚ)

Both `nopertListQ[j]` and `nopertListℚ[j]` are `Fin 3 → ℚ`. Their
per-coordinate difference is a rational number. We need to show:

```lean
∀ j : Fin 90, ∀ c : Fin 3,
  |nopertListQ[j] c - nopertListℚ[j] c| ≤ κ_left / √3
```

or equivalently (to avoid √3):

```lean
∀ j : Fin 90,
  (nopertListQ[j] 0 - nopertListℚ[j] 0)^2
  + (nopertListQ[j] 1 - nopertListℚ[j] 1)^2
  + (nopertListQ[j] 2 - nopertListℚ[j] 2)^2
  ≤ (κ / 2)^2
```

This is a decidable proposition over ℚ. It can be verified by `norm_num`.

**Performance:** Each evaluation of `nopertListℚ[j]` requires
computing `sinQ` and `cosQ` at one rational argument (degree-25
polynomial evaluation over ℚ), plus a few multiplications. For 90
vertices this is ~90 polynomial evaluations. This shouldn't be too hard.
We can lean on `norm_num` and should not use `native_decide`.

---

## Assembly: κApproxPoly from the Two Legs

```lean
-- Combining both legs:
theorem nopert_kappa_approx_coord (j : Fin 90) :
    ‖(↑(nopertListQ[j]) : ℝ³) - nopertList[j]‖ ≤ κ := by
  calc ‖(↑(nopertListQ[j]) : ℝ³) - nopertList[j]‖
      ≤ ‖(↑(nopertListQ[j]) : ℝ³) - (↑(nopertListℚ[j]) : ℝ³)‖
        + ‖(↑(nopertListℚ[j]) : ℝ³) - nopertList[j]‖ := norm_sub_le_of_triangle ...
    _ ≤ κ/2 + κ/2 := add_le_add left_leg_bound right_leg_bound
    _ = κ := ...
```

Then construct the `κApproxPoly`:
```lean
noncomputable def nopert_kapprox : κApproxPoly nopertVerts approxVerts where
  bijection := ...  -- from nopert_list_eq_nopert_verts + indexing
  approx := fun ⟨v, hv⟩ => nopert_kappa_approx_coord (index_of v hv)
```

The bijection part uses `nopert_list_eq_nopert_verts` (existing,
NopertList.lean line 145) which says `nopertList.toFinset =
nopertVerts`. We need the analogous statement for the rational side:
`nopertListQ.toList.toFinset_image_cast = approxVerts`.

---

## Execution Plan

### Phase 0: First vertex, first coordinate (validate approach)

1. Prove `nopertPt 0 0 0 = C1R` (Rz(0) is identity).
2. Show `nopertList[0] = C1R` (combines with existing
   `nopert_list_test_0`).
3. Compute `|nopertListQ[0][0] - C1[0]|` as a rational number.
4. Show it's `≤ κ/√3` (or directly show the squared-norm bound).

**File:** `Checker/KappaApprox.lean`
**Difficulty:** Low. Pure rational arithmetic + one simple trig identity.

### Phase 1: First vertex, all coordinates

5. Extend to coordinates 1 and 2.
6. Prove `‖(↑(nopertListQ[0]) : ℝ³) - nopertList[0]‖ ≤ κ`.

**Difficulty:** Low. Same approach, three coordinates.

### Phase 2: All vertices with k = 0

7. Extend to all 6 vertices with k = 0 (three base points × two signs).
   These all have trivial rotation, so nopertListℚ = nopertList.

**Difficulty:** Low. Same approach, 6 × 3 = 18 rational comparisons.

### Phase 3: General case (k > 0)

8. Define `piQ` and prove π bounds.
9. Define `nopertPtℚ` and `nopertListℚ`.
10. Prove the right-leg uniform bound (Taylor + MVT).
11. Verify the left-leg bound.
12. Assemble `κApproxPoly`.

**Difficulty:** Medium–High. The π bounds (step 8) and right-leg
proof (step 10) are the main challenges.

---

## Open Questions

1. **π bounds:** Mathlib provides ~7 digits of π. We need ~12. How to
   get tighter bounds? Machin's formula
   (`π/4 = 4·arctan(1/5) - arctan(1/239)`) with explicit arctan
   Taylor remainder is one option. Another is to find or port existing
   Lean/Mathlib π bound proofs.

2. **MVT in Lean:** We need `|cos(x) - cos(y)| ≤ |x - y|`. This
   follows from `|cos'| = |sin| ≤ 1`. Mathlib likely has the
   ingredients (Lipschitz lemmas for trig functions) but we need to
   check.

3. **Bijection construction:** The bijection between
   `nopertList.toFinset` and `nopertListQ.toList.toFinset` (both cast
   to ℝ³) is index-based. We need to verify the indexing conventions
   match. The existing `nopert_list_test_*` lemmas confirm specific
   indices.

4. **Performance of left-leg decide:** 90 evaluations of degree-25
   rational polynomials.

---

## Risk Assessment

| Component | Difficulty | Risk |
|-----------|-----------|------|
| Phase 0 (first coord) | Low | Minimal — pure ℚ arithmetic |
| Phase 1 (first vertex) | Low | Minimal |
| Phase 2 (k=0 vertices) | Low | Minimal |
| π bounds | Medium–High | Main risk for general case |
| Right-leg uniform bound | Medium | Taylor machinery exists; MVT needs checking |
| Left-leg | Low | Performance risk only |
| Bijection construction | Medium | Indexing bookkeeping |
