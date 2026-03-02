# M1 Sub-Plan: Global Validity Checker

This is a plan for the remaining work to help Claude make progress.

## Goal

Define `checkGlobal : Row → Bool` — a computable, pure-ℚ function that
returns `true` iff a global row's data satisfies all preconditions of the
rational global theorem (`rational_global` in `RationalApprox/RationalGlobal.lean`).

Then wire `Row.ValidGlobal` to use it, replacing the current `sorry`.

---

## New file: `Noperthedron/Checker/Global.lean`

All checker code lives here. This file imports `SolutionTable.Basic` for
the `Row`/`Interval` types but does NOT import any `RationalApprox` or
`Global` modules. Everything is computable — no `noncomputable` keyword.

### Why a separate file?

The existing `sinℚ`, `cosℚ`, `rotMℚ_mat`, etc. in
`RationalApprox/Basic.lean` are all inside a `noncomputable section`.
A `Bool`-returning checker cannot call noncomputable definitions. We
reimplement the same math as computable functions over ℚ. This
duplication is intentional and acceptable — the checker is a
self-contained computational artifact, separate from the proof
infrastructure. This is sensible, because the function of `sinℚ` is to
define the Taylor-series approximation of sin for the purposes of
*reasoning* about it. It is okay if we define a separate function that
takes rationals as inputs and outputs rationals for the purposes of
*computing* with it, and prove that the two are equivalent under
coercion.

### Contents

#### A. Constants

```
DENOMQ : ℚ := 15360000
κQ     : ℚ := 1 / 10^10
```

#### B. Computable sinQ / cosQ

Reimplemented using the continued-fraction form from the Python
`helper_functions.py`, which is more efficient than `Finset.sum` and
manifestly computable:

```
sinQ(x) = x · (1 − x²/(2·3) · (1 − x²/(4·5) · (1 − ··· (1 − x²/(24·25)))))
cosQ(x) =     (1 − x²/(1·2) · (1 − x²/(3·4) · (1 − ··· (1 − x²/(23·24)))))
```

12 nesting levels each, giving degree-25 (sin) and degree-24 (cos) polynomials.
Mathematically identical to `sin_psum 13` and `cos_psum 13` in
`RationalApprox/Basic.lean`.

#### C. Computable rotation matrices over ℚ

Same formulas as `rotMℚ_mat`, `rotMθℚ_mat`, `rotMφℚ_mat`, `rotRℚ_mat`,
`rotR'ℚ_mat` from `RationalApprox/Basic.lean`, but using the computable
`sinQ`/`cosQ`:

| Function | Size | Description |
|----------|------|-------------|
| `rotMQ θ φ`  | 2×3 | Projection matrix M(θ,φ) |
| `rotMθQ θ φ` | 2×3 | ∂M/∂θ |
| `rotMφQ θ φ` | 2×3 | ∂M/∂φ |
| `rotRQ α`    | 2×2 | In-plane rotation R(α) |
| `rotR'Q α`   | 2×2 | dR/dα |

#### D. Rational vertex data

```
nopertListQ : Array (Fin 3 → ℚ)   -- 90 entries
```

These are rational approximations of the 90 noperthedron vertices. See
"Vertex approximation strategy" below for the full discussion of how
these are produced and why.

The indexing convention matches the Python NOP matrix and the Lean
`nopertList`:

```
index = k + 15·i + 45·ℓ
```

where k ∈ [0,15) is the rotation index, i ∈ {0,1,2} selects C1/C2/C3,
and ℓ ∈ {0,1} is the sign flip.

#### E. Helper functions

```
-- Center of an interval box along one parameter, as a rational
centerQ (iv : Interval) (p : Param) : ℚ :=
  (iv.min p + iv.max p) / (2 * DENOMQ)

-- Max half-width of an interval box across all 5 parameters
epsilonQ (iv : Interval) : ℚ :=
  max over p of (iv.max p - iv.min p) / (2 * DENOMQ)

-- 2D dot product
dot2 (u v : Fin 2 → ℚ) : ℚ := u 0 * v 0 + u 1 * v 1
```

#### F. Gℚ and Hℚ computation

Direct rational computation matching the formulas in
`RationalApprox/RationalGlobal.lean`, lines 16–25:

```
GQ(θ₁, φ₁, α, ε, S, w) =
    ⟨R(α) · M(θ₁,φ₁) · S, w⟩
  − ε · (|⟨R'(α) · M(θ₁,φ₁) · S, w⟩|
        + |⟨R(α) · Mθ(θ₁,φ₁) · S, w⟩|
        + |⟨R(α) · Mφ(θ₁,φ₁) · S, w⟩|)
  − 9ε²/2
  − 4κ(1 + 3ε)

HQ(θ₂, φ₂, ε, w, P) =
    ⟨M(θ₂,φ₂) · P, w⟩
  + ε · (|⟨Mθ(θ₂,φ₂) · P, w⟩| + |⟨Mφ(θ₂,φ₂) · P, w⟩|)
  + 2ε²
  + 3κ(1 + 2ε)

maxHQ(θ₂, φ₂, ε, w) = max over all 90 vertices P of HQ(θ₂, φ₂, ε, w, P)
```

All intermediate values are rational. The inner products are computed via
matrix-vector multiply followed by `dot2`.

#### G. The main checker

```
checkGlobal (row : Row) : Bool :=
  -- (1) Node type
  row.nodeType == 1
  -- (2) Unit vector
  && row.wx_numerator² + row.wy_numerator² == row.w_denominator²
  -- (3) S_index in bounds
  && row.S_index < 90
  -- (4) Center in [-4, 4]⁵
  && all 5 center coordinates in [-4, 4]
  -- (5) G > maxH inequality
  && GQ ... > maxHQ ...
```

---

## Wire into SolutionTable/Basic.lean

Replace the sorry-based definitions:

```
def Row.ValidGlobal (_tab : Table) (row : Row) : Prop :=
  checkGlobal row = true

instance (tab : Table) (row : Row) : Decidable (Row.ValidGlobal tab row) :=
  inferInstanceAs (Decidable (_ = true))
```

Note: `ValidGlobal` does not actually need the `tab` argument for global
rows. The `tab` parameter exists for uniformity with split/local rows.

---

## Vertex approximation strategy

The real nopert vertices are defined as:

```
nopertPt k ℓ i = (-1)^ℓ · Rz(2πk/15)(Cᵢ)
```

where `Rz` uses exact `cos(2πk/15)` and `sin(2πk/15)` — irrational
values. Any rational approximation must deal with this irrationality,
and for M2 we must *prove* the approximation is within κ = 10⁻¹⁰.

### The two approaches

**Approach A: Hard-code from Python.**
The Python does `⌊exact · 10¹⁶⌋ / 10¹⁶`, producing 270 rational numbers.
We'd paste these into Lean via a data generation script. This is
guaranteed to make the G > maxH inequality hold (since it matches the
Python's verified computation). But for M2, proving κApproxPoly still
requires bounding `|cos(2πk/15) - hardcoded_value|`, which requires
Taylor remainder bounds + a π approximation bound — the same proof
machinery as approach B.

**Approach B: Compute algorithmically.**
Define the rational vertices using our computable `sinQ`/`cosQ` applied
to rational angle approximations:

```
πQ : ℚ := (a rational approximation of π good to ~16+ digits)
angleQ(k) := 2 · πQ · k / 15

nopertPtQ k ℓ i :=
  let θ := angleQ k
  let c := CiQ i     -- the rational coordinates of Cᵢ (already in the codebase)
  (-1)^ℓ · (c₁·cosQ(θ) - c₂·sinQ(θ), c₁·sinQ(θ) + c₂·cosQ(θ), c₃)
```

No data generation script needed. The "vertex data" is just the 9
rational coordinates of C1, C2, C3 (already in `Nopert.lean`) plus πQ.

### Why both approaches need the same M2 proof work

In either case, proving `‖real_vertex - rational_vertex‖ ≤ κ` decomposes
into the same ingredients:

1. **π approximation bound:** `|π - πQ| ≤ 10⁻¹⁶` or similar. Mathlib has
   `Real.pi_lt_3141593` and `Real.pi_gt_3141592` which give ~7 digits.
   We may need tighter bounds, but these are standard.

2. **Taylor remainder bound:** `|sin(x) - sinQ(x)| ≤ |x|²⁷/27!` for
   `|x| ≤ 4`. At x = 4 this is ~1.7 · 10⁻¹². The existing BoundsKappa
   module proves related bounds (e.g. `‖rotM - rotMℚ‖ ≤ κ`), so the
   machinery exists or is close.

3. **Composition:** The per-coordinate error of a vertex is bounded by
   `|Cᵢⱼ| · (trig_error)`, and since `‖Cᵢ‖ ≤ 1`, the L2 norm error is
   at most `√3 · max_trig_error ≈ √3 · 10⁻¹² ≪ κ`.

For Approach A, the proof would go: "the hard-coded value equals
cosQ(rational_angle) which approximates cos(exact_angle)." For Approach B,
the proof is more direct: "cosQ(rational_angle) approximates
cos(exact_angle)" — skipping the middle step.

### Risk with Approach B

Since we'd use different rational vertices than the Python, the G and
maxH values would be slightly different. The G > maxH inequality
*should* still hold because:

- The Gℚ and Hℚ formulas include κ-correction terms (4κ(1+3ε) and
  3κ(1+2ε)) specifically designed to absorb vertex approximation error
  up to κ
- Both our approximation and the Python's are well within κ of the real
  vertices (error ~10⁻¹² vs κ = 10⁻¹⁰)

But "should" isn't "must" — there could be razor-thin margins on some
rows. We won't know for sure until we run the checker.

### Recommendation

Use **Approach B** (algorithmic computation). It's cleaner (no data
generation script, vertices defined from first principles, more natural
M2 proof structure). Validate early by running the checker on a few rows.
If any row fails, fall back to Approach A (hard-coded data from Python).

---

## Smoke test

Extract one global row from `data/solution_tree.csv` (e.g. row 91, the
first global row), hard-code it as a Lean `Row` literal, and verify:

```
def testGlobalRow : Row := {
  ID := 91, nodeType := 1, nrChildren := 0, IDfirstChild := 0, split := 0,
  interval := { min := fun | .θ₁ => 0 | .φ₁ => 0 | .θ₂ => 806400
                            | .φ₂ => 808960 | .α => -23459840,
                max := fun | .θ₁ => 806400 | .φ₁ => 806400 | .θ₂ => 1612800
                            | .φ₂ => 1617920 | .α => -22650880 },
  S_index := 39,
  wx_numerator := 5319166373, wy_numerator := 15662395164,
  w_denominator := 16540984045,
  P1_index := 0, P2_index := 0, P3_index := 0,
  Q1_index := 0, Q2_index := 0, Q3_index := 0,
  r := 0, sigma_Q := ⟨0, by omega⟩
}

#eval checkGlobal testGlobalRow   -- expected: true
```

This validates that our ℚ computation matches the Python verification for
at least one row, confirming the formulas and vertex data are correct.

---

## Execution order

1. Fix `Interval` and `Row` types in `SolutionTable/Basic.lean` (prerequisite)
2. Create `Checker/Global.lean` with `sinQ`/`cosQ` and rotation matrices
3. Implement `nopertListQ` algorithmically (Approach B: sinQ/cosQ at rational angles)
4. Implement `GQ`/`HQ`/`maxHQ`/`checkGlobal`
5. Smoke test with one row (`#eval`)
6. If smoke test fails, investigate: wrong formula? or thin margin → fall back to Approach A
7. Wire `ValidGlobal` to use `checkGlobal`

---

## Relationship to M2

M1 produces a `Bool`-returning checker. M2 must prove:

```
checkGlobal row = true → ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull
```

This requires three things, all M2 concerns:

1. **sinQ/cosQ agreement:** The computable `sinQ`/`cosQ` in
   `Checker/Global.lean` agree with the noncomputable `sinℚ`/`cosℚ` in
   `RationalApprox/Basic.lean` when evaluated at rational points (cast
   to ℝ). This should be a straightforward proof that the
   continued-fraction form equals the Finset.sum form, since they compute
   the same polynomial.

2. **κApproxPoly for vertices:** `nopertListQ` satisfies
   `κApproxPoly nopertVerts nopertListQ_as_reals`. This requires the
   Taylor remainder + π approximation bounds discussed in "Vertex
   approximation strategy" above. The existing BoundsKappa module proves
   similar bounds for rotation matrices and may provide reusable
   ingredients.

3. **Interval containment:** The axis-aligned box from
   `row.toPoseInterval` is contained in `pbar.closed_ball ε` where pbar
   is the center and ε is the max half-width. This is a simple geometric
   fact about sup-norm balls containing axis-aligned boxes.

---

## Performance notes

- Each `checkGlobal` call evaluates sinQ/cosQ (degree 25) at ~4 rational
  angles, computes ~10 matrix-vector products (2×3 or 2×2), and iterates
  over 90 vertices for maxHQ. This is ~1000 rational multiplications per row.

- For `#eval` (interpreted), one row should take well under a second.

- For `native_decide` on the full table (~17.5M global rows), performance
  will depend on the compiled code speed. This is an M5 concern.

- The continued-fraction form of sinQ/cosQ avoids computing large
  factorials and large powers separately, keeping intermediate rational
  numerator/denominator sizes more manageable.
