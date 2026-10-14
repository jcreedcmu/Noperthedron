# A rational-coordinate (Cayley) proof that the Noperthedron is not Rupert

This is the design of the proof of `¬ IsRupert exactVerts`. Every pose coordinate is
rational and every leaf check is exact polynomial arithmetic. This file describes the
parametrization and the reduction, with every step.

## Notation

* `P` is the hull of the 90 vertices `exactVerts = {±Rz(2πk/15) C_i}`.
* `G = {g_k = Rz(2πk/15) : k = 0..14}` (proper symmetries); also `P = −P`.
* `proj(x) = (x₀, x₁)`. A pose is a pair `(R_o, R_i)` of rotations. The *view* of `R` is
  `n(R) = Rᵀ e_z` (its third row).
* `Cay(r)` is the Cayley rotation with numerator `N(r)` (`cayleyNumeratorMatrix` in
  NopertTriakisTetrahedron) and denominator `D(r) = 1 + |r|²`. It rotates about `r` by
  `2·atan|r|`. `tr Cay(r) = (3 − |r|²)/(1 + |r|²)`.
* `s(u, v) = Cay(v, −u, 0)`. Its view is the inverse stereographic image
  `n = (2u, 2v, 1 − u² − v²)/(1 + u² + v²)`. Polar angle `φ` and azimuth `θ` satisfy
  `u + iv = tan(φ/2)·e^{iθ}`.
* `H_n = 2nnᵀ − I` (half-turn about `n`). `H_n = sᵀ Rz(π) s` for `s = s(u,v)`.
* `τ = −Refl_{θ₃}`, where `θ₃` is the azimuth of `C3` and `Refl_{θ₃}` is the reflection in
  the vertical plane through `C3`. Its entries are rational: `cos 2θ₃ = (x²−y²)/(x²+y²)` and
  `sin 2θ₃ = 2xy/(x²+y²)` with `(x, y) = (C3₀, C3₁)`. `τ` is a half-turn about a horizontal
  axis. It maps the 30 copies of `C3` onto themselves, but it does **not** map `P` to itself.
* Chart bases `B₀ = I`, `B₁ = diag(1,−1,−1)`, `B₂ = diag(−1,1,−1)`, `B₃ = diag(−1,−1,1)`
  (the Klein four-group of NopertTriakisTetrahedron's atlas), and `B₄ = τ`.

## Moves that preserve the Rupert property

Write `Sh(R) = proj(R P)`.

1. **Offset.** Because `P = −P` and `P` is convex, a Rupert passage with an offset gives one
   with offset 0. This is the existing `rupert_implies_rot_rupert`. From now on, a Rupert pose
   means `closure Sh(R_i) ⊆ interior Sh(R_o)`.
2. **Common left factor.** Take `L ∈ SO(3)` with `L e_z = ±e_z`, i.e. `Rz(δ)` or `Rx(π)Rz(δ)`.
   Then `proj ∘ L = ℓ ∘ proj` for a linear isometry `ℓ` of the plane. So `(L R_o, L R_i)` is
   Rupert iff `(R_o, R_i)` is. Since `Rx(π)` maps the view `n` to `−n`, this move can flip
   the outer view.
3. **Symmetries.** `(R_o g, R_i)` and `(R_o, R_i g)` for `g ∈ G`, since `gP = P`.
4. **Inner half-turn.** `(R_o, Rz(π) R_i)`, since `Sh(Rz(π)R) = −Sh(R) = Sh(R)` because
   `P = −P`.

## Reduction

Take a Rupert pose (offset 0).

**Step A: outer view.** Let `n = n(R_o)`. Use move 2 with `Rx(π)` to get `n_z ≥ 0`. Use move 3
on the outer rotation to put the azimuth in `[0, 2π/15]`. Then `n = n(s(u,v))` for unique
`(u, v)` with

    u ≥ 0,  0 ≤ v ≤ m·u,  u² + v² ≤ 1      (m ≥ tan(2π/15) rational; using a larger m is sound)

(at the pole, `u = v = 0`). Now `L := R_o s(u,v)ᵀ` fixes `e_z`, so `L = Rz(δ)`. Move 2 with
`Lᵀ` makes `R_o = s(u,v)`.

**Step B: relative rotation.** Let `Q = R_oᵀ R_i`. Moves 3 (inner) and 4 act on `Q` by
`Q ↦ Q g` and `Q ↦ H_n Q`, and leave `n` fixed. The orbit is `O(Q) = {H_n^ε Q g}`, with 30
elements. Pick `Q* ∈ O(Q)` maximizing

    F(X) = max(tr X, tr(τᵀX) − δ)        (δ = 1/8)

The point of `F`: every exactly aligned configuration has a representative at `Q* = I` or
`Q* = τ`. The bias `δ` breaks ties in favour of `I` where the two aligned sheets cross. That
happens at isolated horizontal views, where `H_n g = τ`.

**Step C: chart.** Pick `j ∈ argmax_k tr(B_kᵀ Q*)`. If `j ≤ 3`, NopertTriakisTetrahedron's
`cayley_mem_unit_cube_of_maximal_chart` gives `Q* = B_j Cay(r)` with `r ∈ [−1,1]³`. If
`j = 4`, then `tr(τᵀQ*) ≥ max_k≤3 tr(B_kᵀQ*) ≥ 0`, because the four Klein traces sum to 0
(`exists_chart_trace_nonneg`). So `exists_cayleyMatrix_of_trace_nonneg` gives
`τᵀQ* = Cay(r)` with `|r|² ≤ 3`, hence `|r|∞ ≤ 2`.

**Result.** Some reduced pose `(u, v, j, r)` is Rupert, with `R_o = s(u,v)` and
`R_i = s(u,v) B_j Cay(r)`. It satisfies the wedge and disk inequalities, chart maximality
`tr(B_kᵀQ) ≤ tr(B_jᵀQ)`, and orbit maximality `F(X) ≤ F(Q)` for all `X ∈ O(Q)`. Boundedness:
`(u, v) ∈ [0,1] × [0,1/2]`, `r ∈ [−1,1]³` (charts 0–3) or `[−2,2]³` (chart 4).

Charts 0 and 4 are *blown up*: `r = ρc` with `c` on a face of `∂[−1,1]³` (6 faces) and
`ρ = |r|∞ ∈ [0, 1]` (chart 0) or `[0, 2]` (chart 4). Every root box has dyadic endpoints.

## Polynomial form

All checks multiply through by the positive denominators `D_o = 1 + u² + v²` and `D_r`.
For an inner vertex `S`, an outer vertex `T` and a direction `w ∈ ℚ²`:

    gap(S,T,w)·D_o·D_r = α(u,v) · (B_j N(r) S − D_r(r) T),
    α = w₀·N_o[0,:] + w₁·N_o[1,:]

This is a bilinear form: degree ≤ 2 in each of `u, v`, times degree ≤ 2 in each of the three
`r` (or `c, ρ`) variables. In the normalized box coordinates `t ∈ [-1,1]⁵` it is bounded below
either by its coefficients (constant term minus the absolute values of the terms with an odd
exponent and the negative terms with all-even exponents) or by its least Bernstein coefficient.

## Certificates

Every certificate proves `∃ inner point q, ∀ outer vertex T, ⟨w,q⟩ ≥ ⟨w,T⟩`. Then `q` is not
in the interior of the outer shadow, so the pose is not Rupert. Only `≥` is needed, so exact
touching (aligned) poses need no separate argument.

* **Domain:** one reduction inequality is strictly violated on the whole box.
* **Global:** `(S, w)`: the lower bound of `gap(S,T,w)·D_oD_r` is `≥ 0` for all 90 `T`.
* **Blown-up (charts 0, 4):** `(S, w)` with paired vertex `σ(S) = B_j S` (`σ = id` for
  chart 0; for chart 4, `S` must be one of the 30 `C3` copies). Then exactly
  `gap(S, σS) D_oD_r = 2ρ · α · B_j (c×S + ρ c×(c×S))`. The checker bounds the bracket
  `L ≥ 0`, together with the plain gaps for `T ≠ σS`. This is the blow-up/zoom step. Nothing
  else is needed because the aligned set is exactly `ρ = 0`.

## Irrational data

The `cos/sin(2πk/15)` in the vertices and in `G` enter through rational approximations with
an explicit error. The vertex error is absorbed by subtracting
`2ε‖w‖₁ D_o D_r` (orthogonality bounds `|proj R e| ≤ |e|`). The `g_k` error is absorbed by a
`9ε·denominator` margin in the domain tests. The divided identity for `L` is exact for the
true vertices (`τ` permutes the `C3` copies exactly), and `L` is linear in `S`, so the same
error bound applies.

## Why chart 4 and the bias

* The z-axis view of the Noperthedron is an exact regular 30-gon: only the `C3` copies lie
  on the hull. Near the pole, the hull consists of `C3` copies only. Their orbit has the extra
  half-turn symmetry `τ`, so the poses `(n, τ)` with `n` near the pole are exactly aligned
  (zero margin) without being symmetric poses of `P`. Hence chart 4. [SY25] handles these
  with its local theorem.
* Where the `τ` sheet meets the `I` sheet (two horizontal views per wedge, `H_n g = τ`), the
  plain max-trace reduction ties. The bias `δ` fixes this.

## The certificate

The floating-point search (`cayley/search`) tries 12 inner vertices × 13 directions per box,
chooses each split by look-ahead (the direction whose halves can both be certified), and uses
the Bernstein bound. The result has 245,484 leaves (194,785 gap, 50,699 domain), 3.5 MB of
preorder tokens `S<d>`, `D<code>`, `G<s>:<w0>:<w1>`.
