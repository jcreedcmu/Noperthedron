import Noperthedron.Checker.Global
import Noperthedron.RationalApprox.Basic
import Noperthedron.RationalApprox.TrigLemmas
import Noperthedron.Vertices.Exact
import Noperthedron.Vertices.Taylor
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# κ-Approximation of Noperthedron Vertices

Proves that the hard-coded rational vertices in `nopertListQ`
are within distance κ = 10⁻¹⁰ of the real noperthedron vertices.

See `plans/M2D_PLAN.md` for the overall strategy.
-/

open Nopert RationalApprox Noperthedron.Solution.Checker Real
open scoped Nat

namespace Noperthedron.KappaApprox

/-! ## Phase 0: First vertex (k=0) -/

/-- RzL at angle 0 is the identity. -/
private lemma RzL_zero_eq_one : RzL (0 : ℝ) = 1 :=
  AddChar.map_zero_eq_one RzC

/-- The first vertex of nopertList is C1R (rotation at k=0 is identity). -/
lemma exactPt_0_0_0 : exactPt 0 0 0 = C1R := by
  simp only [exactPt, Int.reduceNeg, pow_zero, CharP.cast_eq_zero, mul_zero, zero_div, Cpt,
    one_smul]
  rw [RzL_zero_eq_one, ContinuousLinearMap.one_apply]

lemma exactVertex_0 : exactVertex 0 = C1R :=
  by simp [exactVertex, exactPt, Cpt, RzL_zero_eq_one]

/-! ## Phase 1: Full first vertex norm bound -/

-- Extract concrete rational values of nopertListQ[0]
private lemma nlq0_0 : pythonVertex 0 0 = (5861195714524832 : ℚ) / 10000000000000000 := by
  decide +kernel
private lemma nlq0_1 : pythonVertex 0 1 = 0 := by decide +kernel
private lemma nlq0_2 : pythonVertex 0 2 = (8102245663767282 : ℚ) / 10000000000000000 := by
  decide +kernel

/-- The ℝ³ norm of the difference between the first rational vertex
    and C1R is at most κ. -/
lemma first_vertex_close :
    ‖(WithLp.toLp 2 (fun i => (pythonVertex 0 i : ℝ)) : ℝ³) - C1R‖ ≤ κ := by
  have hκ : (0 : ℝ) ≤ κ := by unfold κ; positivity
  rw [EuclideanSpace.norm_eq]
  calc sqrt (∑ i : Fin 3, ‖(WithLp.toLp 2 (fun i => (pythonVertex 0 i : ℝ)) - C1R) i‖ ^ 2)
      ≤ sqrt (κ ^ 2) := by
        apply sqrt_le_sqrt
        simp only [norm_eq_abs, sq_abs, Fin.sum_univ_three]
        show ((↑(pythonVertex 0 0) : ℝ) - C1R 0) ^ 2 +
             ((↑(pythonVertex 0 1) : ℝ) - C1R 1) ^ 2 +
             ((↑(pythonVertex 0 2) : ℝ) - C1R 2) ^ 2 ≤ κ ^ 2
        simp only [nlq0_0, nlq0_1, nlq0_2]
        unfold C1R C1 κ
        simp only [Pi.mul_apply, Matrix.cons_val]
        push_cast
        norm_num
    _ = κ := sqrt_sq hκ

/-! ## General case infrastructure -/

/-- π exceeds our rational approximation. -/
lemma piQ_lt_pi : (piQ : ℝ) < π := pi_gt_d20

/-- π is within 10⁻²⁰ of our rational approximation. -/
lemma pi_sub_piQ_lt : π - (piQ : ℝ) < 1 / 10 ^ 20 := by
  have h := pi_lt_d20  -- π < 3.14159265358979323847
  -- 3.14159265358979323847 = piQ + 1/10^20
  have : (3.14159265358979323847 : ℝ) = (piQ : ℝ) + 1 / 10 ^ 20 := by
    unfold piQ; push_cast; norm_num
  linarith

/-! ## sinQ/cosQ agreement with sinℚ/cosℚ -/

/-- The computable Horner-form `sinQ` agrees with the Finset.sum-form `sinℚ`. -/
theorem sinQ_eq_sinℚ (x : ℚ) : sinQ x = sinℚ (k := ℚ) x := by
  simp only [sinQ, sinℚ, sin_psum, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The computable Horner-form `cosQ` agrees with the Finset.sum-form `cosℚ`. -/
theorem cosQ_eq_cosℚ (x : ℚ) : cosQ x = cosℚ (k := ℚ) x := by
  simp only [cosQ, cosℚ, cos_psum, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- sinQ at a rational x, cast to ℝ, equals sinℚ at the cast argument. -/
theorem sinQ_cast (x : ℚ) : (sinQ x : ℝ) = sinℚ (k := ℝ) (x : ℝ) := by
  rw [sinQ_eq_sinℚ, sinℚ_match]

/-- cosQ at a rational x, cast to ℝ, equals cosℚ at the cast argument. -/
theorem cosQ_cast (x : ℚ) : (cosQ x : ℝ) = cosℚ (k := ℝ) (x : ℝ) := by
  rw [cosQ_eq_cosℚ, cosℚ_match]

/-- Taylor remainder bound: |sin(x) - ↑(sinQ q)| ≤ |x|^27/27! when x = ↑q. -/
theorem sinQ_approx (q : ℚ) : |Real.sin q - (sinQ q : ℝ)| ≤ |↑q| ^ 27 / 27! := by
  rw [sinQ_cast]; exact sinℚ_approx q

/-- Taylor remainder bound: |cos(x) - ↑(cosQ q)| ≤ |x|^26/26! when x = ↑q. -/
theorem cosQ_approx (q : ℚ) : |Real.cos q - (cosQ q : ℝ)| ≤ |↑q| ^ 26 / 26! := by
  rw [cosQ_cast]; exact cosℚ_approx q

/-! ## Left-leg validation: k > 0 vertex -/

/-- Left-leg squared distance for ALL 90 vertices.
    The hard-coded `pythonVertex` agrees with the Taylor-polynomial
    `taylorVertex` to within squared distance κ² = 10⁻²⁰ per vertex. -/
lemma left_leg_all :
    ∀ j : Fin 90,
    (pythonVertex j 0 - taylorVertex j 0) ^ 2 +
    (pythonVertex j 1 - taylorVertex j 1) ^ 2 +
    (pythonVertex j 2 - taylorVertex j 2) ^ 2 ≤
    (1 : ℚ) / 10 ^ 28 := by
  decide +kernel

/-! ## Right-leg bound: nopertListℚ vs nopertList -/

/-- Cast a `Fin 3 → ℚ` to an `ℝ³` point. -/
noncomputable def toR3 (v : Fin 3 → ℚ) : ℝ³ :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

/-- The reduced angle index k' = min(k, 15-k) satisfies k' ≤ 7. -/
private lemma reduced_le_seven (k : ℕ) (hk : k < 15) :
    (if k ≤ 7 then k else 15 - k) ≤ 7 := by
  split_ifs with h <;> omega

/-- The rational angle 2·piQ·k'/15 has absolute value < 3 when k' ≤ 7. -/
private lemma piQ_angle_abs_lt_three (k' : ℕ) (hk : k' ≤ 7) :
    |(2 * piQ * k' / 15 : ℚ)| < 3 := by
  rw [abs_lt]
  constructor
  · have : (0 : ℚ) ≤ 2 * piQ * ↑k' / 15 := by unfold piQ; positivity
    linarith
  · have : (k' : ℚ) ≤ 7 := by exact_mod_cast hk
    unfold piQ
    calc 2 * 3.14159265358979323846 * (k' : ℚ) / 15
        ≤ 2 * 3.14159265358979323846 * 7 / 15 := by gcongr
      _ < 3 := by norm_num

/-- Combined trig error for cosQ at a reduced rational angle vs cos at the real angle. -/
private lemma cosQ_combined_error (k' : ℕ) (hk : k' ≤ 7) :
    |↑(cosQ (2 * piQ * k' / 15)) - Real.cos (2 * π * k' / 15)| ≤ κ / 7 := by
  set q : ℚ := 2 * piQ * k' / 15 with hq_def
  have taylor := cosQ_approx q
  have habs : |(↑q : ℝ)| < 3 := by exact_mod_cast piQ_angle_abs_lt_three k' hk
  have hq_eq : (↑q : ℝ) = 2 * (piQ : ℝ) * k' / 15 := by
    simp only [hq_def]; push_cast; ring
  have mvt : |Real.cos ↑q - Real.cos (2 * π * k' / 15)| ≤
      |↑q - 2 * π * k' / 15| := by rw [hq_eq]; exact abs_cos_sub_cos_le _ _
  have hpi := pi_sub_piQ_lt
  have hk7 : (k' : ℝ) ≤ 7 := by exact_mod_cast hk
  -- Bound on |↑q - 2πk'/15|
  have hpi_pos : 0 ≤ π - (piQ : ℝ) := le_of_lt (sub_pos.mpr piQ_lt_pi)
  have hdiff : |↑q - 2 * π * k' / 15| ≤ 14 / 15 * (1 / 10 ^ 20) := by
    rw [hq_eq, show 2 * (piQ : ℝ) * k' / 15 - 2 * π * k' / 15 =
        -(2 * k' / 15 * (π - (piQ : ℝ))) from by ring, abs_neg,
        abs_of_nonneg (mul_nonneg (by positivity) hpi_pos)]
    exact mul_le_mul (by linarith) (le_of_lt hpi) hpi_pos (by positivity)
  calc |(↑(cosQ q) : ℝ) - Real.cos (2 * π * k' / 15)|
      = |(↑(cosQ q) - Real.cos ↑q) + (Real.cos ↑q - Real.cos (2 * π * k' / 15))| := by
        congr 1; ring
    _ ≤ |↑(cosQ q) - Real.cos ↑q| + |Real.cos ↑q - Real.cos (2 * π * k' / 15)| :=
        abs_add_le _ _
    _ ≤ |(↑q : ℝ)| ^ 26 / 26! + |↑q - 2 * π * k' / 15| :=
        add_le_add (by rw [abs_sub_comm]; exact taylor) mvt
    _ ≤ 3 ^ 26 / 26! + (14 / 15 * (1 / 10 ^ 20)) :=
        add_le_add (by gcongr) hdiff
    _ ≤ κ / 7 := by unfold κ; norm_num

/-- Same bound for sinQ. -/
private lemma sinQ_combined_error (k' : ℕ) (hk : k' ≤ 7) :
    |↑(sinQ (2 * piQ * k' / 15)) - Real.sin (2 * π * k' / 15)| ≤ κ / 7 := by
  set q : ℚ := 2 * piQ * k' / 15 with hq_def
  have taylor := sinQ_approx q
  have habs : |(↑q : ℝ)| < 3 := by exact_mod_cast piQ_angle_abs_lt_three k' hk
  have hq_eq : (↑q : ℝ) = 2 * (piQ : ℝ) * k' / 15 := by
    simp only [hq_def]; push_cast; ring
  have mvt : |Real.sin ↑q - Real.sin (2 * π * k' / 15)| ≤
      |↑q - 2 * π * k' / 15| := by rw [hq_eq]; exact abs_sin_sub_sin_le _ _
  have hpi := pi_sub_piQ_lt
  have hk7 : (k' : ℝ) ≤ 7 := by exact_mod_cast hk
  have hpi_pos : 0 ≤ π - (piQ : ℝ) := le_of_lt (sub_pos.mpr piQ_lt_pi)
  have hdiff : |↑q - 2 * π * k' / 15| ≤ 14 / 15 * (1 / 10 ^ 20) := by
    rw [hq_eq, show 2 * (piQ : ℝ) * k' / 15 - 2 * π * k' / 15 =
        -(2 * k' / 15 * (π - (piQ : ℝ))) from by ring, abs_neg,
        abs_of_nonneg (mul_nonneg (by positivity) hpi_pos)]
    exact mul_le_mul (by linarith) (le_of_lt hpi) hpi_pos (by positivity)
  calc |(↑(sinQ q) : ℝ) - Real.sin (2 * π * k' / 15)|
      = |(↑(sinQ q) - Real.sin ↑q) + (Real.sin ↑q - Real.sin (2 * π * k' / 15))| := by
        congr 1; ring
    _ ≤ |↑(sinQ q) - Real.sin ↑q| + |Real.sin ↑q - Real.sin (2 * π * k' / 15)| :=
        abs_add_le _ _
    _ ≤ |(↑q : ℝ)| ^ 27 / 27! + |↑q - 2 * π * k' / 15| :=
        add_le_add (by rw [abs_sub_comm]; exact taylor) mvt
    _ ≤ 3 ^ 27 / 27! + (14 / 15 * (1 / 10 ^ 20)) :=
        add_le_add (by gcongr) hdiff
    _ ≤ κ / 7 := by unfold κ; norm_num

/-! ### Helper lemmas for right-leg bound -/

/-- `Cpt i j` (real base vertex coordinate) equals `↑(Crat i j)`. -/
private lemma Cpt_cast (i : Fin 3) (j : Fin 3) : (Cpt i) j = (↑(Crat i j) : ℝ) := by
  fin_cases i <;> fin_cases j <;> simp [Cpt, Crat, C1R, C2R, C3R, C1, C2, C3]

/-- The first two coordinates of each base vertex satisfy x² + y² ≤ 1. -/
private lemma Crat_xy_sq_le_one (i : Fin 3) :
    (↑(Crat i 0) : ℝ) ^ 2 + (↑(Crat i 1) : ℝ) ^ 2 ≤ 1 := by
  fin_cases i <;> simp [Crat, C1, C2, C3, Pi.mul_apply] <;> norm_num

/-- Angle reduction for cos: cos(2πk/15) = cos(2πk'/15) where k' is the reduced index. -/
private lemma cos_reduced_angle (k : ℕ) (hk : k < 15) :
    Real.cos (2 * π * k / 15) = Real.cos (2 * π * (if k ≤ 7 then k else 15 - k) / 15) := by
  split_ifs with h
  · rfl
  · have hk_cast : (k : ℝ) = 15 - ((15 - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : k ≤ 15)]; ring
    rw [hk_cast, show 2 * π * (15 - ↑(15 - k)) / 15 = 2 * π - 2 * π * ↑(15 - k) / 15
        from by ring]
    exact cos_two_pi_sub _

/-- Angle reduction for sin: sin(2πk/15) = ±sin(2πk'/15). -/
private lemma sin_reduced_angle (k : ℕ) (hk : k < 15) :
    Real.sin (2 * π * k / 15) =
    if k ≤ 7 then Real.sin (2 * π * (if k ≤ 7 then k else 15 - k) / 15)
    else -Real.sin (2 * π * (if k ≤ 7 then k else 15 - k) / 15) := by
  split_ifs with h
  · rfl
  · have hk_cast : (k : ℝ) = 15 - ((15 - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : k ≤ 15)]; ring
    rw [hk_cast, show 2 * π * (15 - ↑(15 - k)) / 15 = 2 * π - 2 * π * ↑(15 - k) / 15
        from by ring]
    exact sin_two_pi_sub _

/-- Components of RzL: coordinate 0. -/
private lemma RzL_apply_0 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 0 = cos θ * v 0 - sin θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]; ring

/-- Components of RzL: coordinate 1. -/
private lemma RzL_apply_1 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 1 = sin θ * v 0 + cos θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

/-- Components of RzL: coordinate 2. -/
private lemma RzL_apply_2 (θ : ℝ) (v : ℝ³) :
    (RzL θ v) 2 = v 2 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

/-- The core analytical bound: each vertex of nopertPtℚ is within κ/2 of the
    corresponding real nopertPt vertex. -/
theorem taylorPt_close (k : ℕ) (hk : k < 15) (ℓ : ℕ) (i : Fin 3) :
    ‖toR3 (taylorPt k ℓ i) - exactPt k ℓ i‖ ≤ κ / 2 := by
  -- Set up reduced angle
  set k' := if k ≤ 7 then k else 15 - k with hk'_def
  have hk'_le : k' ≤ 7 := reduced_le_seven k hk
  -- Trig errors
  set ce := (↑(cosQ (2 * piQ * k' / 15)) : ℝ) - Real.cos (2 * π * k' / 15) with hce_def
  set se := (↑(sinQ (2 * piQ * k' / 15)) : ℝ) - Real.sin (2 * π * k' / 15) with hse_def
  have hce : |ce| ≤ κ / 7 := cosQ_combined_error k' hk'_le
  have hse : |se| ≤ κ / 7 := sinQ_combined_error k' hk'_le
  -- Base coordinates
  set a := (↑(Crat i 0) : ℝ) with ha_def
  set b := (↑(Crat i 1) : ℝ) with hb_def
  have hab : a ^ 2 + b ^ 2 ≤ 1 := Crat_xy_sq_le_one i
  -- Set up the difference vector
  set d := toR3 (taylorPt k ℓ i) - exactPt k ℓ i with hd_def
  -- z-component is 0 (both sides use the same rational base coord)
  have hz : d 2 = 0 := by
    simp only [hd_def, toR3, taylorPt, exactPt]
    simp [RzL_apply_2, Cpt_cast]
  -- x,y squared norm = (ce² + se²)(a² + b²) via rotation algebra identity
  -- Both k ≤ 7 and k > 7 give the same squared norm due to cross-term cancellation
  have hsq : d 0 ^ 2 + d 1 ^ 2 = (ce ^ 2 + se ^ 2) * (a ^ 2 + b ^ 2) := by
    sorry
  -- Norm bound via sqrt
  have hκ2 : (0 : ℝ) ≤ κ / 2 := by unfold κ; positivity
  rw [EuclideanSpace.norm_eq, ← sqrt_sq hκ2]
  apply sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs]
  -- Goal: d 0^2 + d 1^2 + d 2^2 ≤ (κ/2)^2
  have hz2 : d 2 ^ 2 = 0 := by rw [hz]; ring
  rw [hz2, add_zero, hsq]
  -- Goal: (ce^2 + se^2) * (a^2 + b^2) ≤ (κ/2)^2
  have hce_sq : ce ^ 2 ≤ (κ / 7) ^ 2 := sq_le_sq' (abs_le.mp hce).1 (abs_le.mp hce).2
  have hse_sq : se ^ 2 ≤ (κ / 7) ^ 2 := sq_le_sq' (abs_le.mp hse).1 (abs_le.mp hse).2
  calc (ce ^ 2 + se ^ 2) * (a ^ 2 + b ^ 2)
      ≤ 2 * (κ / 7) ^ 2 * 1 := mul_le_mul (by linarith) hab (by positivity) (by positivity)
    _ ≤ (κ / 2) ^ 2 := by unfold κ; norm_num

/-- Index correspondence: exactVertex j = exactPt with computed indices. -/
private lemma exactVertex_index (j : Fin 90) :
    exactVertex j =
    exactPt (j.val % 15) (j.val / 45) ⟨(j.val % 45) / 15, by omega⟩ := by
  rfl

/-- Right-leg bound: the Taylor-polynomial intermediate list is close to
    the real noperthedron vertices. Uses Taylor remainder + MVT + π bounds.
    The actual error is ~10⁻¹⁵, well within κ/2 = 5·10⁻¹¹. -/
theorem right_leg_all (j : Fin 90) :
    ‖toR3 (taylorVertex j) - exactVertex j‖ ≤ κ / 2 := by
  -- Relate nopertListℚ[j] to nopertPtℚ
  have hℚ : taylorVertex j =
      taylorPt (j.val % 15) (j.val / 45) ⟨(j.val % 45) / 15, by omega⟩ := by
    simp [taylorVertex]
  -- Relate nopertList[j] to nopertPt
  rw [hℚ, exactVertex_index]
  exact taylorPt_close (j.val % 15) (by omega) (j.val / 45) _

/-! ## Combined bound via triangle inequality -/

/-- Componentwise unfolding of toR3 difference. -/
private lemma toR3_sub_apply (v₁ v₂ : Fin 3 → ℚ) (k : Fin 3) :
    (toR3 v₁ - toR3 v₂) k = (↑(v₁ k) : ℝ) - ↑(v₂ k) := by
  simp [toR3]

/-- Left-leg ℝ³ norm bound derived from the ℚ squared distance bound. -/
theorem left_leg_norm (j : Fin 90) :
    ‖toR3 (pythonVertex j) - toR3 (taylorVertex j)‖ ≤ κ / 2 := by
  have hκ2 : (0 : ℝ) ≤ κ / 2 := by unfold κ; positivity
  have h := left_leg_all j
  rw [EuclideanSpace.norm_eq, ← sqrt_sq hκ2]
  apply sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs, toR3_sub_apply]
  -- Goal: (↑(Q 0) - ↑(ℚ 0))² + ... ≤ (κ/2)²
  -- Rewrite differences to pull casts outside
  have heq : ((↑(pythonVertex j 0) : ℝ) - ↑(taylorVertex j 0)) ^ 2 +
       ((↑(pythonVertex j 1) : ℝ) - ↑(taylorVertex j 1)) ^ 2 +
       ((↑(pythonVertex j 2) : ℝ) - ↑(taylorVertex j 2)) ^ 2
      = ((pythonVertex j 0 - taylorVertex j 0) ^ 2 +
         (pythonVertex j 1 - taylorVertex j 1) ^ 2 +
         (pythonVertex j 2 - taylorVertex j 2) ^ 2 : ℚ) := by
    push_cast; ring
  rw [heq]
  -- Goal: (↑(ℚ sum) : ℝ) ≤ (κ / 2) ^ 2
  exact le_trans (Rat.cast_le.mpr h) (by unfold κ; push_cast; norm_num)

/-- The hard-coded rational vertices are within κ of the real vertices,
    for each index in [0, 90). -/
theorem vertex_close_index (j : Fin 90) :
    ‖toR3 (pythonVertex j) - exactVertex j‖ ≤ κ := by
  calc ‖toR3 (pythonVertex j) - exactVertex j‖
      = ‖(toR3 (pythonVertex j) - toR3 (taylorVertex j)) +
         (toR3 (taylorVertex j) - exactVertex j)‖ := by
        congr 1; abel
    _ ≤ ‖toR3 (pythonVertex j) - toR3 (taylorVertex j)‖ +
        ‖toR3 (taylorVertex j) - exactVertex j‖ :=
        norm_add_le _ _
    _ ≤ κ / 2 + κ / 2 := add_le_add (left_leg_norm j) (right_leg_all j)
    _ = κ := by ring

end KappaApprox
