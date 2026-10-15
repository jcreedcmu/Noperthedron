module

public import Cayley.Soundness.Pose
public import Cayley.Soundness.Trig
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# The reduction to a reduced Cayley pose

Every Rupert pair of rotations yields a Rupert pair `(s(u,v), s(u,v) · B_j · Cay(r))`
with `Reduced u v j r`. See `cayley/DESIGN.md`, steps A–C.
-/

namespace Cayley

open Noperthedron Real
open scoped Matrix

/-! ## Step A: the outer view -/

theorem RxPi_mem_SO3 : RxPi ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [mem_SO3_iff']
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [RxPi, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [RxPi, Matrix.det_fin_three]

theorem gR_mem_SO3 (k : ℕ) : gR k ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Bounding.rot3_mat_mem_SO3 2 _

theorem step_flip {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ}
    (hRo : Ro ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hRi : Ri ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h : RupPair Ro Ri) :
    ∃ Ro' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∃ Ri' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      RupPair Ro' Ri' ∧ 0 ≤ Ro' 2 2 := by
  by_cases hz : 0 ≤ Ro 2 2
  · exact ⟨Ro, hRo, Ri, hRi, h, hz⟩
  · refine ⟨RxPi * Ro, Submonoid.mul_mem _ RxPi_mem_SO3 hRo, RxPi * Ri,
      Submonoid.mul_mem _ RxPi_mem_SO3 hRi, rupPair_RxPi h, ?_⟩
    simp [RxPi, Matrix.mul_apply, Fin.sum_univ_three]
    linarith

theorem gR_eq (k : ℕ) : gR k = Rz_mat (k * θ₁) := by
  unfold gR θ₁; congr 1; ring

theorem mul_gR_row2 (R : Matrix (Fin 3) (Fin 3) ℝ) (k : ℕ) :
    (R * gR k) 2 0 = R 2 0 * cos (k * θ₁) + R 2 1 * sin (k * θ₁) ∧
    (R * gR k) 2 1 = - R 2 0 * sin (k * θ₁) + R 2 1 * cos (k * θ₁) ∧
    (R * gR k) 2 2 = R 2 2 := by
  rw [gR_eq]
  simp [Rz_mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem step_azimuth (a b : ℝ) :
    ∃ k : ℕ, 0 ≤ a * cos (k * θ₁) + b * sin (k * θ₁) ∧
      0 ≤ -a * sin (k * θ₁) + b * cos (k * θ₁) ∧
      -a * sin (k * θ₁) + b * cos (k * θ₁) ≤ 57 / 128 * (a * cos (k * θ₁) + b * sin (k * θ₁)) := by
  set z : ℂ := ⟨a, b⟩
  set ρ := ‖z‖
  set θ := Complex.arg z
  have ha : a = ρ * cos θ := by
    exact (Complex.norm_mul_cos_arg z).symm
  have hb : b = ρ * sin θ := by
    exact (Complex.norm_mul_sin_arg z).symm
  have hρ : 0 ≤ ρ := norm_nonneg _
  have hθ1 : 0 < θ₁ := by unfold θ₁; positivity
  -- an angle in [0, 2π) congruent to θ
  obtain ⟨θ0, hθ0, hθ0', hc, hs⟩ : ∃ θ0 : ℝ, 0 ≤ θ0 ∧ θ0 < 2 * π ∧
      cos θ0 = cos θ ∧ sin θ0 = sin θ := by
    by_cases hneg : θ < 0
    · refine ⟨θ + 2 * π, by linarith [Complex.neg_pi_lt_arg z], by linarith, ?_, ?_⟩
      · exact cos_add_two_pi θ
      · exact sin_add_two_pi θ
    · exact ⟨θ, by linarith, by linarith [Complex.arg_le_pi z, pi_pos], rfl, rfl⟩
  set k := ⌊θ0 / θ₁⌋₊
  have hk1 : (k : ℝ) * θ₁ ≤ θ0 := by
    have := Nat.floor_le (div_nonneg hθ0 hθ1.le)
    rwa [le_div_iff₀ hθ1] at this
  have hk2 : θ0 < (k + 1) * θ₁ := by
    have := Nat.lt_floor_add_one (θ0 / θ₁)
    rwa [div_lt_iff₀ hθ1] at this
  set φ := θ0 - k * θ₁
  have hφ0 : 0 ≤ φ := by simp only [φ]; linarith
  have hφ1 : φ ≤ θ₁ := by simp only [φ]; linarith
  have hθ1π : θ₁ < π / 2 := by unfold θ₁; linarith [pi_pos]
  have hcosφ : 0 ≤ cos φ := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsinφ : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith)
  have hA : a * cos (k * θ₁) + b * sin (k * θ₁) = ρ * cos φ := by
    rw [ha, hb, ← hc, ← hs, show φ = θ0 - k * θ₁ from rfl, cos_sub]; ring
  have hB : -a * sin (k * θ₁) + b * cos (k * θ₁) = ρ * sin φ := by
    rw [ha, hb, ← hc, ← hs, show φ = θ0 - k * θ₁ from rfl, sin_sub]; ring
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [hA]; positivity
  · rw [hB]; positivity
  · rw [hA, hB]
    -- sin φ cos θ₁ ≤ cos φ sin θ₁ since sin(φ - θ₁) ≤ 0
    have hsub : sin (φ - θ₁) ≤ 0 :=
      sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    rw [sin_sub] at hsub
    have hw := sin_θ₁_le_wedge
    have hcp := cos_θ₁_pos
    have : sin φ * cos θ₁ ≤ 57 / 128 * cos φ * cos θ₁ := by nlinarith
    have : sin φ ≤ 57 / 128 * cos φ := le_of_mul_le_mul_right (by linarith) hcp
    nlinarith

theorem outerRot_row2 (u v : ℝ) :
    outerRot u v 2 0 = 2 * u / (1 + u ^ 2 + v ^ 2) ∧
    outerRot u v 2 1 = 2 * v / (1 + u ^ 2 + v ^ 2) ∧
    outerRot u v 2 2 = (1 - u ^ 2 - v ^ 2) / (1 + u ^ 2 + v ^ 2) := by
  simp only [outerRot, cayleyMatrix, cayleyDenom]
  simp
  refine ⟨?_, ?_, ?_⟩ <;> ring_nf

/-- An SO(3) matrix whose third row is the stereographic image of `(u, v)` is
`Rz(γ) · s(u, v)`. -/
theorem eq_Rz_mul_outerRot (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (u v : ℝ)
    (h0 : R 2 0 = outerRot u v 2 0) (h1 : R 2 1 = outerRot u v 2 1)
    (h2 : R 2 2 = outerRot u v 2 2) :
    ∃ γ, R = Rz_mat γ * outerRot u v := by
  set S := outerRot u v
  have hS := outerRot_mem_SO3 u v
  set M := R * Sᵀ
  have hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    refine Submonoid.mul_mem _ hR ?_
    rw [mem_SO3_iff']
    exact ⟨by rw [Matrix.transpose_transpose, SO3_transpose_mul hS],
      by rw [Matrix.det_transpose]; exact ((mem_SO3_iff' S).1 hS).2⟩
  have hRR := SO3_mul_transpose hR
  have hMz : M.toEuclideanLin !₂[0, 0, 1] = !₂[0, 0, 1] := by
    have hrow : ∀ i, M i 2 = R i 0 * R 2 0 + R i 1 * R 2 1 + R i 2 * R 2 2 := by
      intro i
      simp only [M, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, h0, h1, h2]
    have hRR' : ∀ i, R i 0 * R 2 0 + R i 1 * R 2 1 + R i 2 * R 2 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 := by
      intro i
      rw [← hRR]
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
    ext i
    fin_cases i <;> simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      hrow, hRR']
  obtain ⟨γ, hγ⟩ := Bounding.SO3_fixing_z_is_Rz M hM hMz
  refine ⟨γ, ?_⟩
  rw [← hγ]
  simp only [M, Matrix.mul_assoc, S, SO3_transpose_mul hS, Matrix.mul_one]

/-- Step A: a Rupert pair with outer rotation `s(u, v)` in the wedge. -/
theorem step_outer {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ}
    (hRo : Ro ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hRi : Ri ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h : RupPair Ro Ri) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ v ≤ 57 / 128 * u ∧ u ^ 2 + v ^ 2 ≤ 1 ∧
      ∃ Ri' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, RupPair (outerRot u v) Ri' := by
  obtain ⟨Ro1, hRo1, Ri1, hRi1, h1, hz⟩ := step_flip hRo hRi h
  obtain ⟨k, hk0, hk1, hk2⟩ := step_azimuth (Ro1 2 0) (Ro1 2 1)
  set Ro2 := Ro1 * gR k
  have hRo2 : Ro2 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ hRo1 (gR_mem_SO3 k)
  have h2 : RupPair Ro2 Ri1 := rupPair_outer_gR k h1
  obtain ⟨e0, e1, e2⟩ := mul_gR_row2 Ro1 k
  set a := Ro2 2 0
  set b := Ro2 2 1
  set c := Ro2 2 2
  have ha : 0 ≤ a := by simp only [a, Ro2]; rw [e0]; exact hk0
  have hb : 0 ≤ b := by simp only [b, Ro2]; rw [e1]; exact hk1
  have hab : b ≤ 57 / 128 * a := by simp only [a, b, Ro2]; rw [e0, e1]; exact hk2
  have hc : 0 ≤ c := by simp only [c, Ro2]; rw [e2]; exact hz
  have hunit : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
    have := congrFun (congrFun (SO3_mul_transpose hRo2) 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] at this
    simp only [a, b, c]; nlinarith
  set u := a / (1 + c)
  set v := b / (1 + c)
  have hc1 : 0 < 1 + c := by linarith
  have hD : 1 + u ^ 2 + v ^ 2 = 2 / (1 + c) := by
    simp only [u, v]; field_simp; nlinarith
  obtain ⟨r0, r1, r2⟩ := outerRot_row2 u v
  obtain ⟨γ, hγ⟩ := eq_Rz_mul_outerRot Ro2 hRo2 u v
    (by rw [r0, hD]; simp only [u]; field_simp; rfl)
    (by rw [r1, hD]; simp only [v]; field_simp; rfl)
    (by rw [r2, hD]; simp only [u, v]; field_simp; nlinarith)
  refine ⟨u, v, by positivity, by positivity, ?_, ?_, Rz_mat (-γ) * Ri1,
    Submonoid.mul_mem _ (Bounding.rot3_mat_mem_SO3 2 _) hRi1, ?_⟩
  · simp only [u, v]; rw [div_le_iff₀ hc1]; field_simp; linarith
  · simp only [u, v]; rw [div_pow, div_pow, ← add_div, div_le_one (by positivity)]; nlinarith
  · have h3 := rupPair_Rz (-γ) h2
    have hinv : Rz_mat (-γ) * Rz_mat γ = 1 := by
      simpa using (Bounding.Rz_mat_mul_neg (-γ))
    rwa [hγ, ← Matrix.mul_assoc, hinv, Matrix.one_mul] at h3

/-! ## Step B: the relative rotation's orbit -/

theorem gR_mul (k k' : ℕ) : gR k * gR k' = gR (k + k') := by
  simp only [gR_eq, Bounding.Rz_mat_mul_Rz_mat]; congr 1; push_cast; ring

theorem gR_mod (k : ℕ) : gR (k % 15) = gR k := by
  rw [gR_eq, gR_eq]
  have h := Nat.mod_add_div k 15
  have : ((k % 15 : ℕ) : ℝ) * θ₁ = (k : ℝ) * θ₁ + ((-((k / 15 : ℕ) : ℤ) : ℤ) : ℝ) * (2 * π) := by
    have h' : ((k % 15 : ℕ) : ℝ) + 15 * ((k / 15 : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast h
    have hk : ((k % 15 : ℕ) : ℝ) = k - 15 * ((k / 15 : ℕ) : ℝ) := by linarith
    unfold θ₁; simp only [Int.cast_neg, Int.cast_natCast]; rw [hk]; ring
  rw [this, Rz_mat_add_int_mul_two_pi]

theorem ZR_mul_self : ZR * ZR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ZR, Matrix.mul_apply, Fin.sum_univ_three]

theorem Hmat_mul_self (u v : ℝ) : Hmat u v * Hmat u v = 1 := by
  have hS := SO3_mul_transpose (outerRot_mem_SO3 u v)
  have hS' := SO3_transpose_mul (outerRot_mem_SO3 u v)
  simp only [Hmat]
  calc (outerRot u v)ᵀ * ZR * outerRot u v * ((outerRot u v)ᵀ * ZR * outerRot u v)
      = (outerRot u v)ᵀ * ZR * (outerRot u v * (outerRot u v)ᵀ) * ZR * outerRot u v := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hS, Matrix.mul_one, Matrix.mul_assoc (outerRot u v)ᵀ, ZR_mul_self,
          Matrix.mul_one, hS']

/-- `H^e`. -/
noncomputable def hp (u v : ℝ) (e : Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  if e then Hmat u v else 1

theorem hp_mul (u v : ℝ) (e e' : Bool) : hp u v e' * hp u v e = hp u v (xor e e') := by
  cases e <;> cases e' <;> simp [hp, Hmat_mul_self]

theorem step_orbit {u v : ℝ} {Ri : Matrix (Fin 3) (Fin 3) ℝ}
    (hRi : Ri ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h : RupPair (outerRot u v) Ri) :
    ∃ Ri' ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, RupPair (outerRot u v) Ri' ∧
      ∀ (e : Bool) (k : ℕ), Fsc (hp u v e * ((outerRot u v)ᵀ * Ri') * gR k) ≤
        Fsc ((outerRot u v)ᵀ * Ri') := by
  set s := outerRot u v
  set Q := sᵀ * Ri
  obtain ⟨⟨e0, k0⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun ek : Bool × Fin 15 => Fsc (hp u v ek.1 * Q * gR ek.2)) Finset.univ_nonempty
  set Ri' := (if e0 then ZR else 1) * Ri * gR k0
  have hS := SO3_mul_transpose (outerRot_mem_SO3 u v)
  have hQ' : sᵀ * Ri' = hp u v e0 * Q * gR k0 := by
    cases e0
    · simp [Ri', hp, Q, Matrix.mul_assoc]
    · simp only [Ri', hp, Q, Hmat, ite_true]
      calc sᵀ * (ZR * Ri * gR k0) = sᵀ * ZR * (s * sᵀ) * Ri * gR k0 := by
            rw [hS]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]; rfl
  refine ⟨Ri', ?_, ?_, ?_⟩
  · refine Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ hRi) (gR_mem_SO3 _)
    cases e0
    · exact Submonoid.one_mem _
    · show ZR ∈ _
      rw [mem_SO3_iff']
      exact ⟨by ext a b; fin_cases a <;> fin_cases b <;>
          simp [ZR, Matrix.mul_apply, Fin.sum_univ_three],
        by simp [ZR, Matrix.det_fin_three]⟩
  · have h1 : RupPair s ((if e0 then ZR else 1) * Ri) := by
      cases e0
      · simpa using h
      · simpa [ZR_eq] using rupPair_inner_RzPi h
    exact rupPair_inner_gR _ h1
  · intro e k
    rw [hQ']
    have := hmax ⟨xor e0 e, ⟨(k0.val + k) % 15, Nat.mod_lt _ (by norm_num)⟩⟩ (Finset.mem_univ _)
    simp only at this
    calc Fsc (hp u v e * (hp u v e0 * Q * gR k0) * gR k)
        = Fsc (hp u v (xor e0 e) * Q * gR ((k0.val + k) % 15)) := by
          rw [gR_mod, ← gR_mul, ← hp_mul]; simp only [Matrix.mul_assoc]
      _ ≤ _ := this

/-! ## Step C: the chart -/

theorem chartB_transpose_mul_self (j : ℕ) : (chartB j)ᵀ * chartB j = 1 :=
  SO3_transpose_mul (chartB_mem_SO3 j)

theorem klein_trace_sum (X : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace ((chartB 0)ᵀ * X) + Matrix.trace ((chartB 1)ᵀ * X) +
      Matrix.trace ((chartB 2)ᵀ * X) + Matrix.trace ((chartB 3)ᵀ * X) = 0 := by
  simp [chartB, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem klein_mul (j m : ℕ) (hj : j < 4) (hm : m < 4) (X : Matrix (Fin 3) (Fin 3) ℝ) :
    (chartB (j ^^^ m))ᵀ * (chartB j * X) = chartB m * X := by
  rw [← Matrix.mul_assoc]
  congr 1
  interval_cases j <;> interval_cases m <;>
    (ext a b; fin_cases a <;> fin_cases b <;> simp [chartB, Matrix.mul_apply, Fin.sum_univ_three])

theorem trace_diag_mul_cay (a b c x y z : ℝ) :
    Matrix.trace (!![a, 0, 0; 0, b, 0; 0, 0, c] * cayleyMatrix x y z) =
      (a * (1 + x ^ 2 - y ^ 2 - z ^ 2) + b * (1 - x ^ 2 + y ^ 2 - z ^ 2) +
        c * (1 - x ^ 2 - y ^ 2 + z ^ 2)) / cayleyDenom x y z := by
  simp [Matrix.trace, cayleyMatrix, Fin.sum_univ_three]
  ring

theorem step_chart (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ j < 5, ∃ r : Fin 3 → ℝ, Q = Qm j r ∧
      (∀ k < 5, Matrix.trace ((chartB k)ᵀ * Q) ≤ Matrix.trace ((chartB j)ᵀ * Q)) ∧
      ∀ i, |r i| ≤ (if j = 4 then 2 else 1) := by
  obtain ⟨j, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun k : Fin 5 => Matrix.trace ((chartB k)ᵀ * Q)) Finset.univ_nonempty
  have hmax' : ∀ k < 5, Matrix.trace ((chartB k)ᵀ * Q) ≤ Matrix.trace ((chartB j)ᵀ * Q) :=
    fun k hk => hmax ⟨k, hk⟩ (Finset.mem_univ _)
  have hnn : 0 ≤ Matrix.trace ((chartB j)ᵀ * Q) := by
    have := klein_trace_sum Q
    have h0 := hmax' 0 (by norm_num)
    have h1 := hmax' 1 (by norm_num)
    have h2 := hmax' 2 (by norm_num)
    have h3 := hmax' 3 (by norm_num)
    linarith
  have hA : (chartB j)ᵀ * Q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    refine Submonoid.mul_mem _ ?_ hQ
    have hB := chartB_mem_SO3 j
    rw [mem_SO3_iff'] at hB ⊢
    exact ⟨by rw [Matrix.transpose_transpose, chartB_transpose_mul_self],
      by rw [Matrix.det_transpose]; exact hB.2⟩
  obtain ⟨x, y, z, hr, hxyz⟩ := exists_cayleyMatrix_of_trace_nonneg _ hA hnn
  set r : Fin 3 → ℝ := ![x, y, z]
  have hQr : Q = Qm j r := by
    have hB := SO3_mul_transpose (chartB_mem_SO3 j)
    simp only [Qm, cayV, r, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← hxyz, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  refine ⟨j, j.isLt, r, hQr, hmax', ?_⟩
  by_cases hj4 : (j : ℕ) = 4
  · simp only [hj4, ite_true]
    intro i
    have hsq : r i ^ 2 ≤ 4 := by
      fin_cases i <;> simp [r] <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (r i - 2), sq_nonneg (r i + 2)]
  · simp only [hj4, ite_false]
    have hj : (j : ℕ) < 4 := by omega
    -- trace(C_m cay) ≤ trace(cay) for the three non-identity Klein elements
    have hc : ∀ m, 0 < m → m < 4 →
        Matrix.trace (chartB m * cayV r) ≤ Matrix.trace (cayV r) := by
      intro m hm0 hm4
      have hk := hmax' (j ^^^ m) (by
        have : j.val ^^^ m < 4 := Nat.xor_lt_two_pow (n := 2) hj hm4
        omega)
      rw [hQr, Qm, klein_mul _ _ hj hm4, ← Matrix.mul_assoc, chartB_transpose_mul_self,
        Matrix.one_mul] at hk
      exact hk
    have h1 := hc 1 (by norm_num) (by norm_num)
    have h2 := hc 2 (by norm_num) (by norm_num)
    have h3 := hc 3 (by norm_num) (by norm_num)
    have hd := cayleyDenom_pos x y z
    have ht := trace_cayleyMatrix x y z
    simp only [chartB, cayV, r, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, trace_diag_mul_cay, ht] at h1 h2 h3
    rw [div_le_div_iff_of_pos_right hd] at h1 h2 h3
    intro i
    rw [abs_le]
    fin_cases i <;> simp [r] <;> constructor <;> nlinarith

/-! ## The reduction -/

theorem reduction (h : IsRupert exactVerts) :
    ∃ u v : ℝ, ∃ j : ℕ, ∃ r : Fin 3 → ℝ, Reduced u v j r ∧
      RupPair (outerRot u v) (outerRot u v * Qm j r) := by
  obtain ⟨Ro, hRo, Ri, hRi, h0⟩ := exists_rupPair h
  obtain ⟨u, v, hu, hv, hw, hd, Ri1, hRi1, h1⟩ := step_outer hRo hRi h0
  obtain ⟨Ri2, hRi2, h2, horb⟩ := step_orbit hRi1 h1
  have hS := outerRot_mem_SO3 u v
  have hQ : (outerRot u v)ᵀ * Ri2 ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    refine Submonoid.mul_mem _ ?_ hRi2
    rw [mem_SO3_iff'] at hS ⊢
    exact ⟨by rw [Matrix.transpose_transpose, SO3_transpose_mul (outerRot_mem_SO3 u v)],
      by rw [Matrix.det_transpose]; exact hS.2⟩
  obtain ⟨j, hj, r, hQr, hch, hrb⟩ := step_chart _ hQ
  have hRi2' : Ri2 = outerRot u v * Qm j r := by
    rw [← hQr, ← Matrix.mul_assoc, SO3_mul_transpose (outerRot_mem_SO3 u v), Matrix.one_mul]
  refine ⟨u, v, j, r, ⟨hj, hu, hv, hw, hd, ?_, ?_, hrb⟩, hRi2' ▸ h2⟩
  · intro k hk; rw [← hQr]; exact hch k hk
  · intro e k; rw [← hQr]; exact horb e k

end Cayley

end
