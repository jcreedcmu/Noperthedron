module

public import Noperthedron.BalancedSupport.TranslatedPose
public import Noperthedron.PoseInterval

@[expose] public section


/-!
# Pose parameters

Every rotation in SO(3) has Euler-type parameters (`rotRM`) in bounded
intervals; used to restrict the pose domain.

(Extracted, with only what the #231 proof uses, from the earlier snub-cube
proof attempt.)
-/

namespace Noperthedron.Atlas

open Real
open scoped Matrix

/-- A projective fundamental chamber for viewing directions.  The first
coordinate is chosen maximal after moving the vector into the positive
octant. -/
def ViewInChamber (v : Fin 3 → ℝ) : Prop :=
  0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2 ∧ v 1 ≤ v 0 ∧ v 2 ≤ v 0

private def matrixThirdRow (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ³ :=
  WithLp.toLp 2 (fun j => M 2 j)

private theorem matrixThirdRow_norm (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ‖matrixThirdRow M‖ = 1 := by
  have hparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hM
  have horth : M * Mᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hparts.1
  have h22 := congrFun (congrFun horth (2 : Fin 3)) (2 : Fin 3)
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h22
  have hs : M 2 0 ^ 2 + M 2 1 ^ 2 + M 2 2 ^ 2 = 1 := by
    nlinarith [h22]
  rw [EuclideanSpace.norm_eq]
  simp [matrixThirdRow, Fin.sum_univ_three, sq_abs, hs]

/-- Every unit vector has spherical coordinates in the standard bounded
domain.  Unlike `exists_positive_spherical_coords`, this does not assume an
octant, so the azimuth may be negative and the polar angle may exceed `π/2`.
-/
theorem exists_bounded_spherical_coords (v : ℝ³) (hv : ‖v‖ = 1) :
    ∃ θ φ : ℝ, θ ∈ Set.Ioc (-π) π ∧ φ ∈ Set.Icc 0 π ∧
      v = ![Real.sin φ * Real.cos θ, Real.sin φ * Real.sin θ, Real.cos φ] := by
  let θ := Complex.arg (v 0 + v 1 * Complex.I)
  let φ := Real.arccos (v 2)
  refine ⟨θ, φ, ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩,
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  have hv' := hv
  simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs,
    Fin.sum_univ_three, sqrt_eq_one, Nat.succ_eq_add_one,
    Nat.reduceAdd] at hv' ⊢
  have h_cos_sin : Real.cos φ = v 2 ∧
      Real.sin φ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2) := by
    dsimp only [φ]
    rw [Real.cos_arccos, Real.sin_arccos] <;>
      try linarith [sq_nonneg (1 + v 2), sq_nonneg (1 - v 2),
        sq_nonneg (v 0), sq_nonneg (v 1)]
    exact ⟨rfl, congrArg Real.sqrt <| sub_eq_iff_eq_add.mpr hv'.symm⟩
  by_cases h : v 0 + v 1 * Complex.I = 0
  · simp_all
    simp_all [Complex.ext_iff]
    ext i
    fin_cases i <;> tauto
  · have hpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      rw [← Complex.normSq_add_mul_I]
      exact Complex.normSq_pos.mpr h
    dsimp only [θ]
    simp_all [Complex.cos_arg, Complex.sin_arg]
    simp [Complex.normSq, Complex.norm_def] at *
    simp [← sq, mul_div_cancel₀ _ (ne_of_gt <| Real.sqrt_pos.mpr hpos)]
    ext i
    fin_cases i <;> rfl

/-- Every SO(3) matrix has `rotRM` coordinates in the standard bounded Euler
domain.  This complements the smaller positive-octant theorem above and is
used when a separately chosen symmetry must be preserved. -/
theorem SO3_to_bounded_rotRM_params
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ θ φ α : ℝ,
      θ ∈ Set.Ioc (-π) π ∧ φ ∈ Set.Icc 0 π ∧
      α ∈ Set.Ioc (-π) π ∧ M = rotRM_mat θ φ α := by
  obtain ⟨θ, φ, hθ, hφ, hrow⟩ := exists_bounded_spherical_coords
    (matrixThirdRow M) (matrixThirdRow_norm M hM)
  let B := rotRM_mat θ φ 0
  have hB : B ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    rotRM_mat_mem_SO3 θ φ 0
  have hBrow (j : Fin 3) : B 2 j = M 2 j := by
    have hj := congrFun hrow j
    fin_cases j <;>
      simpa [matrixThirdRow, B, rotRM_mat, Matrix.mul_apply,
        Fin.sum_univ_three] using hj.symm
  have hBt : Bᵀ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    have hBparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hB
    rw [Matrix.mem_specialOrthogonalGroup_iff,
      Matrix.mem_orthogonalGroup_iff]
    constructor
    · simpa only [Matrix.transpose_transpose] using
        (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hBparts.1
    · simpa only [Matrix.det_transpose] using hBparts.2
  let A := M * Bᵀ
  have hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    Submonoid.mul_mem _ hM hBt
  let ez : Fin 3 → ℝ := fun i => if i = 2 then 1 else 0
  have htranspose_ez : Bᵀ *ᵥ ez = Mᵀ *ᵥ ez := by
    ext j
    simpa [ez, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hBrow j
  have hAfix : A.toEuclideanLin !₂[0, 0, 1] = !₂[0, 0, 1] := by
    ext j
    change (A *ᵥ (![0, 0, 1] : Fin 3 → ℝ)) j =
      (![0, 0, 1] : Fin 3 → ℝ) j
    have hez : (![0, 0, 1] : Fin 3 → ℝ) = ez := by
      funext i
      fin_cases i <;> simp [ez]
    rw [hez]
    rw [show A *ᵥ ez = M *ᵥ (Bᵀ *ᵥ ez) by
      simp only [A, Matrix.mulVec_mulVec]]
    rw [htranspose_ez, Matrix.mulVec_mulVec]
    have hMparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hM
    rw [(Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hMparts.1,
      Matrix.one_mulVec]
  obtain ⟨α, hα⟩ := Bounding.SO3_fixing_z_is_Rz A hA hAfix
  have hBparts := (Matrix.mem_specialOrthogonalGroup_iff).mp hB
  have hBtB : Bᵀ * B = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hBparts.1
  have hrecover : A * B = M := by
    simp only [A, Matrix.mul_assoc, hBtB, Matrix.mul_one]
  have hform : M = rotRM_mat θ φ α := by
    rw [← hrecover, hα]
    simp only [B, rotRM_mat, Bounding.Rz_mat_zero, Matrix.mul_one,
      ← Matrix.mul_assoc, Bounding.Rz_mat_mul_Rz_mat]
    congr 3
    ring
  obtain ⟨α', hα'mem, hα'⟩ := Bounding.Rz_mod_two_pi α
  refine ⟨θ, φ, α', hθ, hφ, hα'mem, hform.trans ?_⟩
  simp only [rotRM_mat]
  rw [hα']

end Noperthedron.Atlas

end
