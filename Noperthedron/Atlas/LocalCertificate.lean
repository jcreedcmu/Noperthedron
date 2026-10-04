module

public import Noperthedron.Checker.SqrtFixed
public import Noperthedron.RationalApprox.RationalBalancedGlobal
public import Noperthedron.Atlas.LocalRigidity

@[expose] public section


/-!
# Rational rotation matrices

Rational approximations `rotRMQ` of the pose rotation matrices and the bound
`rotRMQ_difference_norm_bounded` on their distance from the exact ones.

(Extracted, with only what the certificates use, from the earlier snub-cube
proof attempt.)
-/

namespace Noperthedron.Atlas.LocalCertificate

open scoped Matrix RealInnerProductSpace
open RationalApprox GlobalTheorem


def frameQ (theta phi : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![-sinℚ theta, cosℚ theta, 0;
     -cosℚ theta * cosℚ phi, -sinℚ theta * cosℚ phi, sinℚ phi;
      cosℚ theta * sinℚ phi,  sinℚ theta * sinℚ phi, cosℚ phi]

def rzQ (alpha : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![cosℚ alpha, -sinℚ alpha, 0;
     sinℚ alpha,  cosℚ alpha, 0;
     0, 0, 1]

def frameApprox : Matrix (Fin 3) (Fin 3)
    RationalApprox.DistLeKappaEntry :=
  !![(.msin, .one), (.cos, .one), (.zero, .zero);
     (.mcos, .cos), (.msin, .cos), (.one, .sin);
     (.cos, .sin), (.sin, .sin), (.one, .cos)]

def rz3Approx : Matrix (Fin 3) (Fin 3)
    RationalApprox.DistLeKappaEntry :=
  !![(.one, .cos), (.one, .msin), (.zero, .zero);
     (.one, .sin), (.one, .cos), (.zero, .zero);
     (.zero, .zero), (.zero, .zero), (.one, .one)]

noncomputable def frameQCLM (theta phi : ℚ) : ℝ³ →L[ℝ] ℝ³ :=
  ((frameQ theta phi).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

noncomputable def rzQCLM (alpha : ℚ) : ℝ³ →L[ℝ] ℝ³ :=
  ((rzQ alpha).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

private theorem frameQ_difference_norm_bounded
    (theta phi : ℚ) (hθ : (theta : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hφ : (phi : ℝ) ∈ Set.Icc (-4 : ℝ) 4) :
    ‖rotRM (theta : ℝ) (phi : ℝ) 0 - frameQCLM theta phi‖ ≤
      RationalApprox.κ := by
  let θ4 : Set.Icc (-4 : ℝ) 4 := ⟨theta, hθ⟩
  let φ4 : Set.Icc (-4 : ℝ) 4 := ⟨phi, hφ⟩
  have hactual : rotRM (theta : ℝ) (phi : ℝ) 0 =
      RationalApprox.clinActual frameApprox θ4 φ4 := by
    rw [rotRM_eq_rotRM_mat]
    unfold RationalApprox.clinActual
    apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M.toEuclideanLin.toContinuousLinearMap)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotRM_mat, Rz_mat, Ry_mat, frameApprox, θ4, φ4,
        Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have happrox : frameQCLM theta phi =
      RationalApprox.clinApprox frameApprox θ4 φ4 := by
    unfold frameQCLM RationalApprox.clinApprox
    apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M.toEuclideanLin.toContinuousLinearMap)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [frameQ, frameApprox, θ4, φ4, sinℚ_match, cosℚ_match]
  rw [hactual, happrox]
  exact RationalApprox.norm_matrix_actual_approx_le_kappa
    (m := ⟨3, by norm_num⟩) (n := ⟨3, by norm_num⟩)
    frameApprox θ4 φ4

private theorem rzQ_difference_norm_bounded
    (alpha : ℚ) (hα : (alpha : ℝ) ∈ Set.Icc (-4 : ℝ) 4) :
    ‖RzL (alpha : ℝ) - rzQCLM alpha‖ ≤ RationalApprox.κ := by
  let z4 : Set.Icc (-4 : ℝ) 4 := ⟨0, by norm_num⟩
  let α4 : Set.Icc (-4 : ℝ) 4 := ⟨alpha, hα⟩
  have hactual : RzL (alpha : ℝ) =
      RationalApprox.clinActual rz3Approx z4 α4 := by
    unfold RzL RationalApprox.clinActual
    apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M.toEuclideanLin.toContinuousLinearMap)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rz_mat, rz3Approx, z4, α4]
  have happrox : rzQCLM alpha =
      RationalApprox.clinApprox rz3Approx z4 α4 := by
    unfold rzQCLM RationalApprox.clinApprox
    apply congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      M.toEuclideanLin.toContinuousLinearMap)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rzQ, rz3Approx, z4, α4, sinℚ_match, cosℚ_match]
  rw [hactual, happrox]
  exact RationalApprox.norm_matrix_actual_approx_le_kappa
    (m := ⟨3, by norm_num⟩) (n := ⟨3, by norm_num⟩)
    rz3Approx z4 α4

/-- Conservative full-rotation approximation error. -/
def rotationError : ℚ := 3 * κℚ + κℚ ^ 2

def rotRMQ (theta phi alpha : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  rzQ alpha * frameQ theta phi

noncomputable def rotRMQCLM (theta phi alpha : ℚ) : ℝ³ →L[ℝ] ℝ³ :=
  ((rotRMQ theta phi alpha).map fun x => (x : ℝ)).toEuclideanLin.toContinuousLinearMap

private theorem rotRM_eq_rz_comp (theta phi alpha : ℝ) :
    rotRM theta phi alpha = RzL alpha ∘L rotRM theta phi 0 := by
  have hmat : rotRM_mat theta phi alpha =
      Rz_mat alpha * rotRM_mat theta phi 0 := by
    simp only [rotRM_mat]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Bounding.Rz_mat_mul_Rz_mat, Bounding.Rz_mat_mul_Rz_mat]
    rw [add_comm]
    simp only [add_zero]
    rw [Bounding.Rz_mat_mul_Rz_mat]
  rw [rotRM_eq_rotRM_mat, rotRM_eq_rotRM_mat]
  ext v
  simp only [ContinuousLinearMap.comp_apply, RzL,
    LinearMap.coe_toContinuousLinearMap', Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply]
  rw [hmat, Matrix.mulVec_mulVec]

private theorem rotRMQCLM_eq_comp (theta phi alpha : ℚ) :
    rotRMQCLM theta phi alpha = rzQCLM alpha ∘L frameQCLM theta phi := by
  have hmap : ((rotRMQ theta phi alpha).map fun x => (x : ℝ)) =
      ((rzQ alpha).map fun x => (x : ℝ)) *
        ((frameQ theta phi).map fun x => (x : ℝ)) := by
    ext i j
    simp only [rotRMQ, Matrix.map_apply, Matrix.mul_apply]
    push_cast
    rfl
  ext v
  simp only [rotRMQCLM, rzQCLM, frameQCLM,
    ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  rw [hmap, Matrix.mulVec_mulVec]

theorem rotRMQ_difference_norm_bounded
    (theta phi alpha : ℚ)
    (hθ : (theta : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hφ : (phi : ℝ) ∈ Set.Icc (-4 : ℝ) 4)
    (hα : (alpha : ℝ) ∈ Set.Icc (-4 : ℝ) 4) :
    ‖rotRM (theta : ℝ) (phi : ℝ) (alpha : ℝ) -
        rotRMQCLM theta phi alpha‖ ≤ (rotationError : ℝ) := by
  have hframe := frameQ_difference_norm_bounded theta phi hθ hφ
  have hrz := rzQ_difference_norm_bounded alpha hα
  have hexactFrame : ‖rotRM (theta : ℝ) (phi : ℝ) 0‖ = 1 := by
    simp only [rotRM]
    rw [Bounding.Rz_preserves_op_norm, Bounding.Rz_preserves_op_norm,
      Bounding.Ry_preserves_op_norm, Bounding.Rz_norm_one]
  have hframeNorm : ‖frameQCLM theta phi‖ ≤ 1 + RationalApprox.κ :=
    RationalApprox.approx_norm_le hexactFrame.le hframe
  rw [rotRM_eq_rz_comp, rotRMQCLM_eq_comp]
  have hdecomp :
      RzL (alpha : ℝ) ∘L rotRM (theta : ℝ) (phi : ℝ) 0 -
          rzQCLM alpha ∘L frameQCLM theta phi =
        RzL (alpha : ℝ) ∘L
            (rotRM (theta : ℝ) (phi : ℝ) 0 - frameQCLM theta phi) +
          (RzL (alpha : ℝ) - rzQCLM alpha) ∘L frameQCLM theta phi := by
    ext v
    simp
  rw [hdecomp]
  calc
    ‖RzL (alpha : ℝ) ∘L
          (rotRM (theta : ℝ) (phi : ℝ) 0 - frameQCLM theta phi) +
        (RzL (alpha : ℝ) - rzQCLM alpha) ∘L frameQCLM theta phi‖ ≤
      ‖RzL (alpha : ℝ) ∘L
          (rotRM (theta : ℝ) (phi : ℝ) 0 - frameQCLM theta phi)‖ +
        ‖(RzL (alpha : ℝ) - rzQCLM alpha) ∘L frameQCLM theta phi‖ :=
      norm_add_le _ _
    _ ≤ 1 * RationalApprox.κ +
        RationalApprox.κ * (1 + RationalApprox.κ) := by
      apply add_le_add
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (le_of_eq (Bounding.Rz_norm_one _)) hframe
            (norm_nonneg _) (by norm_num))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hrz hframeNorm (norm_nonneg _) (by
            unfold RationalApprox.κ
            norm_num))
    _ ≤ (rotationError : ℝ) := by
      norm_num [rotationError, RationalApprox.κ, RationalApprox.κℚ]

end Noperthedron.Atlas.LocalCertificate

end
