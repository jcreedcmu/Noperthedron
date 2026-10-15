module
-- Ported from NopertTriakisTetrahedron (Apache-2.0): Noperts/BalancedSupport/Rodrigues.lean

public import Noperthedron.Bounding.OrthEquivRotz
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

@[expose] public section

/-!
# Exact axis-angle decomposition

The local balanced-support argument needs an exact finite-rotation identity,
not an infinitesimal approximation.  We obtain it from the existing theorem
that every element of `SO(3)` is orthogonally conjugate to a rotation about
the z axis.
-/

namespace Cayley.BalancedSupport

open scoped Matrix Real RealInnerProductSpace

noncomputable def zFirst (v : ℝ³) : ℝ³ := !₂[-v 1, v 0, 0]

noncomputable def zRemainder (v : ℝ³) : ℝ³ := !₂[-v 0, -v 1, 0]

/-- Euclidean-space wrapper for the ordinary three-dimensional cross
product. -/
noncomputable def cross3 (v w : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (v.ofLp ⨯₃ w.ofLp)

/-- The standard unit z vector. -/
noncomputable def zAxis : ℝ³ := !₂[0, 0, 1]

theorem zFirst_eq_cross3 (v : ℝ³) : zFirst v = cross3 zAxis v := by
  ext i
  fin_cases i <;> simp [zFirst, cross3, zAxis, cross_apply]

def vecRows (x y z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![x, y, z]

theorem inner_cross3_eq_det (u v w : ℝ³) :
    ⟪u, cross3 v w⟫ = Matrix.det (vecRows u.ofLp v.ofLp w.ofLp) := by
  rw [cross3, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]
  simpa [vecRows] using triple_product_eq_det u.ofLp v.ofLp w.ofLp

private theorem vecRows_mul_transpose
    (M : Matrix (Fin 3) (Fin 3) ℝ) (x y z : Fin 3 → ℝ) :
    vecRows (M *ᵥ x) (M *ᵥ y) (M *ᵥ z) =
      vecRows x y z * M.transpose := by
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;>
    simp [vecRows, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]

private theorem det_vecRows_map
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (x y z : Fin 3 → ℝ) :
    Matrix.det (vecRows (M *ᵥ x) (M *ᵥ y) (M *ᵥ z)) =
      Matrix.det (vecRows x y z) * M.det := by
  rw [vecRows_mul_transpose, Matrix.det_mul, Matrix.det_transpose]

private theorem det_vecRows_cycle (x y z : Fin 3 → ℝ) :
    Matrix.det (vecRows x y z) = Matrix.det (vecRows y z x) := by
  simp only [vecRows]
  rw [← triple_product_eq_det, ← triple_product_eq_det]
  exact triple_product_permutation x y z

/-- Orientation-preserving orthonormal frames carry the standard infinitesimal
z rotation to cross product with their z axis. -/
theorem oriented_frame_first_inner
    (frame : ℝ³ ≃ₗᵢ[ℝ] ℝ³) (inverseMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (hinverse : ∀ x : ℝ³,
      (frame.symm x).ofLp = inverseMatrix *ᵥ x.ofLp)
    (v d : ℝ³) :
    ⟪d, frame (zFirst (frame.symm v))⟫ =
      inverseMatrix.det * ⟪frame zAxis, cross3 v d⟫ := by
  have hz : zAxis.ofLp = inverseMatrix *ᵥ (frame zAxis).ofLp := by
    simpa using hinverse (frame zAxis)
  calc
    ⟪d, frame (zFirst (frame.symm v))⟫ =
        ⟪frame.symm d, zFirst (frame.symm v)⟫ := by
      simpa using frame.inner_map_map (frame.symm d) (zFirst (frame.symm v))
    _ = Matrix.det (vecRows (frame.symm d).ofLp zAxis.ofLp
          (frame.symm v).ofLp) := by
      rw [zFirst_eq_cross3, inner_cross3_eq_det]
    _ = Matrix.det (vecRows (inverseMatrix *ᵥ d.ofLp)
          (inverseMatrix *ᵥ (frame zAxis).ofLp)
          (inverseMatrix *ᵥ v.ofLp)) := by rw [hinverse d, hz, hinverse v]
    _ = Matrix.det (vecRows d.ofLp (frame zAxis).ofLp v.ofLp) *
        inverseMatrix.det := det_vecRows_map inverseMatrix _ _ _
    _ = inverseMatrix.det *
        Matrix.det (vecRows (frame zAxis).ofLp v.ofLp d.ofLp) := by
      rw [det_vecRows_cycle]
      ring
    _ = inverseMatrix.det * ⟪frame zAxis, cross3 v d⟫ := by
      rw [inner_cross3_eq_det]

theorem Rz_apply_sub_exact (s : ℝ) (v : ℝ³) :
    RzL s v - v = (Real.sin s) • zFirst v + (1 - Real.cos s) • zRemainder v := by
  ext i
  fin_cases i <;>
    simp [RzL, Rz_mat, zFirst, zRemainder, Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- An axis-angle presentation of a three-dimensional rotation.  The axis is
encoded by the orthonormal frame taking the standard z axis to that axis. -/
structure AxisAngle (Q : ℝ³ →L[ℝ] ℝ³) where
  frame : ℝ³ ≃ₗᵢ[ℝ] ℝ³
  axis : ℝ³
  axis_norm : ‖axis‖ = 1
  first_inner : ∀ v d,
    ⟪d, frame (zFirst (frame.symm v))⟫ = ⟪axis, cross3 v d⟫
  angle : ℝ
  angle_mem : angle ∈ Set.Ioc (-Real.pi) Real.pi
  rotation_eq : Q =
    frame.toLinearIsometry.toContinuousLinearMap ∘L RzL angle ∘L
      frame.symm.toLinearIsometry.toContinuousLinearMap

noncomputable def AxisAngle.first {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) : ℝ³ :=
  a.frame (zFirst (a.frame.symm v))

noncomputable def AxisAngle.remainder {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) : ℝ³ :=
  a.frame (zRemainder (a.frame.symm v))

theorem AxisAngle.first_inner_eq {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v d : ℝ³) :
    ⟪d, a.first v⟫ = ⟪a.axis, cross3 v d⟫ := by
  exact a.first_inner v d

theorem AxisAngle.apply_sub_exact {Q : ℝ³ →L[ℝ] ℝ³}
    (a : AxisAngle Q) (v : ℝ³) :
    Q v - v = (Real.sin a.angle) • a.first v +
      (1 - Real.cos a.angle) • a.remainder v := by
  have hQ : Q v = a.frame (RzL a.angle (a.frame.symm v)) := by
    have h := congrArg (fun f : ℝ³ →L[ℝ] ℝ³ => f v) a.rotation_eq
    change Q v = a.frame.toLinearIsometry.toContinuousLinearMap
      (RzL a.angle (a.frame.symm.toLinearIsometry.toContinuousLinearMap v))
    simpa only [ContinuousLinearMap.comp_apply] using h
  rw [hQ]
  simp only [AxisAngle.first, AxisAngle.remainder]
  have hz := Rz_apply_sub_exact a.angle (a.frame.symm v)
  calc
    a.frame (RzL a.angle (a.frame.symm v)) - v =
        a.frame (RzL a.angle (a.frame.symm v) - a.frame.symm v) := by
      rw [map_sub, LinearIsometryEquiv.apply_symm_apply]
    _ = a.frame ((Real.sin a.angle) • zFirst (a.frame.symm v) +
        (1 - Real.cos a.angle) • zRemainder (a.frame.symm v)) := by rw [hz]
    _ = (Real.sin a.angle) • a.frame (zFirst (a.frame.symm v)) +
        (1 - Real.cos a.angle) • a.frame (zRemainder (a.frame.symm v)) := by
      rw [map_add, map_smul, map_smul]

theorem Rz_mod_two_pi (γ : ℝ) : ∃ γ' ∈ Set.Ioc (-π) π, Rz_mat γ = Rz_mat γ' := by
  refine ⟨toIocMod Real.two_pi_pos (-π) γ, ?_, ?_⟩
  · have h := toIocMod_mem_Ioc Real.two_pi_pos (-π) γ
    simpa [show -π + 2 * π = π by ring] using h
  · obtain ⟨k, hk⟩ : ∃ k : ℤ, toIocMod Real.two_pi_pos (-π) γ = γ - k • (2 * π) :=
      ⟨toIocDiv Real.two_pi_pos (-π) γ, rfl⟩
    rw [hk]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rz_mat, zsmul_eq_mul, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

theorem SO3_is_conj_Rz_within_pi (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (_ : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (γ : ℝ),
      γ ∈ Set.Ioc (-π) π ∧ A = U * Rz_mat γ * U⁻¹ := by
  obtain ⟨U, U_SO, γ, hγ⟩ := Bounding.SO3_is_conj_Rz A hA
  obtain ⟨γ', γ'_in, hγ'⟩ := Rz_mod_two_pi γ
  exact ⟨U, U_SO, γ', γ'_in, hγ' ▸ hγ⟩

/-- Every special orthogonal matrix has an exact `AxisAngle` presentation
with angle in `(-π,π]`. -/
theorem exists_axisAngle (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Nonempty (AxisAngle A.toEuclideanLin.toContinuousLinearMap) := by
  obtain ⟨U, hU, s, hs, hconj⟩ := SO3_is_conj_Rz_within_pi A hA
  let u : ℝ³ ≃ₗᵢ[ℝ] ℝ³ := Bounding.OrthogonalGroup.toLinearIsometryEquiv ⟨U, hU⟩
  have hu : ∀ x : ℝ³, (u x).ofLp = U *ᵥ x.ofLp :=
    Bounding.OrthogonalGroup.toLinearIsometryEquiv_apply ⟨U, hU⟩
  have hUdet : IsUnit U.det := Matrix.isUnit_det_of_left_inverse hU.1
  have hu_symm : ∀ x : ℝ³, (u.symm x).ofLp = U⁻¹ *ᵥ x.ofLp := fun x => by
    have h := hu (u.symm x)
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    rw [h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hUdet, Matrix.one_mulVec]
  have toCLM_mul : ∀ B C : Matrix (Fin 3) (Fin 3) ℝ,
      (B * C).toEuclideanLin.toContinuousLinearMap =
        B.toEuclideanLin.toContinuousLinearMap ∘L C.toEuclideanLin.toContinuousLinearMap := by
    intro B C
    ext v
    simp
  have hUclm : u.toLinearIsometry.toContinuousLinearMap =
      U.toEuclideanLin.toContinuousLinearMap := by
    ext x
    simp [hu]
  have hUinvclm : u.symm.toLinearIsometry.toContinuousLinearMap =
      U⁻¹.toEuclideanLin.toContinuousLinearMap := by
    ext x
    simp [hu_symm]
  let ug : Matrix.orthogonalGroup (Fin 3) ℝ := ⟨U, hU⟩
  have hUinv_orth : U⁻¹ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
    have hinv : (↑ug⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) * U = 1 := by
      simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using
        congrArg Subtype.val (inv_mul_cancel ug)
    rw [Matrix.inv_eq_left_inv hinv]
    exact ug⁻¹.property
  have hdet_sq : (U⁻¹).det ^ 2 = 1 := by
    rw [Matrix.mem_orthogonalGroup_iff] at hUinv_orth
    have horth := hUinv_orth
    have hdet := congrArg Matrix.det horth
    simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using hdet
  have hdet_abs : |(U⁻¹).det| = 1 := by
    rcases (sq_eq_one_iff.mp hdet_sq) with h | h <;> simp [h]
  have haxis : ‖(U⁻¹).det • u zAxis‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hdet_abs, one_mul, u.norm_map,
      EuclideanSpace.norm_eq]
    simp [zAxis, Fin.sum_univ_three]
  refine ⟨⟨u, (U⁻¹).det • u zAxis, haxis,
    (fun v d => by
      rw [real_inner_smul_left]
      exact oriented_frame_first_inner u U⁻¹ hu_symm v d),
    s, hs, ?_⟩⟩
  rw [hconj, toCLM_mul, toCLM_mul, hUclm, hUinvclm, RzL,
    ContinuousLinearMap.comp_assoc]

end Cayley.BalancedSupport

end
