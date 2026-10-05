module

public import Noperthedron.PentagonalHexecontahedron.CapWitness
public import Noperthedron.PentagonalHexecontahedron.CapCoverMain

@[expose] public section

/-!
# From support witnesses in the body frame to non-Rupert poses

`not_rupert_of_support`: if d ⊥ the view of a pose (d ≠ 0), every point of the
centrally symmetric solid S has ⟪d, v⟫ ≤ M, and some v_k ∈ S has
⟪d, R v_k⟫ ≥ M for the relative rotation R, then the pose is not Rupert.
(The witness n = proj(O d) of `CapWitness`, with O the outer rotation.)
-/

namespace Noperthedron.PentagonalHexecontahedron

open scoped Matrix RealInnerProductSpace

theorem inner_euc3 (a b : ℝ³) : ⟪a, b⟫ = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem inner_proj_xyL (a b : ℝ³) : ⟪proj_xyL a, proj_xyL b⟫ = ⟪a, b⟫ - a 2 * b 2 := by
  rw [inner_euc3]
  simp [PiLp.inner_apply, Fin.sum_univ_two, proj_xyL, proj_xy_mat, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  ring

/-- An orthogonal matrix preserves inner products. -/
theorem inner_orth (O : Matrix (Fin 3) (Fin 3) ℝ) (hO : Oᵀ * O = 1) (a b : ℝ³) :
    ⟪O.toEuclideanLin a, O.toEuclideanLin b⟫ = ⟪a, b⟫ := by
  have h : ∀ i j, ∑ k, O k i * O k j = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hO i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    exact this
  simp only [inner_euc3, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have h00 := h 0 0; have h01 := h 0 1; have h02 := h 0 2; have h11 := h 1 1; have h12 := h 1 2
  have h22 := h 2 2; have h10 := h 1 0; have h20 := h 2 0; have h21 := h 2 1
  simp [Fin.sum_univ_three] at h00 h01 h02 h11 h12 h22 h10 h20 h21
  linear_combination (a 0 * b 0) * h00 + (a 1 * b 1) * h11 + (a 2 * b 2) * h22 +
    (a 0 * b 1) * h01 + (a 0 * b 2) * h02 + (a 1 * b 2) * h12 + (a 1 * b 0) * h10 + (a 2 * b 0) * h20 +
    (a 2 * b 1) * h21

theorem not_rupert_of_support (p : MatrixPose) (S : Set ℝ³) (hS : ∀ v ∈ S, -v ∈ S)
    (d : ℝ³) (hd : d ≠ 0) (hview : (p.outerRot.val.toEuclideanLin d) 2 = 0)
    (M : ℝ) (hM : ∀ v ∈ S, ⟪d, v⟫ ≤ M) (vk : ℝ³) (hvk : vk ∈ S)
    (hk : M ≤ ⟪d, p.relativeRotation.toEuclideanLin vk⟫) : ¬ RupertPose p S := by
  set O := p.outerRot.val
  have hO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp p.outerRot.property.1
  set n := proj_xyL (O.toEuclideanLin d)
  have hn : n ≠ 0 := by
    intro h0
    have h1 : ⟪n, n⟫ = 0 := by rw [h0]; simp
    rw [inner_proj_xyL, inner_orth O hO, hview, mul_zero, sub_zero] at h1
    exact hd (inner_self_eq_zero.mp h1)
  apply not_rupertPose_of_witness p S hS n hn M _ vk hvk
  · -- ⟪n, proj(inner rot vk)⟫ = ⟪d, R vk⟫.
    have hinner : p.innerRot.val.toEuclideanLin vk = O.toEuclideanLin (p.relativeRotation.toEuclideanLin vk) := by
      rw [← Noperthedron.Atlas.MatrixPose.outer_mul_relativeRotation p]
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, O]
    rw [hinner, inner_proj_xyL, inner_orth O hO, hview, zero_mul, sub_zero]
    exact hk
  · intro v hv
    show ⟪n, proj_xyL (p.outerRot.val.toEuclideanLin.toAffineMap v)⟫ ≤ M
    simp only [LinearMap.coe_toAffineMap]
    rw [inner_proj_xyL, inner_orth O hO, hview, zero_mul, sub_zero]
    exact hM v hv

end Noperthedron.PentagonalHexecontahedron
