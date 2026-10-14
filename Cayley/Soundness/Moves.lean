module

public import Cayley.Soundness.Shadow

@[expose] public section

/-!
# Moves that preserve Rupert pairs

* a common left factor acting on the screen by a linear homeomorphism
  (`Rz(γ)`, and `Rx(π)` which reflects the screen);
* right multiplication of either rotation by a symmetry `Rz(2πk/15)`;
* left multiplication of the inner rotation by `Rz(π)` (point symmetry).
-/

namespace Cayley

open Noperthedron Real
open scoped Matrix

theorem shadow_left (L R : Matrix (Fin 3) (Fin 3) ℝ) (A : ℝ² ≃L[ℝ] ℝ²)
    (hA : ∀ x : ℝ³, proj_xyL (L.toEuclideanLin x) = A (proj_xyL x)) :
    shadow (L * R) = A '' shadow R := by
  unfold shadow
  rw [Set.image_image]
  apply Set.image_congr
  intro p _
  rw [← hA]
  congr 1
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem rupPair_left {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (L : Matrix (Fin 3) (Fin 3) ℝ)
    (A : ℝ² ≃L[ℝ] ℝ²) (hA : ∀ x : ℝ³, proj_xyL (L.toEuclideanLin x) = A (proj_xyL x))
    (h : RupPair Ro Ri) : RupPair (L * Ro) (L * Ri) := by
  unfold RupPair at *
  rw [shadow_left L Ro A hA, shadow_left L Ri A hA]
  have hc := Homeomorph.image_closure A.toHomeomorph (shadow Ri)
  have hi := Homeomorph.image_interior A.toHomeomorph (shadow Ro)
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at hc hi
  rw [← hc, ← hi]
  exact Set.image_mono h

theorem rupPair_Rz (γ : ℝ) {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (h : RupPair Ro Ri) :
    RupPair (Rz_mat γ * Ro) (Rz_mat γ * Ri) := by
  refine rupPair_left _ (MatrixPose.rotR_equiv γ) (fun x => ?_) h
  have := ContinuousLinearMap.ext_iff.mp (proj_xyL_comp_RzL γ) x
  exact this

/-- The half-turn about the x-axis. -/
def RxPi : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

/-- The reflection `(a, b) ↦ (a, -b)` of the screen. -/
noncomputable def screenRefl : ℝ² →L[ℝ] ℝ² :=
  (Matrix.toEuclideanLin !![(1 : ℝ), 0; 0, -1]).toContinuousLinearMap

theorem screenRefl_apply (z : ℝ²) : screenRefl z = !₂[z 0, -z 1] := by
  ext i; fin_cases i <;> simp [screenRefl, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

noncomputable def screenReflEquiv : ℝ² ≃L[ℝ] ℝ² :=
  ContinuousLinearEquiv.equivOfInverse screenRefl screenRefl
    (fun z => by ext i; fin_cases i <;> simp [screenRefl_apply])
    (fun z => by ext i; fin_cases i <;> simp [screenRefl_apply])

theorem rupPair_RxPi {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (h : RupPair Ro Ri) :
    RupPair (RxPi * Ro) (RxPi * Ri) := by
  refine rupPair_left _ screenReflEquiv (fun x => ?_) h
  change _ = screenRefl _
  rw [screenRefl_apply]
  ext i; fin_cases i <;>
    simp [RxPi, proj_xyL, proj_xy_mat, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]

/-! ## Symmetries of the Noperthedron -/

/-- The symmetry rotation `g_k = Rz(2πk/15)`. -/
noncomputable def gR (k : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := Rz_mat (2 * π * k / 15)

theorem RzL_add_apply (α β : ℝ) (v : ℝ³) : RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

theorem RzL_nat_mod_15 (x : ℕ) :
    RzL (2 * π * ((x % 15 : ℕ) : ℝ) / 15) = RzL (2 * π * (x : ℝ) / 15) := by
  have hreal : ((x % 15 : ℕ) : ℝ) = (x : ℝ) + ((-((x / 15 : ℕ) : ℤ) : ℤ) : ℝ) * 15 := by
    have := Nat.mod_add_div x 15
    have h2 : ((x % 15 : ℕ) : ℝ) + 15 * ((x / 15 : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast this
    simp only [Int.cast_neg, Int.cast_natCast]; linarith
  rw [hreal, show 2 * π * ((x : ℝ) + ((-((x / 15 : ℕ) : ℤ) : ℤ) : ℝ) * 15) / 15 =
    2 * π * x / 15 + ((-((x / 15 : ℕ) : ℤ) : ℤ) : ℝ) * (2 * π) by ring, RzL_add_int_mul_two_pi]

theorem gR_exactVertex (m : ℕ) (T : VertexIndex) :
    (gR m).toEuclideanLin (exactVertex T) =
      exactVertex ⟨⟨(T.k.val + m) % 15, Nat.mod_lt _ (by norm_num)⟩, T.ℓ, T.i⟩ := by
  simp only [exactVertex]
  rw [map_zsmul, RzL_nat_mod_15, show 2 * π * ((T.k.val + m : ℕ) : ℝ) / 15 =
    2 * π * m / 15 + 2 * π * T.k.val / 15 by push_cast; ring, RzL_add_apply]
  rfl

theorem gR_image_hull (m : ℕ) : (gR m).toEuclideanLin '' exactHull = exactHull := by
  have himg : (gR m).toEuclideanLin '' (exactVerts : Set ℝ³) = exactVerts := by
    ext x
    simp only [exactVerts, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image,
      Set.mem_range]
    constructor
    · rintro ⟨y, ⟨T, rfl⟩, rfl⟩
      exact ⟨_, (gR_exactVertex m T).symm⟩
    · rintro ⟨T, rfl⟩
      refine ⟨exactVertex ⟨⟨(T.k.val + (15 - m % 15)) % 15, Nat.mod_lt _ (by norm_num)⟩,
        T.ℓ, T.i⟩, ⟨_, rfl⟩, ?_⟩
      rw [gR_exactVertex]
      congr 2
      ext
      simp only
      omega
  rw [exactHull, LinearMap.image_convexHull, himg]

theorem shadow_mul_gR (R : Matrix (Fin 3) (Fin 3) ℝ) (m : ℕ) : shadow (R * gR m) = shadow R := by
  unfold shadow
  conv_rhs => rw [← gR_image_hull m]
  rw [Set.image_image]
  apply Set.image_congr
  intro p _
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- `Rz(π)` negates the screen, and the shadow is centrally symmetric. -/
theorem shadow_RzPi_mul (R : Matrix (Fin 3) (Fin 3) ℝ) : shadow (Rz_mat π * R) = shadow R := by
  have hneg : ∀ p : ℝ³, proj_xyL ((Rz_mat π * R).toEuclideanLin p) =
      proj_xyL (R.toEuclideanLin (-p)) := by
    intro p
    ext i; fin_cases i <;>
      simp [proj_xyL, proj_xy_mat, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Rz_mat, Matrix.mul_apply, Matrix.vecMul] <;> ring
  have hsym : ∀ p ∈ exactHull, -p ∈ exactHull := by
    intro p hp
    have := exactPolyhedron_point_symmetric
    rw [exactPolyhedron_hull] at this
    exact this p hp
  ext z
  simp only [shadow, Set.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨-p, hsym p hp, (hneg p).symm⟩
  · rintro ⟨p, hp, rfl⟩; refine ⟨-p, hsym p hp, ?_⟩; rw [hneg, neg_neg]

theorem rupPair_inner_gR {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (m : ℕ) (h : RupPair Ro Ri) :
    RupPair Ro (Ri * gR m) := by
  unfold RupPair at *; rwa [shadow_mul_gR]

theorem rupPair_outer_gR {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (m : ℕ) (h : RupPair Ro Ri) :
    RupPair (Ro * gR m) Ri := by
  unfold RupPair at *; rwa [shadow_mul_gR]

theorem rupPair_inner_RzPi {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (h : RupPair Ro Ri) :
    RupPair Ro (Rz_mat π * Ri) := by
  unfold RupPair at *; rwa [shadow_RzPi_mul]

end Cayley

end
