module

public import Cayley.Soundness.Reduction.Shadow
public import Noperthedron.Bounding.OpNorm

@[expose] public section

/-!
# Moves that preserve Rupert pairs

* a common left factor that maps the z-axis to itself, and so acts on the screen by an
  isometry (the half-turn `Rx(π)`, and the quotient of two rotations with the same view);
* right multiplication of either rotation by a symmetry `Rz(2πk/15)`;
* left multiplication of the inner rotation by the screen half-turn `Rz(π)` (point symmetry).
-/

namespace Cayley

open Noperthedron Real
open scoped Matrix

theorem shadow_pointSym (R : Matrix (Fin 3) (Fin 3) ℝ) : PointSym (shadow R) :=
  continuousLinearMap_preserves_point_sym (screen R) exactHull_pointSym

/-- An orthogonal matrix whose third row is `±e_z` acts on the screen by an isometry, so it can
be applied to both rotations of a Rupert pair. -/
theorem rupPair_left {Ro Ri L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : L ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (h20 : L 2 0 = 0) (h21 : L 2 1 = 0)
    (h : RupPair Ro Ri) : RupPair (L * Ro) (L * Ri) := by
  have hrow := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hL
  have hcol := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hL
  -- the third column is `±e_z` as well
  have r22 := congrFun (congrFun hrow 2) 2
  have c22 := congrFun (congrFun hcol 2) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, h20, h21,
    Matrix.one_apply_eq, mul_zero, zero_add] at r22 c22
  obtain ⟨h02, h12⟩ : L 0 2 = 0 ∧ L 1 2 = 0 :=
    mul_self_add_mul_self_eq_zero.mp (by linarith)
  -- so the upper left block is orthogonal
  have hB : !![L 0 0, L 0 1; L 1 0, L 1 1] ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    have hij := congrFun (congrFun hrow (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h02, h12] using hij
  set e : ℝ² ≃ₗᵢ[ℝ] ℝ² := Bounding.OrthogonalGroup.toLinearIsometryEquiv ⟨_, hB⟩
  have hsh (R : Matrix (Fin 3) (Fin 3) ℝ) : shadow (L * R) = e '' shadow R := by
    rw [shadow, shadow, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [screen_mul, screen_apply, screen_apply]
    ext i
    fin_cases i <;>
      simp [e, Bounding.OrthogonalGroup.toLinearIsometryEquiv_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, h02, h12]
  rw [RupPair, hsh, hsh]
  exact (Set.image_mono h).trans (e.toHomeomorph.image_interior _).subset

/-- The half-turn about the x-axis. -/
def RxPi : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

theorem RxPi_mem_SO3 : RxPi ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [RxPi, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [RxPi, Matrix.det_fin_three]

theorem rupPair_RxPi {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (h : RupPair Ro Ri) :
    RupPair (RxPi * Ro) (RxPi * Ri) :=
  rupPair_left (Matrix.mem_specialOrthogonalGroup_iff.mp RxPi_mem_SO3).1 (by simp [RxPi])
    (by simp [RxPi]) h

/-! ## Symmetries of the Noperthedron -/

/-- The symmetry rotation `g_k = Rz(2πk/15)`. -/
noncomputable def gR (k : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := Rz_mat (2 * π * k / 15)

theorem gR_mem_SO3 (k : ℕ) : gR k ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  Rz_mat_mem_SO3 _

theorem gR_mul (k k' : ℕ) : gR k * gR k' = gR (k + k') := by
  simp only [gR, Rz_mat_mul_Rz_mat]; congr 1; push_cast; ring

theorem gR_mod (k : ℕ) : gR (k % 15) = gR k := by
  have h : ((k % 15 : ℕ) : ℝ) + 15 * ((k / 15 : ℕ) : ℝ) = (k : ℝ) :=
    mod_cast Nat.mod_add_div k 15
  rw [gR, gR, show 2 * π * ((k % 15 : ℕ) : ℝ) / 15 =
    2 * π * k / 15 + ((-((k / 15 : ℕ) : ℤ) : ℤ) : ℝ) * (2 * π) by
      simp only [Int.cast_neg, Int.cast_natCast]; linear_combination (2 * π / 15) * h,
    Rz_mat_add_int_mul_two_pi]

theorem gR_exactVertex (m : ℕ) (T : VertexIndex) :
    (gR m).toEuclideanLin (exactVertex T) =
      exactVertex ⟨⟨(T.k.val + m) % 15, Nat.mod_lt _ (by norm_num)⟩, T.ℓ, T.i⟩ := by
  have h : ∀ (k : ℕ) (v : ℝ³), RzL (2 * π * k / 15) v = (gR k).toEuclideanLin v := fun _ _ => rfl
  simp only [exactVertex]
  rw [map_zsmul, h, h, gR_mod, add_comm, ← gR_mul]
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

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
  rw [shadow, shadow]
  conv_rhs => rw [← gR_image_hull m]
  rw [Set.image_image]
  exact Set.image_congr fun p _ => screen_mul R (gR m) p

/-- The screen half-turn `Rz(π)`. -/
def ZR : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- `Rz(π)` negates the screen, and the shadow is centrally symmetric. -/
theorem shadow_ZR_mul (R : Matrix (Fin 3) (Fin 3) ℝ) : shadow (ZR * R) = shadow R := by
  have hneg : ∀ p : ℝ³, screen (ZR * R) p = -screen R p := by
    intro p
    rw [screen_mul, screen_apply]
    ext i; fin_cases i <;> simp [screen_apply, ZR, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [← neg_image_eq_if_pointsym _ (shadow_pointSym R), shadow, shadow, Set.image_image]
  exact Set.image_congr fun p _ => hneg p

theorem rupPair_inner_gR {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (m : ℕ) (h : RupPair Ro Ri) :
    RupPair Ro (Ri * gR m) := by
  unfold RupPair at *; rwa [shadow_mul_gR]

theorem rupPair_outer_gR {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (m : ℕ) (h : RupPair Ro Ri) :
    RupPair (Ro * gR m) Ri := by
  unfold RupPair at *; rwa [shadow_mul_gR]

theorem rupPair_inner_ZR {Ro Ri : Matrix (Fin 3) (Fin 3) ℝ} (h : RupPair Ro Ri) :
    RupPair Ro (ZR * Ri) := by
  unfold RupPair at *; rwa [shadow_ZR_mul]

end Cayley

end
