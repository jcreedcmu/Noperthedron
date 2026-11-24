module

public import Noperthedron.Rupert.Basic

@[expose] public section

open scoped Matrix

open Real

noncomputable
def proj_xy_mat : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0]

noncomputable
def proj_xyL : (ℝ³ →L[ℝ] ℝ²) := proj_xy_mat |>.toEuclideanLin.toContinuousLinearMap

/-
As mere functions, `proj_xy` and `proj_xyL` are the same.
The only difference is that `proj_xyL` knows that it is continuous linear,
and it's defined a little differently, via a matrix, which is the reason
that it's so easy to see that it's linear.

I think we ought to prefer `proj_xyL` to `proj_xy` in most places.
but this lemma lets us push back the boundary between the newer uses
of `proj_xyL` and the older uses of `proj_xy`.
-/
lemma proj_xy_eq_proj_xyL :
    proj_xy = proj_xyL := by
  ext1
  simp only [proj_xy, Fin.isValue, proj_xyL, proj_xy_mat, LinearMap.coe_toContinuousLinearMap']
  ext i
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]

-- rotation about z-axis by θ
@[simp]
noncomputable
def Rz_mat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0;
     sin θ,  cos θ, 0;
     0,      0,     1]

noncomputable
def RzL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Rz_mat θ |>.toEuclideanLin.toContinuousLinearMap

noncomputable
def RzC : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := RzL α
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [RzL, Matrix.vecHead, Matrix.vecTail]
  map_add_eq_mul' a b := by
    ext v i
    fin_cases i <;> {
      simp [RzL, Fin.sum_univ_succ, Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, Rz_mat, cos_add, sin_add];
      first | done | ring_nf
    }

lemma RzC_coe : RzC = RzL := rfl

@[simp]
theorem Rz_mat_add_int_mul_two_pi (z : ℤ) (x : ℝ) : Rz_mat (x + z * (2 * π)) = Rz_mat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem RzL_add_int_mul_two_pi (z : ℤ) (x : ℝ) : RzL (x + z * (2 * π)) = RzL x := by
  unfold RzL; rw [Rz_mat_add_int_mul_two_pi]

theorem Rz_mat_mem_SO3 (θ : ℝ) : Rz_mat θ ∈ SO3 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, ← sq] <;> ring
  · simp [Matrix.det_fin_three, ← sq]

/-- Rz(α) * Rz(β) = Rz(α + β). -/
lemma Rz_mat_mul_Rz_mat (α β : ℝ) : Rz_mat α * Rz_mat β = Rz_mat (α + β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz_mat, cos_add, sin_add] <;> ring

end
