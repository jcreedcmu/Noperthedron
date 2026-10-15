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

-- rotation about x-axis by θ
@[simp]
noncomputable
def Rx_mat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,     0,      0;
     0, cos θ, -sin θ;
     0, sin θ,  cos θ]

@[simp]
noncomputable
def Ry_mat (θ : ℝ) : (Matrix (Fin 3) (Fin 3) ℝ) :=
  !![cos θ, 0, -sin θ;
     0,     1,      0;
     sin θ, 0,  cos θ]

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
      try ring_nf
    }

lemma RzC_coe : RzC = RzL := rfl

@[simp]
theorem Rz_mat_add_int_mul_two_pi (z : ℤ) (x : ℝ) : Rz_mat (x + z * (2 * π)) = Rz_mat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem RzL_add_int_mul_two_pi (z : ℤ) (x : ℝ) : RzL (x + z * (2 * π)) = RzL x := by
  unfold RzL; rw [Rz_mat_add_int_mul_two_pi]

noncomputable
def rot3_mat : Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => Rx_mat
  | 1 => Ry_mat
  | 2 => Rz_mat

@[simp]
noncomputable
def rotR_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos α, -Real.sin α;
     Real.sin α,  Real.cos α]

-- [SY25] § 1.1 Definition 2
noncomputable
def rotR : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := (rotR_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext x i
    fin_cases i <;> simp [Matrix.toEuclideanLin, Matrix.vecHead, Matrix.vecTail]

  map_add_eq_mul' := by
    intro α β
    ext v i
    fin_cases i <;> {
      simp [Matrix.toLpLin_apply, Matrix.mulVec_eq_sum, rotR_mat, cos_add, sin_add]
      ring_nf
     }

/-
Some nice identities as laid out in [SY25] §2.2
-/

/-- Projecting to xy after Rz rotation equals 2D rotation after projection. -/
@[simp]
lemma proj_xyL_comp_RzL (δ : ℝ) : proj_xyL ∘L RzL δ = rotR δ ∘L proj_xyL := by
  ext v i
  fin_cases i <;> simp [proj_xyL, proj_xy_mat, RzL, Rz_mat, rotR, rotR_mat,
    Matrix.vecHead, Matrix.vecTail] <;> ring

/-- A convex polyhedron, given as a finite indexed set of vertices. -/
structure Polyhedron (ι X : Type) where
  v : ι → X

def Polyhedron.hull {ι : Type} [Fintype ι] (poly : Polyhedron ι ℝ³) : Set ℝ³ :=
  convexHull ℝ { poly.v i | i }

structure GoodPoly (ι : Type) [Fintype ι] [Nonempty ι] where
  vertices : Polyhedron ι ℝ³
  vertex_radius_le_one : ∀ i, ‖vertices.v i‖ ≤ 1

def GoodPoly.hull {ι : Type} [Fintype ι] [Nonempty ι] (poly : GoodPoly ι) : Set ℝ³ :=
  poly.vertices.hull

end
