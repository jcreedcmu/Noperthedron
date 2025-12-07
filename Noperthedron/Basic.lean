import Noperthedron.Rupert.Basic

open scoped Matrix

/--
A finite collection of vertices in ℝ³
-/
structure Shape : Type where
  vertices : Finset ℝ³

namespace Shape

def hull (s : Shape) : Set ℝ³ := convexHull ℝ (s.vertices)

end Shape

open Real

-- flip about y-axis
@[simp]
noncomputable
def flip_y_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,  0;
     0, -1]

@[simp]
noncomputable
def flip_y : (ℝ² →L[ℝ] ℝ²) := flip_y_mat |>.toEuclideanLin.toContinuousLinearMap

@[simp]
noncomputable
def proj_xy_mat : Matrix (Fin 2) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0]

@[simp]
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
def RxL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Rx_mat θ |>.toEuclideanLin.toContinuousLinearMap

-- rotation about y-axis by θ
@[simp]
noncomputable
def Ry_mat (θ : ℝ) : (Matrix (Fin 3) (Fin 3) ℝ) :=
  !![cos θ, 0, -sin θ;
     0,     1,      0;
     sin θ, 0,  cos θ]

noncomputable
def RyL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Ry_mat θ |>.toEuclideanLin.toContinuousLinearMap

-- rotation about z-axis by θ
@[simp]
noncomputable
def Rz_mat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0;
     sin θ,  cos θ, 0;
     0,      0,     1]

noncomputable
def RzL : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := (Rz_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
  map_add_eq_mul' := by
    intro a b
    ext v i
    fin_cases i <;> {
      simp [Fin.sum_univ_succ, Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Rz_mat, cos_add, sin_add];
      try ring_nf
    }

@[simp]
noncomputable
def rotR_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos α, -Real.sin α;
     Real.sin α,  Real.cos α]

-- [SY25] § 1.1 Definition 2
@[simp]
noncomputable
def rotR : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := (rotR_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    simp only [rotR_mat, cos_zero, sin_zero, neg_zero, LinearMap.coe_toContinuousLinearMap',
      Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.cons_mulVec,
      Matrix.cons_dotProduct, one_mul, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, zero_add,
      Matrix.empty_mulVec, ContinuousLinearMap.one_apply]
    simp only [Matrix.vecHead, Fin.isValue, Matrix.vecTail, Nat.succ_eq_add_one, Nat.reduceAdd,
      Function.comp_apply, Fin.succ_zero_eq_one]
    fin_cases i <;> rfl

  map_add_eq_mul' := by
    intro α β
    ext v i
    fin_cases i <;> {
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, rotR_mat, cos_add, sin_add]
      ring_nf
     }

-- Derivative of rotR with respect to its parameter
noncomputable
def rotR' (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  (rotR_mat α).toEuclideanLin.toContinuousLinearMap

-- [SY25] § 1.1 Definition 2
noncomputable
def vecX (θ : ℝ) (φ : ℝ) : ℝ³ :=
  !₂[ cos θ * sin φ, sin θ * sin φ, cos φ ]

-- [SY25] § 1.1 Definition 2
noncomputable
def rotM_mat (θ : ℝ) (φ : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![-sin θ, cos θ, 0; -cos θ * cos φ, -sin θ * cos φ, sin φ]

noncomputable
def rotM (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotM_mat θ φ |>.toEuclideanLin.toContinuousLinearMap

-- Partial derivative of rotM with respect to θ
noncomputable
def rotMθ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  let A : Matrix (Fin 2) (Fin 3) ℝ :=
    !![-cos θ, -sin θ, 0; sin θ * cos φ, -cos θ * cos φ, 0]
  A.toEuclideanLin.toContinuousLinearMap

-- Partial derivative of rotM with respect to φ
noncomputable
def rotMφ (θ : ℝ) (φ : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  let A : Matrix (Fin 2) (Fin 3) ℝ :=
    !![0, 0, 0; cos θ * sin φ, sin θ * sin φ, cos φ]
  A.toEuclideanLin.toContinuousLinearMap

theorem sin_neg_pi_div_two : Real.sin (-(π / 2)) = -1 := by
  simp only [Real.sin_neg, Real.sin_pi_div_two]

theorem cos_neg_pi_div_two : Real.cos (-(π / 2)) = 0 := by
  simp only [Real.cos_neg, Real.cos_pi_div_two]

infixr:80 " ∘ᵃ " => AffineMap.comp

-- This is R(α) M(θ, φ) in (5) in [SY25] § 2.2,
-- except we don't project to ℝ²
noncomputable
def rotRM (θ : ℝ) (φ : ℝ) (α : ℝ) : ℝ³ →L[ℝ] ℝ³ :=
  RzL (-(π / 2)) ∘L RzL α ∘L RyL φ ∘L RzL (-θ)

-- This is R(α) M(θ, φ) in (5) in [SY25] § 2.2,
noncomputable
def rotprojRM (θ : ℝ) (φ : ℝ) (α : ℝ) : ℝ³ →L[ℝ] ℝ² :=
  rotR α ∘L rotM θ φ

/--
The description of rotRM as axis rotations followed by a projection is the same
thing as the description of rotprojRM as the 2×2 R matrix after the 2×3 M matrix
-/
lemma proj_rotrm_eq_rotprojrm (θ φ α : ℝ) : proj_xyL ∘L rotRM θ φ α = rotprojRM α θ φ := by
  ext1 v
  sorry

noncomputable
def polyhedronRadius {n : ℕ} (S : Finset (E n)) (ne : S.Nonempty) : ℝ :=
  (S.image (‖·‖)).max' (by simp [Finset.image_nonempty]; exact ne)

theorem polyhedron_radius_iff {n : ℕ} {r : ℝ} (S : Finset (E n)) (ne : S.Nonempty) :
    polyhedronRadius S ne = r ↔ (∃ v ∈ S, ‖v‖ = r) ∧ ∀ v ∈ S, ‖v‖ ≤ r := by
  constructor
  · intro h
    simp only [polyhedronRadius, Finset.max'_eq_iff] at h
    let ⟨h1, h2⟩ := h
    simp only [Finset.mem_image] at h1 h2
    simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h2
    exact ⟨h1, h2⟩
  · intro h
    simpa [polyhedronRadius, Finset.max'_eq_iff]

structure GoodPoly : Type where
  vertices : Finset ℝ³
  nonempty : vertices.Nonempty
  nontriv : ∀ v ∈ vertices, ‖v‖ > 0
  radius_eq_one : polyhedronRadius vertices nonempty = 1

def GoodPoly.hull (poly : GoodPoly) : Set ℝ³ :=
  convexHull ℝ poly.vertices

theorem GoodPoly.vertex_radius_le_one (poly : GoodPoly) : ∀ v ∈ poly.vertices, ‖v‖ ≤ 1 := by
  have := poly.radius_eq_one
  simp_all only [polyhedron_radius_iff, implies_true]
