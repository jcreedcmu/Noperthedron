import Noperthedron.Rupert.Basic
import Noperthedron.PushLeft

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
def flip_y_equiv : (ℝ² ≃L[ℝ] ℝ²) := {
  flip_y with
  invFun := flip_y,
  left_inv := by intro v; ext i; fin_cases i <;> (simp [Matrix.vecHead, Matrix.vecTail])
  right_inv := by intro v; ext i; fin_cases i <;> (simp [Matrix.vecHead, Matrix.vecTail])
}

-- dimension reduction with a rotation baked in
@[simp]
noncomputable
def reduce_mat : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0,  1, 0;
     -1, 0, 0]

@[simp]
noncomputable
def reduceL : (ℝ³ →L[ℝ] ℝ²) := reduce_mat |>.toEuclideanLin.toContinuousLinearMap

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

noncomputable
def RxL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Rx_mat θ |>.toEuclideanLin.toContinuousLinearMap

@[simp]
noncomputable
def RxC : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := RxL α
  map_zero_eq_one' := by
    ext v i; fin_cases i <;> simp [RxL, Matrix.vecHead, Matrix.vecTail]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> (simp [RxL, Matrix.vecHead, Matrix.vecTail, cos_add, sin_add]; try ring)

lemma RxC_coe : RxC = RxL := rfl

@[simp]
noncomputable
def Ry_mat (θ : ℝ) : (Matrix (Fin 3) (Fin 3) ℝ) :=
  !![cos θ, 0, -sin θ;
     0,     1,      0;
     sin θ, 0,  cos θ]

noncomputable
def RyL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Ry_mat θ |>.toEuclideanLin.toContinuousLinearMap

@[simp]
noncomputable
def RyC : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := RyL α
  map_zero_eq_one' := by
    ext v i; fin_cases i <;> simp [RyL,  Matrix.vecHead, Matrix.vecTail]
  map_add_eq_mul' α β := by
    ext v i
    fin_cases i <;> (simp [RyL, Matrix.vecHead, Matrix.vecTail, cos_add, sin_add]; try ring)

lemma RyC_coe : RyC = RyL := rfl

-- rotation about z-axis by θ
@[simp]
noncomputable
def Rz_mat (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![cos θ, -sin θ, 0;
     sin θ,  cos θ, 0;
     0,      0,     1]

noncomputable
def RzL (θ : ℝ) : (ℝ³ →L[ℝ] ℝ³) := Rz_mat θ |>.toEuclideanLin.toContinuousLinearMap

@[simp]
noncomputable
def RzC : AddChar ℝ (ℝ³ →L[ℝ] ℝ³) where
  toFun α := RzL α
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [RzL, Matrix.vecHead, Matrix.vecTail]
  map_add_eq_mul' a b := by
    ext v i
    fin_cases i <;> {
      simp [RzL, Fin.sum_univ_succ, Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, Rz_mat, cos_add, sin_add];
      try ring_nf
    }

lemma RzC_coe : RzC = RzL := rfl

@[simp]
theorem Rz_mat_add_int_mul_two_pi (z : ℤ) (x : ℝ) : Rz_mat (x + z * (2 * π)) = Rz_mat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem RzC_two_pi (z : ℤ) : RzC (2 * π * z) = RzC 0 := by
  simp only [show 2 * π * z = 0 + z * (2 * π) by ring_nf, RzC, RzL, AddChar.coe_mk]
  simp only [Rz_mat_add_int_mul_two_pi]

@[simp]
noncomputable
def rot2_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun
      | 0, 0 => Real.cos α
      | 0, 1 => -Real.sin α
      | 1, 0 => Real.sin α
      | 1, 1 => Real.cos α

@[simp]
noncomputable
def rot2 : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := (rot2_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec]

  map_add_eq_mul' := by
    intro α β
    ext v i
    fin_cases i <;> {
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, rot2_mat, cos_add, sin_add]
      ring_nf
     }

noncomputable
def rot3_mat : Fin 3 → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => Rx_mat
  | 1 => Ry_mat
  | 2 => Rz_mat

noncomputable
def rot3 : Fin 3 → AddChar ℝ (ℝ³ →L[ℝ] ℝ³)
  | 0 => RxC
  | 1 => RyC
  | 2 => RzC

@[simp]
noncomputable
def rotR_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos α, -Real.sin α;
     Real.sin α,  Real.cos α]

@[simp]
noncomputable
def rotR'_mat (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-Real.sin α, -Real.cos α;
     Real.cos α,  -Real.sin α]

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
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_eq_sum, rotR_mat, cos_add, sin_add]
      ring_nf
     }

-- Derivative of rotR with respect to its parameter
@[simp]
noncomputable
def rotR' (α : ℝ) : ℝ² →L[ℝ] ℝ² :=
  (rotR'_mat α).toEuclideanLin.toContinuousLinearMap

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

/-
Some nice identities as laid out in [SY25] §2.2
-/

lemma vecX_identity (θ φ : ℝ) :
    vecX θ φ = (RzL θ ∘L RyL (-φ)) !₂[0, 0, 1] := by
  ext i
  fin_cases i <;> simp [RyL, RzL, Matrix.vecHead, Matrix.vecTail, vecX]

lemma rotM_identity (θ φ : ℝ) : rotM θ φ = reduceL ∘L RyL φ ∘L RzL (-θ) := by
  ext v i
  fin_cases i <;> (simp [RzL, RyL, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]; try ring_nf)

lemma rotprojRM_identity (θ φ α : ℝ) : rotprojRM θ φ α = reduceL ∘L RzL α ∘L RyL φ ∘L RzL (-θ) := by
  simp only [rotprojRM]
  ext v i
  fin_cases i <;>
  · simp [RzL, RyL, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
    ring_nf

lemma projxy_rotRM_eq_rotprojRM (θ φ α : ℝ) : proj_xyL ∘ rotRM θ φ α = rotprojRM θ φ α := by
  ext v i; fin_cases i <;>
  · simp [RyL, RzL, rotprojRM, rotRM, rotR, rotM, rotM_mat, Matrix.vecHead, Matrix.vecTail]
    ring_nf

lemma reduce_identity : reduceL = proj_xyL ∘L RzL (-(π / 2)) := by
  ext v i
  simp only [RzL]
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]

lemma rotR_add_pi_eq_neg_rotR {α : ℝ} :
    rotR (α + π) = -rotR α := by
  ext v i; fin_cases i <;>
  · simp [Matrix.vecHead, Matrix.vecTail, rotR, rotR_mat]; ring_nf

lemma rotM_mod_eq_neg_rotM {θ φ : ℝ} :
    rotM (θ + π) (2 * π - φ) = -rotM θ φ := by
  ext v i; fin_cases i <;>
  · simp [Matrix.vecHead, Matrix.vecTail, rotM, rotM_mat]; ring_nf

lemma rotRM_mod_eq_rotRM {α θ φ : ℝ} :
    rotR (α + π) ∘ rotM (θ + π) (2 * π - φ) = rotR α ∘ rotM θ φ := by
  simp only [rotR_add_pi_eq_neg_rotR, rotM_mod_eq_neg_rotM]
  ext; simp

lemma rotM_periodic_φ {θ φ : ℝ} {k : ℤ} :
    rotM θ (φ + k * (2 * π)) = rotM θ φ := by
  ext v i; fin_cases i <;>
  · simp [rotM, rotM_mat]

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
