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
  Matrix.of fun
      | 0, 0 => Real.cos α
      | 0, 1 => -Real.sin α
      | 1, 0 => Real.sin α
      | 1, 1 => Real.cos α

-- [SY25] § 1.1 Definition 2
@[simp]
noncomputable
def rotR : AddChar ℝ (ℝ² →L[ℝ] ℝ²) where
  toFun α := (rotR_mat α).toEuclideanLin.toContinuousLinearMap
  map_zero_eq_one' := by
    ext v i
    fin_cases i <;> simp [Matrix.toEuclideanLin_apply, Matrix.mulVec]

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
  let A : Matrix (Fin 2) (Fin 2) ℝ :=
    !![-sin α, -cos α; cos α, -sin α]
  A.toEuclideanLin.toContinuousLinearMap

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
A little convenience lemma to turn a Nonempty typeclass into a Finset.Nonempty fact
for a image of that finite set. FIXME: is this unused now?
-/
lemma Finset.image_nonempty' {α β : Type} (s : Finset α) {f : α → β} [n : Nonempty s] [DecidableEq β] :
    (s.image f).Nonempty :=
  s.image_nonempty.mpr (nonempty_coe_sort.mp n)

noncomputable
def polyhedron_radius {n : ℕ} (S : Finset (E n)) (ne : S.Nonempty) : ℝ :=
  (S.image (‖·‖)).max' (by simp [Finset.image_nonempty]; exact ne)

theorem polyhedron_radius_def {n : ℕ} {r : ℝ} (S : Finset (E n)) (ne : S.Nonempty)
    (v : E n) (v_in_S : v ∈ S) (hv : ‖v‖ = r) (bound : ∀ v ∈ S, ‖v‖ ≤ r) :
    polyhedron_radius S ne = r := by
  sorry
