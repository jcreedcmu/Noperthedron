module

public import Cayley.Soundness.Moves
public import Cayley.Soundness.CayleyMatrix

@[expose] public section

/-!
# Reduced poses in Cayley coordinates

The outer rotation is `s(u, v) = Cay(v, -u, 0)`; the inner rotation is
`s(u, v) · B_j · Cay(r)` for a chart base `B_j`. `Reduced u v j r` collects the
inequalities that the reduction (`Cayley.Soundness.Reduction`) guarantees.
-/

namespace Cayley

open Noperthedron Real
open scoped Matrix

/-- The outer rotation with stereographic view coordinates `(u, v)`. -/
noncomputable def outerRot (u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := cayleyMatrix v (-u) 0

/-- The Cayley rotation of a vector. -/
noncomputable def cayV (r : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := cayleyMatrix (r 0) (r 1) (r 2)

/-- `C3 = (x', y', ·) · 10⁻¹⁰`. -/
def c3xR : ℝ := 8193990033
def c3yR : ℝ := 5298215096
def kapR : ℝ := c3xR ^ 2 + c3yR ^ 2

/-- `τ`: minus the reflection in the vertical plane through `C3`. -/
noncomputable def tauR : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(c3xR ^ 2 - c3yR ^ 2) / kapR, -(2 * c3xR * c3yR) / kapR, 0;
     -(2 * c3xR * c3yR) / kapR, (c3xR ^ 2 - c3yR ^ 2) / kapR, 0;
     0, 0, -1]

/-- The chart bases: the Klein four-group and `τ`. -/
noncomputable def chartB : ℕ → Matrix (Fin 3) (Fin 3) ℝ
  | 0 => !![1, 0, 0; 0, 1, 0; 0, 0, 1]
  | 1 => !![1, 0, 0; 0, -1, 0; 0, 0, -1]
  | 2 => !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
  | 3 => !![-1, 0, 0; 0, -1, 0; 0, 0, 1]
  | _ => tauR

/-- The screen half-turn `Rz(π)`. -/
def ZR : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

/-- The half-turn about the outer view, `sᵀ Rz(π) s`. -/
noncomputable def Hmat (u v : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (outerRot u v)ᵀ * ZR * outerRot u v

/-- The orbit score `F(X) = max(tr X, tr(τᵀX) − 1/8)`. -/
noncomputable def Fsc (X : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  max (Matrix.trace X) (Matrix.trace (tauRᵀ * X) - 1 / 8)

/-- The relative rotation in chart `j`. -/
noncomputable def Qm (j : ℕ) (r : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := chartB j * cayV r

/-- The reduced domain. -/
structure Reduced (u v : ℝ) (j : ℕ) (r : Fin 3 → ℝ) : Prop where
  j_lt : j < 5
  u_nonneg : 0 ≤ u
  v_nonneg : 0 ≤ v
  wedge : v ≤ 57 / 128 * u
  disk : u ^ 2 + v ^ 2 ≤ 1
  chart : ∀ k < 5, Matrix.trace ((chartB k)ᵀ * Qm j r) ≤ Matrix.trace ((chartB j)ᵀ * Qm j r)
  orbit : ∀ (e : Bool) (k : ℕ),
    Fsc ((if e then Hmat u v else 1) * Qm j r * gR k) ≤ Fsc (Qm j r)
  rb : ∀ i, |r i| ≤ (if j = 4 then 2 else 1)

/-! ## Orthogonality -/

theorem mem_SO3_iff' (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ ↔ A * Aᵀ = 1 ∧ A.det = 1 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]

theorem tauR_mem_SO3 : tauR ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [mem_SO3_iff']
  have hk : kapR ≠ 0 := by unfold kapR c3xR c3yR; norm_num
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tauR, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;>
      unfold kapR <;> ring
  · simp [tauR, Matrix.det_fin_three]
    field_simp
    unfold kapR; ring

theorem chartB_mem_SO3 (j : ℕ) : chartB j ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rcases j with _ | _ | _ | _ | j
  all_goals first
    | exact tauR_mem_SO3
    | (rw [mem_SO3_iff']; constructor
       · ext i k; fin_cases i <;> fin_cases k <;>
           simp [chartB, Matrix.mul_apply, Fin.sum_univ_three]
       · simp [chartB, Matrix.det_fin_three])

theorem ZR_eq : ZR = Rz_mat π := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ZR, Rz_mat]

theorem outerRot_mem_SO3 (u v : ℝ) : outerRot u v ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  cayleyMatrix_mem_SO3 _ _ _

theorem cayV_mem_SO3 (r : Fin 3 → ℝ) : cayV r ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  cayleyMatrix_mem_SO3 _ _ _

theorem SO3_mul_transpose {A : Matrix (Fin 3) (Fin 3) ℝ}
    (h : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) : A * Aᵀ = 1 :=
  ((mem_SO3_iff' A).1 h).1

theorem SO3_transpose_mul {A : Matrix (Fin 3) (Fin 3) ℝ}
    (h : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) : Aᵀ * A = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (Matrix.mem_specialOrthogonalGroup_iff.mp h).1

end Cayley

end
