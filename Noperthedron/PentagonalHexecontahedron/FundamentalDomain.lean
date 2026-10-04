module

public import Mathlib.Data.Finset.Max
public import Noperthedron.PentagonalHexecontahedron.CayleyAtlas

@[expose] public section

/-!
# The fivefold relative-rotation cell

The rotations about z by multiples of 2π/5 are symmetries of the model. A
relative rotation is in the fivefold max-trace (Dirichlet) cell when none of
them increases its trace on the right. The icosahedral cell
(`InIcoFundamentalDomain`) lies inside this one, so the fivefold prune rows
(`AtlasFundamentalPrune`), whose conditions are two quadratic inequalities
per Cayley chart, stay sound.
-/

namespace Noperthedron.PentagonalHexecontahedron

variable {P : C5Model}

open scoped Matrix

/-- The `k`th exact rotation around the symmetry axis. -/
noncomputable def fivefoldMatrix (k : OrbitIndex) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Rz_mat ((k : ℝ) * (2 * Real.pi / 5))

def composeSymmetry (a b : OrbitIndex) : OrbitIndex :=
  ⟨(a.val + b.val) % 5, Nat.mod_lt _ (by omega)⟩

@[simp] theorem fivefoldMatrix_zero : fivefoldMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fivefoldMatrix, Rz_mat]

theorem fivefoldMatrix_mul (a b : OrbitIndex) :
    fivefoldMatrix a * fivefoldMatrix b =
      fivefoldMatrix (composeSymmetry a b) := by
  change Rz_mat ((a : ℝ) * (2 * Real.pi / 5)) *
      Rz_mat ((b : ℝ) * (2 * Real.pi / 5)) =
    Rz_mat ((composeSymmetry a b : ℝ) * (2 * Real.pi / 5))
  rw [Bounding.Rz_mat_mul_Rz_mat]
  have hdecomp : (a.val : ℝ) + (b.val : ℝ) =
      (((a.val + b.val) % 5 : ℕ) : ℝ) +
        5 * (((a.val + b.val) / 5 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div (a.val + b.val) 5).symm
  have hangle :
      (a : ℝ) * (2 * Real.pi / 5) +
          (b : ℝ) * (2 * Real.pi / 5) =
        (composeSymmetry a b : ℝ) * (2 * Real.pi / 5) +
          ((((a.val + b.val) / 5 : ℕ) : ℝ) * (2 * Real.pi)) := by
    change (a.val : ℝ) * (2 * Real.pi / 5) +
        (b.val : ℝ) * (2 * Real.pi / 5) =
      (((a.val + b.val) % 5 : ℕ) : ℝ) * (2 * Real.pi / 5) +
        ((((a.val + b.val) / 5 : ℕ) : ℝ) * (2 * Real.pi))
    calc
      _ = ((a.val : ℝ) + b.val) * (2 * Real.pi / 5) := by ring
      _ = ((((a.val + b.val) % 5 : ℕ) : ℝ) +
          5 * (((a.val + b.val) / 5 : ℕ) : ℝ)) *
            (2 * Real.pi / 5) := by rw [hdecomp]
      _ = _ := by ring
  rw [hangle]
  convert Rz_mat_add_int_mul_two_pi
    (Int.ofNat ((a.val + b.val) / 5))
    ((composeSymmetry a b : ℝ) * (2 * Real.pi / 5)) using 1 <;>
    norm_num

/-- A relative rotation is in the identity fivefold Dirichlet cell when no
right symmetry increases its trace. -/
def InFivefoldFundamentalDomain
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ k : OrbitIndex,
    Matrix.trace (R * fivefoldMatrix k) ≤ Matrix.trace R

end Noperthedron.PentagonalHexecontahedron

end
