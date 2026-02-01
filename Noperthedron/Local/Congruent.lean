import Mathlib.Data.Real.CompleteField
import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.Basic
import Noperthedron.Local.EpsSpanning

namespace Local

open scoped RealInnerProductSpace Real
open scoped Matrix

def Triangle.toMatrix (P : Local.Triangle) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => P i j

def Triangle.toSymMatrix (P : Local.Triangle) : Matrix (Fin 3) (Fin 3) ℝ :=
  (P.toMatrix.transpose) * P.toMatrix

/--
[SY25] Lemma 35
-/
lemma congruent_iff_sym_matrix_eq (P Q : Triangle) (hQ : Invertible (Q.toMatrix)) :
    P.Congruent Q ↔ (P.toSymMatrix = Q.toSymMatrix) :=
  sorry
