module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

notation "Euc(" n:arg ")" => EuclideanSpace ℝ (Fin n)

end
