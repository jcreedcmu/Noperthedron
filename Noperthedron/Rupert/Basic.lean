module

public import Noperthedron.EuclideanSpaceNotation
public import Noperthedron.MainTheorem

@[expose] public section


abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

end
