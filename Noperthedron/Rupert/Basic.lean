import Noperthedron.EuclideanSpaceNotation
import Noperthedron.MainTheorem

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ
