import Noperthedron.Checker.KappaApprox
import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.SolutionTable.Basic
import Noperthedron.Vertices.Exact

namespace Noperthedron.Solution

theorem valid_global_imp_no_rupert (tab : Table) (row : Row)
    (hr : row.ValidGlobal tab) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q exactShape.hull := by
  let iv := row.toPoseInterval
  let pbar := iv.center
  let ε := iv.radius
  have hε : 0 ≤ ε := by sorry
  rintro ⟨q, hqi, hqr⟩
  have hq := q ∈ pbar.closed_ball ε
  have hrg := RationalApprox.GlobalTheorem.rational_global
                 pbar ε hε exactPoly pythonPoly
                 KappaApprox.exact_κApprox_python exactPoly_point_symmetric
  have hqε : q ∈ pbar.closed_ball ε := sorry
  have pc : RationalApprox.GlobalTheorem.RationalGlobalTheoremPrecondition
             exactPoly pythonPoly KappaApprox.exact_κApprox_python pbar ε := sorry
  replace hqr : RupertPose q exactPoly.hull := by
    sorry
  specialize hrg pc
  push Not at hrg
  exact hrg q hqε hqr
