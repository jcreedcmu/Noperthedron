import Noperthedron.Checker.KappaApprox
import Noperthedron.RationalApprox.RationalGlobal
import Noperthedron.SolutionTable.Basic
import Noperthedron.Vertices.Exact

namespace Noperthedron.Solution

theorem valid_global_imp_no_rupert (tab : Table) (row : Row)
    (hrow : row.ValidGlobal tab) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q exactPolyhedron.hull := by
  let iv := row.toPoseInterval
  let pbar := iv.center
  let r := iv.radius
  rintro ⟨q, hqi, hqr⟩
  have hqε : q ∈ pbar.closed_ball r := mem_closed_ball_center_of_mem iv q hqi
  have hr : 0 ≤ r := nonempty_closed_ball_radius_nonneg q pbar r hqε
  have hrg := RationalApprox.GlobalTheorem.rational_global
                 pbar r hr exactPoly pythonPoly
                 KappaApprox.exact_κApprox_python exactPoly_point_symmetric
  have pc : RationalApprox.GlobalTheorem.RationalGlobalTheoremPrecondition
             exactPoly pythonPoly KappaApprox.exact_κApprox_python pbar r := sorry
  specialize hrg pc
  push Not at hrg
  exact hrg q hqε hqr
