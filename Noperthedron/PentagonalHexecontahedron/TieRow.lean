module

public import Noperthedron.PentagonalHexecontahedron.AtlasTiePrune
public import Noperthedron.PentagonalHexecontahedron.HalfTurnPose

@[expose] public section

/-!
# Tie leaves of the solution tree

`TieClaimT S x T ρ`: no pose whose view is a positive multiple of a point of the
triangle T and whose rotation S = H_u R H_x has trace ≥ τ(ρ) is Rupert (the
triangle form of `TieClaim`). `TiesHold S`: every tie node of `dhTieNodes` has
its claim (proved for the exact solid from the tie certificates, DHTies.lean).

`tieLeaf_sound`: a tie leaf (a valid `AtlasTiePrune.Box` over a view triangle
inside a tie node's triangle, with radius at most the node's) has no Rupert
pose.
-/

namespace Noperthedron.PentagonalHexecontahedron.Tie

open Noperthedron.Atlas
open Noperthedron.Atlas.ProjectiveView (InTriangle toReal affinePoint)
open CayleyAtlas Cap NPoly PVec
open scoped Matrix

def TieClaimT (S : Set ℝ³) (x : Fin 3 → ℝ) (T : Triangle) (ρ : ℚ) : Prop :=
  ∀ (p : MatrixPose) (κ : ℝ) (pt : Fin 3 → ℝ), 0 < κ → InTriangle (toReal T) pt → p.view = κ • pt →
    ((AtlasTiePrune.tau ρ : ℚ) : ℝ) ≤ Matrix.trace (halfTurnMat p.view * p.relativeRotation * halfTurnMat x) →
    ¬ RupertPose p S

theorem viewOf_eq_affinePoint (T : Triangle) (w : Fin 3 → ℝ) :
    viewOf T w = affinePoint (toReal T) w := by
  funext k
  simp [viewOf, affinePoint, toReal, Fin.sum_univ_three, mul_comm]

theorem tieClaimT_of_tieClaim {S : Set ℝ³} {x : Fin 3 → ℝ} {T : Triangle} {ρ : ℚ} (h : TieClaim S x T ρ) :
    TieClaimT S x T ρ := by
  intro p κ pt hκ hin hview htr
  obtain ⟨w, hw0, -, hpt⟩ := hin
  apply h p κ w hκ hw0 (by rw [hview, hpt, viewOf_eq_affinePoint])
  have : ((AtlasTiePrune.tau ρ : ℚ) : ℝ) = (3 - (ρ : ℝ) ^ 2) / (1 + (ρ : ℝ) ^ 2) := by
    simp [AtlasTiePrune.tau]
  rw [← this]; exact htr

theorem tau_anti {ρ ρ' : ℚ} (h0 : 0 ≤ ρ') (hle : ρ' ≤ ρ) : AtlasTiePrune.tau ρ ≤ AtlasTiePrune.tau ρ' := by
  unfold AtlasTiePrune.tau
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hle hle h0 (le_trans h0 hle)]

/-- The claims of all tie nodes. -/
def TiesHold (S : Set ℝ³) : Prop :=
  ∀ (k : ℕ) (e : TieNode), dhTieNodes[k]? = some e → TieClaimT S (kv (AtlasTiePrune.tieXK e.normal)) e.tri e.rho

/-- **Tie leaves are sound**, given the claim of a node whose triangle contains the leaf's. -/
theorem tieLeaf_sound (S : Set ℝ³) (box : AtlasTiePrune.Box) (hvalid : box.Valid)
    (T' : Triangle) (ρ' : ℚ) (hclaim : TieClaimT S (kv (AtlasTiePrune.tieXK box.normal)) T' ρ')
    (hρ0 : 0 ≤ box.rho) (hρ : box.rho ≤ ρ')
    (hsub : ∀ pt, InTriangle (toReal box.triangle) pt → InTriangle (toReal T') pt)
    (root : Fin 8) (p : AtlasPose ℝ) (hp : p ∈ box.interval.toReal) (hbounded : p.CayleyBounded)
    (hscale : 1 ≤ AtlasProjectiveView.viewScale root p)
    (htri : InTriangle (toReal box.triangle) (AtlasProjectiveView.normalizedView root p)) (offset : ℝ²) :
    ¬ RupertPose (p.matrixPoseWithOffset box.chart offset) S := by
  set pose := p.matrixPoseWithOffset box.chart offset
  obtain ⟨w, hw0, hw1, hwT⟩ := htri
  set κ := AtlasProjectiveView.viewScale root p
  have hκ : 0 < κ := by linarith
  have hview : pose.view = κ • AtlasProjectiveView.normalizedView root p := by
    funext k
    simp only [pose, MatrixPose.view, AtlasPose.matrixPoseWithOffset_outerRot_val, rotRM_mat_row2, Pi.smul_apply,
      smul_eq_mul, AtlasProjectiveView.normalizedView]
    have : eulerView p.θ p.φ k = AtlasEdgeCertificate.viewVector p k := by
      fin_cases k <;> simp [eulerView, AtlasEdgeCertificate.viewVector]
    rw [this, mul_div_cancel₀ _ hκ.ne']
  have hpt : AtlasProjectiveView.normalizedView root p = viewOf box.triangle w := by
    rw [hwT, viewOf_eq_affinePoint]
  have htr := box.valid_imp_trace hvalid hp hbounded w hw0 (by rw [hw1]; norm_num)
  have hR : pose.relativeRotation = chartMatrix box.chart * cayleyMatrix p.x p.y p.z :=
    AtlasPose.matrixPoseWithOffset_relativeRotation box.chart p offset
  apply hclaim pose κ _ hκ (hsub _ ⟨w, hw0, hw1, hwT⟩) hview
  rw [hR, hview, halfTurnMat_smul κ hκ.ne', hpt]
  have hτ : ((AtlasTiePrune.tau ρ' : ℚ) : ℝ) ≤ (AtlasTiePrune.tau box.rho : ℝ) := by
    exact_mod_cast tau_anti hρ0 hρ
  exact le_trans hτ htr.le

end Noperthedron.PentagonalHexecontahedron.Tie
