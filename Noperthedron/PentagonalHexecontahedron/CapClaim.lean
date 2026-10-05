module

public import Noperthedron.PentagonalHexecontahedron.CapCert

@[expose] public section

/-!
# Cap claims

`CapClaim S x e₁ e₂ μ₀ τ G`: no pose of S is Rupert whose view u has
u·x > 0, |u·eᵢ| ≤ μ₀ u·x, whose relative rotation has trace ≥ τ, and (if G
is given) whose relative rotation R satisfies tr(H_u R G) ≤ tr R. The trace
bound replaces the Cayley ball |w| ≤ wmax (tr cayley(w) = (3 − |w|²)/(1 + |w|²)),
so the claim is invariant under conjugation (`CapClaim.image`).

`CapCert.claim`: a checked certificate proves the claim of its cap with
τ = (3 − wmax²)/(1 + wmax²).
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec
open scoped Matrix

def CapClaim (S : Set ℝ³) (x e1 e2 : Fin 3 → ℝ) (mu0 τ : ℝ) (G : Option (Matrix (Fin 3) (Fin 3) ℝ)) : Prop :=
  ∀ p : MatrixPose, 0 < rdot p.view x → |rdot p.view e1| ≤ mu0 * rdot p.view x →
    |rdot p.view e2| ≤ mu0 * rdot p.view x → τ ≤ Matrix.trace p.relativeRotation →
    (∀ G₀, G = some G₀ → Matrix.trace (halfTurnMat p.view * p.relativeRotation * G₀) ≤
      Matrix.trace p.relativeRotation) →
    ¬ RupertPose p S

theorem rdot_cayley_bound {w : Fin 3 → ℝ} {wmax : ℝ} (hw0 : 0 ≤ wmax)
    (h : (3 - wmax ^ 2) / (1 + wmax ^ 2) ≤ Matrix.trace (cayleyMatrix (w 0) (w 1) (w 2))) :
    rdot w w ≤ wmax ^ 2 := by
  rw [trace_cayleyMatrix] at h
  have hD : 0 < cayleyDenom (w 0) (w 1) (w 2) := cayleyDenom_pos _ _ _
  have hD2 : (0 : ℝ) < 1 + wmax ^ 2 := by positivity
  rw [div_le_div_iff₀ hD2 hD] at h
  simp only [cayleyDenom] at h
  simp only [rdot]
  nlinarith

theorem CapCert.claim (c : CapCert) (hc : c.check = true) (hS : 2 ≤ c.st.strongScale)
    (ht0 : 0 ≤ (c.pr.t0 : ℝ)) (wmax : ℝ) (hw0 : 0 ≤ wmax) (hw3 : wmax ^ 2 ≤ 3) (hw1 : wmax ≤ 2 * c.pr.mu0)
    (hw2 : wmax ≤ c.st.strongScale * (c.pr.mu0 : ℝ) ^ 2)
    (κ : ℝ) (hκ : 0 < κ) (S : Set ℝ³) (hSdef : S = convexHull ℝ {v | ∃ vj ∈ c.verts.toList.map kv, v = κ • toEuc vj})
    (hSsym : ∀ v ∈ S, -v ∈ S) :
    CapClaim S (kv c.st.x) (kv c.st.e1) (kv c.st.e2) c.pr.mu0 ((3 - wmax ^ 2) / (1 + wmax ^ 2))
      (if c.usePrune then some (gMat c.Gcol) else none) := by
  intro p hx he1 he2 htr hcell
  have hτ : 0 ≤ (3 - wmax ^ 2) / (1 + wmax ^ 2) := div_nonneg (by linarith) (by positivity)
  obtain ⟨wx, wy, wz, -, hR⟩ := Noperthedron.exists_cayleyMatrix_of_trace_nonneg p.relativeRotation
    (Noperthedron.Atlas.MatrixPose.relativeRotation_mem_SO3 p) (le_trans hτ htr)
  let w : Fin 3 → ℝ := ![wx, wy, wz]
  have hRw : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2) := hR
  apply c.not_rupert hc hS ht0 wmax hw0 hw1 hw2 κ hκ S hSdef hSsym p hx he1 he2 w hRw
  · apply rdot_cayley_bound hw0
    rw [← hRw]; exact htr
  · intro hp
    exact hcell (gMat c.Gcol) (by simp [hp])

end Noperthedron.PentagonalHexecontahedron.Cap
