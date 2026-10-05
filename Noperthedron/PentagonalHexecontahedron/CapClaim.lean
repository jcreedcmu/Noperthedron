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

/-- The image of a frame vector under g (and a sign). -/
noncomputable def imgVec (g : IcoIndex) (sgn : Bool) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (if sgn then (1 : ℝ) else -1) • (icoMatrix g).mulVec v

theorem rdot_transpose_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    rdot (Mᵀ.mulVec u) v = rdot u (M.mulVec v) := by
  simp [rdot, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]; ring

theorem relativeRotation_viewAntipode (p : MatrixPose) : p.viewAntipode.relativeRotation = p.relativeRotation := by
  have hR := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp MatrixPose.viewAntipodeRotation.property.1
  simp only [MatrixPose.relativeRotation, MatrixPose.viewAntipode]
  show (MatrixPose.viewAntipodeRotation.val * p.outerRot.val)ᵀ * (MatrixPose.viewAntipodeRotation.val * p.innerRot.val) = _
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ MatrixPose.viewAntipodeRotation.val, hR,
    Matrix.one_mul]

theorem halfTurnMat_neg (u : Fin 3 → ℝ) : halfTurnMat (-u) = halfTurnMat u := by
  have := halfTurnMat_smul (-1) (by norm_num) u
  simpa using this

theorem halfTurnMat_view_bothRightIco (p : MatrixPose) (g : IcoIndex) :
    halfTurnMat (p.bothRightIco g).view = (icoMatrix g)ᵀ * halfTurnMat p.view * icoMatrix g := by
  rw [halfTurnMat_view, halfTurnMat_view]
  simp only [MatrixPose.bothRightIco, icoSO3]
  show (p.outerRot.val * icoMatrix g)ᵀ * halfTurnZMat * (p.outerRot.val * icoMatrix g) = _
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem relativeRotation_bothRightIco (p : MatrixPose) (g : IcoIndex) :
    (p.bothRightIco g).relativeRotation = (icoMatrix g)ᵀ * p.relativeRotation * icoMatrix g := by
  simp only [MatrixPose.relativeRotation, MatrixPose.bothRightIco, icoSO3]
  show (p.outerRot.val * icoMatrix g)ᵀ * (p.innerRot.val * icoMatrix g) = _
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem view_viewAntipode' (p : MatrixPose) : p.viewAntipode.view = -p.view := view_viewAntipode p

/-- **Images of a cap.** The claim for the frame (x, e₁, e₂) gives the claim for (s g x, s g e₁, s g e₂),
with the half-turn condition for g G gᵀ. -/
theorem CapClaim.image (P : IModel) {x e1 e2 : Fin 3 → ℝ} {mu0 τ : ℝ} {G : Option (Matrix (Fin 3) (Fin 3) ℝ)}
    (h : CapClaim P.toC5.polyhedron.hull x e1 e2 mu0 τ G) (g : IcoIndex) (sgn : Bool) :
    CapClaim P.toC5.polyhedron.hull (imgVec g sgn x) (imgVec g sgn e1) (imgVec g sgn e2) mu0 τ
      (G.map fun G₀ => icoMatrix g * G₀ * (icoMatrix g)ᵀ) := by
  intro p hx he1 he2 htr hcell
  -- p₁: the view turned to s u; p₂: conjugated by g.
  let p₁ := if sgn then p else p.viewAntipode
  have hv₁ : p₁.view = (if sgn then (1 : ℝ) else -1) • p.view := by
    cases sgn
    · simp [p₁, view_viewAntipode]
    · simp [p₁]
  have hR₁ : p₁.relativeRotation = p.relativeRotation := by
    cases sgn
    · simp [p₁, relativeRotation_viewAntipode]
    · simp [p₁]
  have hrup₁ : RupertPose p₁ P.toC5.polyhedron.hull ↔ RupertPose p P.toC5.polyhedron.hull := by
    cases sgn
    · simp only [p₁, Bool.false_eq_true, if_false]; exact MatrixPose.RupertPose_viewAntipode_iff p _
    · simp [p₁]
  let p₂ := p₁.bothRightIco g
  have hv₂ : p₂.view = (icoMatrix g)ᵀ.mulVec p₁.view := by
    rw [view_bothRightIco]; simp [viewCandidate]
  have hdot : ∀ v : Fin 3 → ℝ, rdot p₂.view v = rdot p.view (imgVec g sgn v) := by
    intro v
    rw [hv₂, rdot_transpose_mulVec, hv₁]
    simp only [imgVec, rdot, Pi.smul_apply, smul_eq_mul]
    ring
  have hR₂ : p₂.relativeRotation = (icoMatrix g)ᵀ * p.relativeRotation * icoMatrix g := by
    rw [relativeRotation_bothRightIco, hR₁]
  have horth := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp (icoMatrix_mem_SO3 g).1
  have horth' := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp (icoMatrix_mem_SO3 g).1
  have htr₂ : Matrix.trace p₂.relativeRotation = Matrix.trace p.relativeRotation := by
    rw [hR₂, Matrix.trace_mul_comm, ← Matrix.mul_assoc, horth, Matrix.one_mul]
  intro hrup
  apply h p₂ (by rw [hdot]; exact hx) (by rw [hdot, hdot]; exact he1) (by rw [hdot, hdot]; exact he2)
    (by rw [htr₂]; exact htr)
  · intro G₀ hG₀
    have hc := hcell (icoMatrix g * G₀ * (icoMatrix g)ᵀ) (by rw [hG₀]; rfl)
    have hH : halfTurnMat p₂.view = (icoMatrix g)ᵀ * halfTurnMat p₁.view * icoMatrix g :=
      halfTurnMat_view_bothRightIco p₁ g
    have hH₁ : halfTurnMat p₁.view = halfTurnMat p.view := by
      rw [hv₁]; cases sgn
      · simp only [Bool.false_eq_true, if_false]; rw [halfTurnMat_smul (-1) (by norm_num)]
      · simp
    have htrc : Matrix.trace ((icoMatrix g)ᵀ * p.relativeRotation * icoMatrix g) = Matrix.trace p.relativeRotation := by
      rw [← hR₂]; exact htr₂
    rw [hH, hH₁, hR₂, htrc]
    calc Matrix.trace ((icoMatrix g)ᵀ * halfTurnMat p.view * icoMatrix g *
          ((icoMatrix g)ᵀ * p.relativeRotation * icoMatrix g) * G₀)
        = Matrix.trace (halfTurnMat p.view * p.relativeRotation * (icoMatrix g * G₀ * (icoMatrix g)ᵀ)) := by
          rw [show (icoMatrix g)ᵀ * halfTurnMat p.view * icoMatrix g *
              ((icoMatrix g)ᵀ * p.relativeRotation * icoMatrix g) * G₀ =
              (icoMatrix g)ᵀ * (halfTurnMat p.view * p.relativeRotation * (icoMatrix g * G₀)) by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (icoMatrix g) (icoMatrix g)ᵀ, horth, Matrix.one_mul]]
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ ≤ _ := hc
  · exact (hrup₁.mpr (by
      have := (P.RupertPose_bothRightIco_iff p₁ g).mpr
      exact hrup)) |> fun h' => by
        exact (P.RupertPose_bothRightIco_iff p₁ g).mpr (hrup₁.mpr hrup)

end Noperthedron.PentagonalHexecontahedron.Cap
