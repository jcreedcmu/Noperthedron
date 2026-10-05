module

public import Noperthedron.PentagonalHexecontahedron.CapBridge
public import Noperthedron.PentagonalHexecontahedron.HalfTurnPose

@[expose] public section

/-!
# The cap theorem (given per-chart goodness)

`cap_pose_not_rupert`: if every point of every chart of a cap is *good*
(`ChartGood`: an F_e point in the cone region, a point outside the half-turn
cell for the element g, or a support witness (v_k, c) with u × c ≠ 0 whose
witness values are ≥ 0 for every vertex), then no pose with view in the cap's
cone {|u·eᵢ| ≤ μ₀ u·x}, relative rotation cayley(w) with |w| ≤ wmax, and (when
the cap uses the half-turn prune) relative rotation in the half-turn cell, is
Rupert for the (scaled) solid. The certificate check (`CapCert`) establishes
`ChartGood` for every chart point.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly PVec
open scoped Matrix RealInnerProductSpace

/-- The real witness value of vertex v_j: N(w) v_k · d − D(w) (v_j · d), d = u × c. -/
noncomputable def witnessValue (u w vk c vj : Fin 3 → ℝ) : ℝ :=
  rdot (rcayleyNum w vk) (rcross u c) - (1 + rdot w w) * rdot vj (rcross u c)

/-- A chart point is good. -/
def ChartGood (st : Setup) (pr : Params) (V : List (Fin 3 → ℝ)) (usePrune : Bool)
    (G : Matrix (Fin 3) (Fin 3) ℝ) (id : ChartId) (y : Fin 5 → ℝ) : Prop :=
  (id.kind = .fe ∧ InConeRegion st pr (rES st id (st.frameAB id.side).1 (st.frameAB id.side).2 y).2) ∨
  (usePrune = true ∧ Matrix.trace (cayleyMatrix (rChartW st id y 0) (rChartW st id y 1) (rChartW st id y 2)) <
    Matrix.trace (halfTurnMat (rChartU st id y) *
      cayleyMatrix (rChartW st id y 0) (rChartW st id y 1) (rChartW st id y 2) * G)) ∨
  ∃ vk ∈ V, ∃ c : Fin 3 → ℝ, rcross (rChartU st id y) c ≠ 0 ∧
    ∀ vj ∈ V, 0 ≤ witnessValue (rChartU st id y) (rChartW st id y) vk c vj

/-- The Cayley rotation times its denominator is the numerator N(w). -/
theorem cayley_mulVec (w v : Fin 3 → ℝ) :
    (1 + rdot w w) • (cayleyMatrix (w 0) (w 1) (w 2)).mulVec v = rcayleyNum w v := by
  have hD : (1 + rdot w w) = cayleyDenom (w 0) (w 1) (w 2) := by
    simp [rdot, cayleyDenom]; ring
  have hne := cayleyDenom_ne (w 0) (w 1) (w 2)
  rw [cayleyMatrix_eq_div_numerator, hD]
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_three, rcayleyNum, rdot, rcross,
    Pi.add_apply, smul_eq_mul]
  fin_cases k <;> simp [cayleyNumeratorMatrix] <;> field_simp <;> ring

/-- A linear bound on a set bounds its convex hull. -/
theorem inner_le_of_mem_convexHull {T : Set ℝ³} (d : ℝ³) (M : ℝ) (hT : ∀ v ∈ T, ⟪d, v⟫ ≤ M) :
    ∀ v ∈ convexHull ℝ T, ⟪d, v⟫ ≤ M := by
  have hconv : Convex ℝ {v : ℝ³ | ⟪d, v⟫ ≤ M} := by
    have : {v : ℝ³ | ⟪d, v⟫ ≤ M} = {v : ℝ³ | (innerₛₗ ℝ d) v ≤ M} := rfl
    rw [this]
    exact convex_halfSpace_le (innerₛₗ ℝ d).isLinear M
  exact fun v hv => convexHull_min hT hconv hv

def toEuc (v : Fin 3 → ℝ) : ℝ³ := WithLp.toLp 2 v

theorem inner_toEuc (a b : Fin 3 → ℝ) : ⟪toEuc a, toEuc b⟫ = rdot a b := by
  rw [inner_euc3]; simp [toEuc, rdot]

theorem rdot_rcross_self (u c : Fin 3 → ℝ) : rdot u (rcross u c) = 0 := by
  simp [rdot, rcross]; ring

/-- **The cap theorem**, given that every chart point is good. -/
theorem cap_pose_not_rupert (st : Setup) (pr : Params) (zOf : Kind × ℕ × ℕ × Bool → ℕ) (hz : ∀ b, 0 < zOf b)
    (hF : FrameOK st) (hS : 2 ≤ st.strongScale) (ht0 : 0 ≤ (pr.t0 : ℝ))
    (wmax : ℝ) (hw0 : 0 ≤ wmax) (hw1 : wmax ≤ 2 * pr.mu0) (hw2 : wmax ≤ st.strongScale * (pr.mu0 : ℝ) ^ 2)
    (V : List (Fin 3 → ℝ)) (usePrune : Bool) (G : Matrix (Fin 3) (Fin 3) ℝ)
    (hgood : ∀ id ∈ chartList st pr zOf, ∀ y, InBoxR (rootBox st pr id) y → ChartGood st pr V usePrune G id y)
    (κ : ℝ) (hκ : 0 < κ) (S : Set ℝ³) (hSdef : S = convexHull ℝ {v | ∃ vj ∈ V, v = κ • toEuc vj})
    (hSsym : ∀ v ∈ S, -v ∈ S) (p : MatrixPose)
    (hx : 0 < rdot p.view (kv st.x))
    (he1 : |rdot p.view (kv st.e1)| ≤ pr.mu0 * rdot p.view (kv st.x))
    (he2 : |rdot p.view (kv st.e2)| ≤ pr.mu0 * rdot p.view (kv st.x))
    (w : Fin 3 → ℝ) (hR : p.relativeRotation = cayleyMatrix (w 0) (w 1) (w 2)) (hw : rdot w w ≤ wmax ^ 2)
    (hcell : usePrune = true →
      Matrix.trace (halfTurnMat p.view * p.relativeRotation * G) ≤ Matrix.trace p.relativeRotation) :
    ¬ RupertPose p S := by
  set u₀ := p.view
  set ξ := rdot u₀ (kv st.x)
  have hξ : ξ ≠ 0 := hx.ne'
  set t₁ := rdot u₀ (kv st.e1) / ξ
  set t₂ := rdot u₀ (kv st.e2) / ξ
  have ht₁ : |t₁| ≤ pr.mu0 := by
    simp only [t₁]; rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]; exact he1
  have ht₂ : |t₂| ≤ pr.mu0 := by
    simp only [t₂]; rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]; exact he2
  have hu : kv st.x + t₁ • kv st.e1 + t₂ • kv st.e2 = (1 / ξ) • u₀ := by
    have hd := decomp_orthonormal hF u₀
    conv_rhs => rw [hd]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, t₁, t₂, ξ]
    have hξ' : rdot u₀ (kv st.x) ≠ 0 := hξ
    field_simp
    ring
  obtain ⟨id, hid, y, hy, hU, hW, hFe⟩ :=
    cap_cover st pr zOf hz hF hS ht0 wmax hw0 hw1 hw2 t₁ t₂ ht₁ ht₂ w hw
  rw [hu] at hU
  rcases hgood id hid y hy with ⟨hfe, hcone⟩ | ⟨hp, htr⟩ | ⟨vk, hvk, c, hd, hwit⟩
  · exact absurd hcone (hFe hfe)
  · rw [hU, hW, halfTurnMat_smul (1 / ξ) (by positivity) u₀] at htr
    have : cayleyMatrix (w 0) (w 1) (w 2) = p.relativeRotation := hR.symm
    rw [this] at htr
    exact absurd (hcell hp) (not_le.mpr htr)
  · rw [hU] at hd
    rw [hU, hW] at hwit
    set u := (1 / ξ) • u₀
    set d := rcross u c
    have hD : 0 < 1 + rdot w w := by linarith [rdot_self_nonneg w]
    -- (R v_k)·d ≥ v_j·d for every vertex.
    have hRvk : ∀ vj ∈ V, rdot vj d ≤ rdot ((cayleyMatrix (w 0) (w 1) (w 2)).mulVec vk) d := by
      intro vj hvj
      have h := hwit vj hvj
      unfold witnessValue at h
      rw [← cayley_mulVec] at h
      have : rdot ((1 + rdot w w) • (cayleyMatrix (w 0) (w 1) (w 2)).mulVec vk) d =
          (1 + rdot w w) * rdot ((cayleyMatrix (w 0) (w 1) (w 2)).mulVec vk) d := by
        simp only [rdot, Pi.smul_apply, smul_eq_mul]; ring
      rw [this] at h
      nlinarith
    set M := κ * rdot ((cayleyMatrix (w 0) (w 1) (w 2)).mulVec vk) d
    apply not_rupert_of_support p S hSsym (toEuc d) ?_ ?_ M ?_ (κ • toEuc vk) ?_ ?_
    · intro h0
      apply hd
      have := congrArg (WithLp.ofLp) h0
      simpa [toEuc] using this
    · -- (O d)_z = u₀ · d = ξ (u · d) = 0.
      have h2 : (p.outerRot.val.toEuclideanLin (toEuc d)) 2 = rdot u₀ d := by
        simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, toEuc, rdot, u₀,
          MatrixPose.view]
      rw [h2]
      have hud : rdot u d = 0 := rdot_rcross_self u c
      have : rdot u₀ d = ξ * rdot u d := by
        simp only [u, rdot, Pi.smul_apply, smul_eq_mul]; field_simp
      rw [this, hud, mul_zero]
    · rw [hSdef]
      apply inner_le_of_mem_convexHull
      rintro v ⟨vj, hvj, rfl⟩
      rw [inner_smul_right, inner_toEuc]
      have := hRvk vj hvj
      rw [show rdot d vj = rdot vj d by simp only [rdot]; ring]
      exact mul_le_mul_of_nonneg_left this hκ.le
    · rw [hSdef]
      exact subset_convexHull ℝ _ ⟨vk, hvk, rfl⟩
    · rw [hR]
      simp only [map_smul, inner_smul_right, M]
      apply le_of_eq
      congr 1
      have : (cayleyMatrix (w 0) (w 1) (w 2)).toEuclideanLin (toEuc vk) =
          toEuc ((cayleyMatrix (w 0) (w 1) (w 2)).mulVec vk) := by
        simp [Matrix.toLpLin_apply, toEuc]
      rw [this, inner_toEuc]
      simp only [rdot]; ring

end Noperthedron.PentagonalHexecontahedron.Cap
