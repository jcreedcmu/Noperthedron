module

public import Noperthedron.PentagonalHexecontahedron.CapCover

@[expose] public section

/-!
# Frame coordinates of the cap charts

For an orthonormal frame (x, e₁, e₂) every vector is the sum of its frame
components (`decomp_orthonormal`); for a ⊥ x, a ≠ 0, every w is
α (x × a) + β a + γ x with α = w·(x×a)/|a|², β = w·a/|a|², γ = w·x
(`decomp_aniso`). These are the Cayley coordinates of the isotropic (u0) and
anisotropic (ux) charts.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open PVec

/-- Three vectors are orthonormal. -/
def Orthonormal3 (a b c : Fin 3 → ℝ) : Prop :=
  rdot a a = 1 ∧ rdot b b = 1 ∧ rdot c c = 1 ∧ rdot a b = 0 ∧ rdot a c = 0 ∧ rdot b c = 0

theorem rdot_comm (a b : Fin 3 → ℝ) : rdot a b = rdot b a := by simp only [rdot]; ring

theorem decomp_orthonormal {a b c : Fin 3 → ℝ} (h : Orthonormal3 a b c) (w : Fin 3 → ℝ) :
    w = rdot w a • a + rdot w b • b + rdot w c • c := by
  obtain ⟨haa, hbb, hcc, hab, hac, hbc⟩ := h
  -- F (rows a, b, c) is orthogonal: F Fᵀ = 1, hence Fᵀ F = 1.
  let F : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![a, b, c]
  have hFF : F * F.transpose = 1 := by
    ext i j
    simp only [rdot] at haa hbb hcc hab hac hbc
    fin_cases i <;> fin_cases j <;>
      simp [F, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> linarith
  have hFtF : F.transpose * F = 1 := Matrix.mul_eq_one_comm.mp hFF
  funext k
  have hk := congrFun (congrFun hFtF k)
  simp only [rdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e0 := hk 0
  have e1 := hk 1
  have e2 := hk 2
  simp [F, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at e0 e1 e2
  fin_cases k <;> simp at e0 e1 e2 ⊢ <;> linear_combination -(w 0) * e0 - w 1 * e1 - w 2 * e2

theorem rdot_rcross_self_left (a b : Fin 3 → ℝ) : rdot (rcross a b) a = 0 := by
  simp [rdot, rcross]; ring

theorem rdot_rcross_self_right (a b : Fin 3 → ℝ) : rdot (rcross a b) b = 0 := by
  simp [rdot, rcross]; ring

theorem rdot_rcross_rcross (x a : Fin 3 → ℝ) :
    rdot (rcross x a) (rcross x a) = rdot x x * rdot a a - rdot x a ^ 2 := by
  simp [rdot, rcross]; ring

theorem decomp_aniso {x a : Fin 3 → ℝ} (hx : rdot x x = 1) (hxa : rdot x a = 0) (ha : 0 < rdot a a)
    (w : Fin 3 → ℝ) :
    w = (rdot w (rcross x a) / rdot a a) • rcross x a + (rdot w a / rdot a a) • a + rdot w x • x := by
  set n := Real.sqrt (rdot a a)
  have hn : 0 < n := Real.sqrt_pos.mpr ha
  have hn2 : n ^ 2 = rdot a a := Real.sq_sqrt ha.le
  have hsm : ∀ (k : ℝ) (u v : Fin 3 → ℝ), rdot (k • u) v = k * rdot u v := by
    intro k u v; simp only [rdot, Pi.smul_apply, smul_eq_mul]; ring
  have hsm' : ∀ (k : ℝ) (u v : Fin 3 → ℝ), rdot u (k • v) = k * rdot u v := by
    intro k u v; simp only [rdot, Pi.smul_apply, smul_eq_mul]; ring
  have hcc : rdot (rcross x a) (rcross x a) = rdot a a := by
    rw [rdot_rcross_rcross, hx, hxa]; ring
  have hnne : n ≠ 0 := hn.ne'
  have hon : Orthonormal3 ((1 / n) • rcross x a) ((1 / n) • a) x := by
    refine ⟨?_, ?_, hx, ?_, ?_, ?_⟩
    · rw [hsm, hsm', hcc, ← hn2]; field_simp
    · rw [hsm, hsm', ← hn2]; field_simp
    · rw [hsm, hsm', rdot_rcross_self_right]; ring
    · rw [hsm, rdot_rcross_self_left]; ring
    · rw [hsm, rdot_comm, hxa]; ring
  have h := decomp_orthonormal hon w
  conv_lhs => rw [h]
  funext k
  have hk : ∀ u : Fin 3 → ℝ, rdot w ((1 / n) • u) * ((1 / n) * u k) = rdot w u / rdot a a * u k := by
    intro u
    rw [hsm', ← hn2]
    field_simp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk]

/-- Bounds of the weighted coordinates by |w|. -/
theorem abs_rdot_le_of_unit {e : Fin 3 → ℝ} (he : rdot e e = 1) (w : Fin 3 → ℝ) :
    |rdot w e| ≤ Real.sqrt (rdot w w) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have := congrArg id he
  simp only [rdot] at he ⊢
  nlinarith [sq_nonneg (w 0 * e 1 - w 1 * e 0), sq_nonneg (w 0 * e 2 - w 2 * e 0),
    sq_nonneg (w 1 * e 2 - w 2 * e 1)]

end Noperthedron.PentagonalHexecontahedron.Cap
