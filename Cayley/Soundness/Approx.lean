module

public import Cayley.Soundness.Pose
public import Cayley.Soundness.QIReal
public import Cayley.Soundness.TrigTable

@[expose] public section

/-!
# The checker's approximate data

The checker's vertex table is within `ε = 2⁻⁶⁰` of the true vertices, its symmetry
table within `ε` of the true rotations, and `τ` permutes the `C3` copies exactly as
`tauPair` says.
-/

namespace Cayley

open Noperthedron Real
open scoped Matrix

/-- The vertex with checker index `t = 6k + 3ℓ + i`. -/
def vIdx (t : ℕ) : VertexIndex :=
  ⟨⟨t / 6 % 15, Nat.mod_lt _ (by norm_num)⟩, ⟨t % 6 / 3, by omega⟩, ⟨t % 3, Nat.mod_lt _ (by norm_num)⟩⟩

/-- The true vertex with checker index `t`. -/
noncomputable def vtx (t : ℕ) : Fin 3 → ℝ := (exactVertex (vIdx t)).ofLp

theorem vIdx_surj (T : VertexIndex) : ∃ t < 90, vIdx t = T := by
  refine ⟨6 * T.k.val + 3 * T.ℓ.val + T.i.val, by omega, ?_⟩
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩, ⟨i, hi⟩⟩ := T
  simp only [vIdx, VertexIndex.mk.injEq, Fin.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Products of approximations. -/
theorem rot_err {c s ch sh x y xh yh e e' : ℝ} (hc : |c - ch| ≤ e) (hs : |s - sh| ≤ e)
    (hx : |x - xh| ≤ e') (hy : |y - yh| ≤ e') (hcb : |c| ≤ 1) (hsb : |s| ≤ 1)
    (hxb : |xh| ≤ 1) (hyb : |yh| ≤ 1) :
    |(c * x - s * y) - (ch * xh - sh * yh)| ≤ 2 * (e + e') ∧
      |(s * x + c * y) - (sh * xh + ch * yh)| ≤ 2 * (e + e') := by
  have key : ∀ a b ah bh : ℝ, |a - ah| ≤ e → |b - bh| ≤ e' → |a| ≤ 1 → |bh| ≤ 1 →
      |a * b - ah * bh| ≤ e + e' := by
    intro a b ah bh ha hb ha1 hb1
    have he : 0 ≤ e := le_trans (abs_nonneg _) ha
    have : a * b - ah * bh = a * (b - bh) + (a - ah) * bh := by ring
    rw [this]
    calc |a * (b - bh) + (a - ah) * bh| ≤ |a| * |b - bh| + |a - ah| * |bh| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * e' + e * 1 := by gcongr
      _ = e + e' := by ring
  have h1 := key c x ch xh hc hx hcb hxb
  have h2 := key s y sh yh hs hy hsb hyb
  have h3 := key s x sh xh hs hx hsb hxb
  have h4 := key c y ch yh hc hy hcb hyb
  constructor
  · have : (c * x - s * y) - (ch * xh - sh * yh) = (c * x - ch * xh) - (s * y - sh * yh) := by ring
    rw [this]; calc _ ≤ |c * x - ch * xh| + |s * y - sh * yh| := abs_sub _ _
      _ ≤ _ := by linarith
  · have : (s * x + c * y) - (sh * xh + ch * yh) = (s * x - sh * xh) + (c * y - ch * yh) := by ring
    rw [this]; calc _ ≤ |s * x - sh * xh| + |c * y - ch * yh| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem cTab_err (i : ℕ) (hi : i < 3) :
    |Cpt ⟨i, hi⟩ 0 - D (cTab[i]!).x| ≤ 1 / 2 ^ 80 ∧ |Cpt ⟨i, hi⟩ 1 - D (cTab[i]!).y| ≤ 1 / 2 ^ 80 ∧
    |Cpt ⟨i, hi⟩ 2 - D (cTab[i]!).z| ≤ 1 / 2 ^ 80 ∧ |D (cTab[i]!).x| ≤ 1 ∧ |D (cTab[i]!).y| ≤ 1 := by
  interval_cases i <;>
    simp [Cpt, C1R, C2R, C3R, C1, C2, C3, cTab, D_d80, abs_le] <;> norm_num

theorem vertex_approx (t : ℕ) (ht : t < 90) (i : Fin 3) :
    |vtx t i - (vertexTab[t]!).toR i| ≤ D errε := by
  have hε : D errε = 1 / 2 ^ 60 := D_errε
  rw [hε]
  set k := t / 6
  set l := t % 6 / 3
  set ci := t % 3
  have hk : k < 15 := by omega
  have hl : l < 2 := by omega
  have hci : ci < 3 := by omega
  have hidx : vIdx t = ⟨⟨k, hk⟩, ⟨l, hl⟩, ⟨ci, hci⟩⟩ := by
    simp only [vIdx, VertexIndex.mk.injEq, Fin.mk.injEq]; omega
  have htab : vertexTab[t]! = vertexOf k l ci := by simp [vertexTab, getElem!_pos, ht, k, l, ci]
  have hcos := cos_tab_err k hk
  have hsin := sin_tab_err k hk
  have hcb : |cos (2 * π * k / 15)| ≤ 1 := abs_cos_le_one _
  have hsb : |sin (2 * π * k / 15)| ≤ 1 := abs_sin_le_one _
  obtain ⟨h0, h1, h2, hb0, hb1⟩ := cTab_err ci hci
  obtain ⟨r1, r2⟩ := rot_err hcos hsin h0 h1 hcb hsb hb0 hb1
  have hsmall : 2 * (1 / 2 ^ 71 + 1 / 2 ^ 80 : ℝ) ≤ 1 / 2 ^ 60 := by norm_num
  have hsmall' : (1 / 2 ^ 80 : ℝ) ≤ 1 / 2 ^ 60 := by norm_num
  unfold vtx
  rw [hidx, exactVertex_eq_vec, htab]
  simp only [vertexOf]
  have hl01 : l = 0 ∨ l = 1 := by omega
  rcases hl01 with h | h
  · simp only [h, ite_true, pow_zero, one_smul]
    fin_cases i <;> simp [V3.toR]
    all_goals (rw [← one_div]; linarith)
  · simp only [h, show (1 : ℕ) ≠ 0 by decide, ite_false, pow_one]
    fin_cases i <;> simp [V3.toR]
    all_goals rw [← one_div]
    all_goals (rw [abs_le] at r1 r2 h2 ⊢; constructor <;> linarith [r1.1, r1.2, r2.1, r2.2, h2.1, h2.2])

theorem cos_sin_reflect (k : ℕ) (hk : k < 15) :
    cos (2 * π * ((15 - k) % 15 : ℕ) / 15) = cos (2 * π * k / 15) ∧
      sin (2 * π * ((15 - k) % 15 : ℕ) / 15) = -sin (2 * π * k / 15) := by
  by_cases hk0 : k = 0
  · subst hk0; simp
  · have : (15 - k) % 15 = 15 - k := Nat.mod_eq_of_lt (by omega)
    rw [this, Nat.cast_sub (by omega)]
    have e : 2 * π * ((15 : ℕ) - (k : ℝ)) / 15 = 2 * π - 2 * π * k / 15 := by push_cast; ring
    rw [e, cos_two_pi_sub, sin_two_pi_sub]
    exact ⟨rfl, rfl⟩

theorem tau_pair (s t : ℕ) (hs : s < 90) (h : tauPair s = some t) :
    vtx t = tauR *ᵥ vtx s := by
  unfold tauPair at h
  split_ifs at h with h3
  cases h
  set k := s / 6
  set l := s % 6 / 3
  have hk : k < 15 := by omega
  have hl : l < 2 := by omega
  set k' := (15 - k) % 15
  have hk' : k' < 15 := Nat.mod_lt _ (by norm_num)
  have hidx : vIdx s = ⟨⟨k, hk⟩, ⟨l, hl⟩, ⟨2, by norm_num⟩⟩ := by
    simp only [vIdx, VertexIndex.mk.injEq, Fin.mk.injEq]; omega
  have hidx' : vIdx (6 * k' + 3 * (1 - l) + 2) = ⟨⟨k', hk'⟩, ⟨1 - l, by omega⟩, ⟨2, by norm_num⟩⟩ := by
    simp only [vIdx, VertexIndex.mk.injEq, Fin.mk.injEq]; omega
  obtain ⟨hc, hsn⟩ := cos_sin_reflect k hk
  unfold vtx
  rw [hidx, hidx', exactVertex_eq_vec, exactVertex_eq_vec]
  simp only
  rw [hc, hsn]
  have hC : Cpt 2 = WithLp.toLp 2 (fun i => ((![c3xR / 10 ^ 10, c3yR / 10 ^ 10, 1230614493 / 10 ^ 10] : Fin 3 → ℝ) i)) := by
    ext i; fin_cases i <;> simp [Cpt, C3R, C3, c3xR, c3yR] <;> norm_num
  have hk2 : kapR ≠ 0 := by unfold kapR c3xR c3yR; norm_num
  have hl01 : l = 0 ∨ l = 1 := by omega
  rcases hl01 with hl0 | hl1
  · simp only [hl0, show 1 - 0 = 1 from rfl]
    ext i; fin_cases i <;>
      simp [hC, tauR, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> field_simp <;>
      unfold kapR <;> ring
  · simp only [hl1, show 1 - 1 = 0 from rfl]
    ext i; fin_cases i <;>
      simp [hC, tauR, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> field_simp <;>
      unfold kapR <;> ring

theorem group_approx (g : ℕ) (hg : g < 15) (i k : Fin 3) :
    |gR g i k - (groupTab[g]!).toR i k| ≤ D errε := by
  have hε : D errε = 1 / 2 ^ 60 := D_errε
  have htab : groupTab[g]! = ⟨cosTab[g]!, -sinTab[g]!, 0, sinTab[g]!, cosTab[g]!, 0, 0, 0, 1⟩ := by
    simp [groupTab, getElem!_pos, hg]
  have hcos := cos_tab_err g hg
  have hsin := sin_tab_err g hg
  have hs : (1 / 2 ^ 71 : ℝ) ≤ 1 / 2 ^ 60 := by norm_num
  rw [hε, htab]
  fin_cases i <;> fin_cases k <;> simp [gR, Rz_mat, M3.toR]
  all_goals first
    | linarith
    | (rw [show -sin (2 * π * g / 15) + D (sinTab[g]!) = -(sin (2 * π * g / 15) - D (sinTab[g]!)) by ring,
        abs_neg]; linarith)

end Cayley

end
