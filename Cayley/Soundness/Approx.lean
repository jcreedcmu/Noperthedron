module

public import Cayley.Soundness.Pose
public import Cayley.Soundness.TrigTable

@[expose] public section

/-!
# The checker's approximate data

The integer vertices `vtxZ` (over `2^160`, computed from the integer trigonometric tables and
the rounded points `C₁, C₂, C₃`) are within `ε = 2⁻⁶⁰` of the true vertices, the tabulated
symmetries `gHat` are within `ε` of the true rotations, and `τ` permutes the `C3` copies
exactly as `tauPair` says.
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

/-- `2^80 Cᵢ`, rounded to integers. -/
def cTab : ℕ → ℤ × ℤ × ℤ
  | 0 => (708575083310368564287871, 0, 979501397978893732372791)
  | 1 => (801848825678901923219191, 738284818130756748970184, 481267276890486254372654)
  | _ => (990592611655862735853342, 640514902742640119587028, 148772163457966633721405)

theorem cTab_err (i : ℕ) (hi : i < 3) :
    |Cpt ⟨i, hi⟩ 0 - ((cTab i).1 : ℝ) / 2 ^ 80| ≤ 1 / 2 ^ 80 ∧
    |Cpt ⟨i, hi⟩ 1 - ((cTab i).2.1 : ℝ) / 2 ^ 80| ≤ 1 / 2 ^ 80 ∧
    |Cpt ⟨i, hi⟩ 2 - ((cTab i).2.2 : ℝ) / 2 ^ 80| ≤ 1 / 2 ^ 80 ∧
    |((cTab i).1 : ℝ) / 2 ^ 80| ≤ 1 ∧ |((cTab i).2.1 : ℝ) / 2 ^ 80| ≤ 1 := by
  interval_cases i <;>
    simp [Cpt, C1R, C2R, C3R, C1, C2, C3, cTab, abs_le] <;> norm_num

/-- The integer vertex with checker index `t`, over `2^160`: `(-1)^ℓ R̂z(2πk/15) Ĉᵢ`. -/
def vtxZ (t : ℕ) : ℤ × ℤ × ℤ :=
  let c := cosM (t / 6)
  let s := sinM (t / 6)
  let p := cTab (t % 3)
  let sg : ℤ := if t % 6 / 3 = 0 then 1 else -1
  (sg * (c * p.1 - s * p.2.1), sg * (s * p.1 + c * p.2.1), sg * (p.2.2 * 2 ^ 80))

/-- An integer triple as a real vector. -/
def svec (S : ℤ × ℤ × ℤ) : Fin 3 → ℝ := ![(S.1 : ℝ), S.2.1, S.2.2]

theorem vertex_approx (t : ℕ) (ht : t < 90) (i : Fin 3) :
    |vtx t i - svec (vtxZ t) i / 2 ^ 160| ≤ 1 / 2 ^ 60 := by
  set k := t / 6
  set l := t % 6 / 3
  set ci := t % 3
  have hk : k < 15 := by omega
  have hl : l < 2 := by omega
  have hci : ci < 3 := by omega
  have hidx : vIdx t = ⟨⟨k, hk⟩, ⟨l, hl⟩, ⟨ci, hci⟩⟩ := by
    simp only [vIdx, VertexIndex.mk.injEq, Fin.mk.injEq]; omega
  have hcos := cos_tab_err k hk
  have hsin := sin_tab_err k hk
  have hcb : |cos (2 * π * k / 15)| ≤ 1 := abs_cos_le_one _
  have hsb : |sin (2 * π * k / 15)| ≤ 1 := abs_sin_le_one _
  obtain ⟨h0, h1, h2, hb0, hb1⟩ := cTab_err ci hci
  obtain ⟨r1, r2⟩ := rot_err hcos hsin h0 h1 hcb hsb hb0 hb1
  have hsmall : 2 * (1 / 2 ^ 71 + 1 / 2 ^ 80 : ℝ) ≤ 1 / 2 ^ 60 := by norm_num
  have hsmall' : (1 / 2 ^ 80 : ℝ) ≤ 1 / 2 ^ 60 := by norm_num
  -- the tabulated vertex, coordinate by coordinate
  set sg : ℝ := if l = 0 then 1 else -1
  have e0 : svec (vtxZ t) 0 / 2 ^ 160 = sg * ((cosM k : ℝ) / 2 ^ 80 * ((cTab ci).1 / 2 ^ 80) -
      (sinM k : ℝ) / 2 ^ 80 * ((cTab ci).2.1 / 2 ^ 80)) := by
    simp only [svec, vtxZ, sg, Matrix.cons_val_zero]; split_ifs <;> push_cast <;> ring
  have e1 : svec (vtxZ t) 1 / 2 ^ 160 = sg * ((sinM k : ℝ) / 2 ^ 80 * ((cTab ci).1 / 2 ^ 80) +
      (cosM k : ℝ) / 2 ^ 80 * ((cTab ci).2.1 / 2 ^ 80)) := by
    simp only [svec, vtxZ, sg, Matrix.cons_val_one, Matrix.cons_val_zero]
    split_ifs <;> push_cast <;> ring
  have e2 : svec (vtxZ t) 2 / 2 ^ 160 = sg * (((cTab ci).2.2 : ℝ) / 2 ^ 80) := by
    simp only [svec, vtxZ, sg, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    split_ifs <;> push_cast <;> ring
  have hv : ∀ a b c : ℝ, ((-1 : ℤ) ^ l • !₂[a, b, c] : ℝ³) = !₂[sg * a, sg * b, sg * c] := by
    intro a b c
    rcases (by omega : l = 0 ∨ l = 1) with h | h <;> ext j <;> fin_cases j <;> simp [sg, h]
  have hsg : |sg| = 1 := by simp only [sg]; split_ifs <;> simp
  have key : ∀ a b : ℝ, |a - b| ≤ 1 / 2 ^ 60 → |sg * a - sg * b| ≤ 1 / 2 ^ 60 := fun a b h => by
    rw [← mul_sub, abs_mul, hsg, one_mul]; exact h
  unfold vtx
  rw [hidx, exactVertex_eq_vec]
  simp only [hv]
  fin_cases i
  · rw [show (⟨0, by norm_num⟩ : Fin 3) = 0 from rfl, e0]; exact key _ _ (r1.trans hsmall)
  · rw [show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl, e1]; exact key _ _ (r2.trans hsmall)
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, e2]; exact key _ _ (h2.trans hsmall')

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

/-- The tabulated symmetry `ĝ`. -/
noncomputable def gHat (g : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(cosM g : ℝ) / 2 ^ 80, -((sinM g : ℝ) / 2 ^ 80), 0;
     (sinM g : ℝ) / 2 ^ 80, (cosM g : ℝ) / 2 ^ 80, 0;
     0, 0, 1]

theorem group_approx (g : ℕ) (hg : g < 15) (i k : Fin 3) :
    |gR g i k - gHat g i k| ≤ 1 / 2 ^ 60 := by
  have hcos := cos_tab_err g hg
  have hsin := sin_tab_err g hg
  have hs : (1 / 2 ^ 71 : ℝ) ≤ 1 / 2 ^ 60 := by norm_num
  fin_cases i <;> fin_cases k <;> simp [gR, Rz_mat, gHat]
  all_goals first
    | linarith
    | (rw [show -sin (2 * π * g / 15) + (sinM g : ℝ) / 2 ^ 80 =
          -(sin (2 * π * g / 15) - (sinM g : ℝ) / 2 ^ 80) by ring, abs_neg]; linarith)

end Cayley

end
