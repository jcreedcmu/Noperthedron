module

public import Noperthedron.PentagonalHexecontahedron.CapChart

@[expose] public section

/-!
# Certificate trees of the DH cap charts

A chart's certificate (nopert229 `capcert.cc --export`) is a binary
subdivision tree of its box: splits at the midpoint of one coordinate, and
leaves that are a witness index, a half-turn-cell prune, or (F_e charts) a box
inside the cone charts' region. `CTree.check` evaluates the leaf tests over the
tree; `CTree.check_sound` turns per-leaf soundness into a statement about
every point of the root box, so the subdivision needs no separate coverage
argument. `boxOk_sound`: a witness leaf makes every divided witness polynomial,
hence (with μ, t ≥ 0) every witness polynomial, nonnegative on the box.
-/

namespace Noperthedron.PentagonalHexecontahedron.Cap

open NPoly

abbrev Box := Fin 5 → ℚ × ℚ

inductive CTree where
  | split (axis : Fin 5) (l r : CTree)
  | leaf (w : ℕ)
  | prune
  | cone
  | fail
deriving Inhabited

/-- The lower (upper = false) or upper half of the box in coordinate a. -/
def half (box : Box) (a : Fin 5) (upper : Bool) : Box := fun i =>
  if i = a then ((box i).1 + (if upper then (box i).2 / 2 else 0), (box i).2 / 2) else box i

theorem half_width_nonneg {box : Box} (hb : ∀ i, 0 ≤ (box i).2) (a : Fin 5) (upper : Bool) :
    ∀ i, 0 ≤ (half box a upper i).2 := by
  intro i
  by_cases hi : i = a
  · simp only [half, hi, if_true]; exact div_nonneg (hb a) (by norm_num)
  · simp only [half, hi, if_false]; exact hb i

theorem inBox_half {box : Box} {y : Fin 5 → ℝ} (hy : InBox box y) (a : Fin 5) :
    InBox (half box a false) y ∨ InBox (half box a true) y := by
  by_cases hmid : y a ≤ (box a).1 + (box a).2 / 2
  · left
    intro i
    by_cases hi : i = a
    · subst hi
      simp only [half, if_true, Bool.false_eq_true, if_false, add_zero]
      push_cast
      exact ⟨(hy i).1, by linarith⟩
    · simp only [half, hi, if_false]; exact hy i
  · right
    intro i
    by_cases hi : i = a
    · subst hi
      simp only [half, if_true]
      push_cast
      exact ⟨by linarith, by linarith [(hy i).2]⟩
    · simp only [half, hi, if_false]; exact hy i

/-- The tree check with the leaf tests as parameters. -/
def CTree.check (leafOk : ℕ → Box → Bool) (pruneOk coneOk : Box → Bool) : CTree → Box → Bool
  | .split a l r, box => l.check leafOk pruneOk coneOk (half box a false) &&
      r.check leafOk pruneOk coneOk (half box a true)
  | .leaf w, box => leafOk w box
  | .prune, box => pruneOk box
  | .cone, box => coneOk box
  | .fail, _ => false

theorem CTree.check_sound (leafOk : ℕ → Box → Bool) (pruneOk coneOk : Box → Bool)
    (Good : (Fin 5 → ℝ) → Prop)
    (hleaf : ∀ w box, (∀ i, 0 ≤ (box i).2) → leafOk w box = true → ∀ y, InBox box y → Good y)
    (hprune : ∀ box, (∀ i, 0 ≤ (box i).2) → pruneOk box = true → ∀ y, InBox box y → Good y)
    (hcone : ∀ box, (∀ i, 0 ≤ (box i).2) → coneOk box = true → ∀ y, InBox box y → Good y) :
    ∀ (t : CTree) (box : Box), (∀ i, 0 ≤ (box i).2) → t.check leafOk pruneOk coneOk box = true →
      ∀ y, InBox box y → Good y
  | .split a l r, box, hb, h, y, hy => by
    simp only [CTree.check, Bool.and_eq_true] at h
    rcases inBox_half hy a with h1 | h1
    · exact CTree.check_sound leafOk pruneOk coneOk Good hleaf hprune hcone l _
        (half_width_nonneg hb a false) h.1 y h1
    · exact CTree.check_sound leafOk pruneOk coneOk Good hleaf hprune hcone r _
        (half_width_nonneg hb a true) h.2 y h1
  | .leaf w, box, hb, h, y, hy => hleaf w box hb h y hy
  | .prune, box, hb, h, y, hy => hprune box hb h y hy
  | .cone, box, hb, h, y, hy => hcone box hb h y hy
  | .fail, _, _, h, _, _ => by simp [CTree.check] at h

/-- A witness leaf: every divided polynomial has a nonnegative Bernstein bound. -/
theorem boxOk_sound {Q : Array (NPoly 5)} {box : Box} (hb : ∀ i, 0 ≤ (box i).2) (h : boxOk Q box = true)
    {y : Fin 5 → ℝ} (hy : InBox box y) : ∀ q ∈ Q, 0 ≤ NPoly.eval 5 q y := by
  intro q hq
  have := Array.all_eq_true.mp h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hq
  have hlow := of_decide_eq_true (this i hi)
  have := lowerDeg_le_eval 5 (degs Q[i]) Q[i] box y hb hy
  exact le_trans (by exact_mod_cast hlow) this

/-- The witness polynomials are nonnegative wherever their divided forms are, for μ ≥ 0 and
(cones) t ≥ 0. -/
theorem witnessPoly_nonneg (ch : Chart) (id : ChartId) (V : Array KVec) (vk c : KVec) (y : Fin 5 → ℝ)
    (hmu : 0 ≤ y 0) (ht : isCone id = true → 0 ≤ y 2)
    (hQ : ∀ q ∈ witnessPolys ch id V vk c, 0 ≤ NPoly.eval 5 q y) :
    ∀ vj ∈ V, 0 ≤ NPoly.eval 5 (witnessPoly (witnessParts ch.u ch.w vk c) vj) y := by
  intro vj hvj
  set p := witnessPoly (witnessParts ch.u ch.w vk c) vj
  have hmem : (let q := NPoly.divOut 5 0 64 p; if isCone id then NPoly.divOut 5 2 64 q else q) ∈
      witnessPolys ch id V vk c := by
    unfold witnessPolys
    exact Array.mem_map.mpr ⟨vj, hvj, rfl⟩
  have h0 := hQ _ hmem
  obtain ⟨m, hm⟩ := eval_divOut 5 0 y 64 p
  rw [hm]
  apply mul_nonneg (pow_nonneg hmu m)
  by_cases hc : isCone id = true
  · simp only [hc, if_true] at h0
    obtain ⟨n, hn⟩ := eval_divOut 5 2 y 64 (NPoly.divOut 5 0 64 p)
    rw [hn]
    exact mul_nonneg (pow_nonneg (ht hc) n) h0
  · simp only [hc] at h0
    simpa using h0

end Noperthedron.PentagonalHexecontahedron.Cap
