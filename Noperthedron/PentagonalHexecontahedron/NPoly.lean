module

public import Noperthedron.PentagonalHexecontahedron.IcoQ
public import Noperthedron.PentagonalHexecontahedron.BernsteinBound

@[expose] public section

/-!
# Nested polynomials over K = ℚ(√5, sin 72°)

`NPoly k` is a polynomial in k real variables with coefficients in `IcoQ`:
`NPoly 0 = IcoQ`, and `NPoly (k + 1)` is the list of coefficients (in
`NPoly k`, the polynomials in the remaining variables) of the powers of the
first variable. Evaluation is Horner's rule. Every operation the DH cap
checker needs is univariate in the first variable and recursive in the rest,
so its soundness is an induction on k from the univariate facts.
-/

namespace Noperthedron.PentagonalHexecontahedron

def NPoly : ℕ → Type
  | 0 => IcoQ
  | k + 1 => List (NPoly k)

namespace NPoly

/-! ### Evaluation -/

/-- Horner evaluation of a coefficient list, given the coefficient values. -/
noncomputable def horner {α : Type} (v : α → ℝ) (x : ℝ) : List α → ℝ
  | [] => 0
  | a :: as => v a + x * horner v x as

noncomputable def eval : (k : ℕ) → NPoly k → (Fin k → ℝ) → ℝ
  | 0, c, _ => IcoQ.val c
  | k + 1, p, y => horner (fun q => eval k q (Fin.tail y)) (y 0) (p : List (NPoly k))

@[simp] theorem horner_nil {α : Type} (v : α → ℝ) (x : ℝ) : horner v x [] = 0 := rfl
@[simp] theorem horner_cons {α : Type} (v : α → ℝ) (x : ℝ) (a : α) (as : List α) :
    horner v x (a :: as) = v a + x * horner v x as := rfl

/-- The j-th coefficient value (0 past the end). -/
noncomputable def cf {α : Type} (v : α → ℝ) (l : List α) (j : ℕ) : ℝ :=
  match l[j]? with
  | some a => v a
  | none => 0

theorem horner_eq_sum {α : Type} (v : α → ℝ) (x : ℝ) (l : List α) :
    horner v x l = ∑ j ∈ Finset.range l.length, cf v l j * x ^ j := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [horner_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [cf, List.getElem?_cons_succ, List.getElem?_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-! ### Zero, constants, linear operations -/

def zero : (k : ℕ) → NPoly k
  | 0 => (0 : IcoQ)
  | _ + 1 => ([] : List _)

theorem eval_zero (k : ℕ) (y : Fin k → ℝ) : eval k (zero k) y = 0 := by
  cases k with
  | zero => exact IcoQ.val_zero
  | succ k => rfl

/-- Padded pointwise combination of coefficient lists. -/
def ladd {α : Type} (f : α → α → α) : List α → List α → List α
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => f x y :: ladd f xs ys

def add : (k : ℕ) → NPoly k → NPoly k → NPoly k
  | 0, a, b => IcoQ.add a b
  | k + 1, a, b => ladd (add k) (a : List (NPoly k)) b

def scale : (k : ℕ) → ℚ → NPoly k → NPoly k
  | 0, q, a => IcoQ.scale q a
  | k + 1, q, a => (a : List (NPoly k)).map (scale k q)

theorem horner_ladd {α : Type} (v : α → ℝ) (x : ℝ) (f : α → α → α) (hf : ∀ a b, v (f a b) = v a + v b) :
    ∀ a b : List α, horner v x (ladd f a b) = horner v x a + horner v x b
  | [], b => by simp [ladd]
  | _ :: _, [] => by simp [ladd]
  | a :: as, b :: bs => by
    simp only [ladd, horner_cons, hf, horner_ladd v x f hf as bs]
    ring

theorem eval_add : ∀ (k : ℕ) (a b : NPoly k) (y : Fin k → ℝ), eval k (add k a b) y = eval k a y + eval k b y
  | 0, a, b, _ => IcoQ.val_add a b
  | k + 1, a, b, y => horner_ladd _ _ _ (fun p q => eval_add k p q _) _ _

theorem eval_scale : ∀ (k : ℕ) (q : ℚ) (a : NPoly k) (y : Fin k → ℝ), eval k (scale k q a) y = q * eval k a y
  | 0, q, a, _ => IcoQ.val_scale q a
  | k + 1, q, a, y => by
    show horner _ _ ((a : List (NPoly k)).map (scale k q)) = _ * horner _ _ (a : List (NPoly k))
    induction (a : List (NPoly k)) with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, horner_cons, eval_scale k q p, ih]
      ring

/-- Σ_i q_i • p_i over a list of (weight, polynomial) pairs. -/
def lincomb (k : ℕ) : List (ℚ × NPoly k) → NPoly k
  | [] => zero k
  | (q, p) :: rest => add k (scale k q p) (lincomb k rest)

theorem eval_lincomb (k : ℕ) (l : List (ℚ × NPoly k)) (y : Fin k → ℝ) :
    eval k (lincomb k l) y = (l.map fun qp => (qp.1 : ℝ) * eval k qp.2 y).sum := by
  induction l with
  | nil => simp [lincomb, eval_zero]
  | cons qp rest ih =>
    obtain ⟨q, p⟩ := qp
    simp [lincomb, eval_add, eval_scale, ih]

theorem sum_map_range {β : Type} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-! ### Taylor shift and Bernstein transform in the first variable -/

/-- The real identity behind `shift`: Σ_{f<L} a_f (lo + h t)^f =
Σ_{g<L} (Σ_{m<L-g} C(g+m, g) lo^m h^g a_{g+m}) t^g. -/
theorem taylor_shift (L : ℕ) (a : ℕ → ℝ) (lo h t : ℝ) :
    ∑ f ∈ Finset.range L, a f * (lo + h * t) ^ f =
      ∑ g ∈ Finset.range L,
        (∑ m ∈ Finset.range (L - g), ((g + m).choose g : ℝ) * lo ^ m * h ^ g * a (g + m)) * t ^ g := by
  have hin : ∀ g ∈ Finset.range L,
      (∑ m ∈ Finset.range (L - g), ((g + m).choose g : ℝ) * lo ^ m * h ^ g * a (g + m)) * t ^ g =
        ∑ f ∈ Finset.Ico g L, (f.choose g : ℝ) * lo ^ (f - g) * h ^ g * a f * t ^ g := by
    intro g _
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    rw [Nat.add_sub_cancel_left]
  rw [Finset.sum_congr rfl hin]
  rw [Finset.sum_comm' (s' := fun f => Finset.range (f + 1)) (t' := Finset.range L)]
  · apply Finset.sum_congr rfl
    intro f _
    rw [add_comm lo, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_pow]
    ring
  · intro g f
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- Coefficient j of a coefficient list (zero past the end). -/
def coeffAt (k : ℕ) (p : List (NPoly k)) (j : ℕ) : NPoly k := p.getD j (zero k)

theorem cf_eq_eval (k : ℕ) (p : List (NPoly k)) (y : Fin k → ℝ) (j : ℕ) :
    cf (fun q => eval k q y) p j = eval k (coeffAt k p j) y := by
  unfold cf coeffAt
  rw [List.getD_eq_getElem?_getD]
  cases p[j]? with
  | none => simp [eval_zero]
  | some a => rfl

/-- The Taylor shift x = lo + h t of the first variable. -/
def shift (k : ℕ) (lo h : ℚ) (p : List (NPoly k)) : List (NPoly k) :=
  (List.range p.length).map fun g =>
    lincomb k ((List.range (p.length - g)).map fun m =>
      (((g + m).choose g : ℚ) * lo ^ m * h ^ g, coeffAt k p (g + m)))

theorem length_shift (k : ℕ) (lo h : ℚ) (p : List (NPoly k)) : (shift k lo h p).length = p.length := by
  simp [shift]

theorem coeffAt_shift (k : ℕ) (lo h : ℚ) (p : List (NPoly k)) (y : Fin k → ℝ) (g : ℕ) (hg : g < p.length) :
    eval k (coeffAt k (shift k lo h p) g) y =
      ∑ m ∈ Finset.range (p.length - g),
        ((g + m).choose g : ℝ) * (lo : ℝ) ^ m * (h : ℝ) ^ g * eval k (coeffAt k p (g + m)) y := by
  have : coeffAt k (shift k lo h p) g = lincomb k ((List.range (p.length - g)).map fun m =>
      (((g + m).choose g : ℚ) * lo ^ m * h ^ g, coeffAt k p (g + m))) := by
    simp [coeffAt, shift, List.getD_eq_getElem?_getD, hg]
  rw [this, eval_lincomb, List.map_map, sum_map_range]
  apply Finset.sum_congr rfl
  intro m _
  simp

theorem horner_shift (k : ℕ) (lo h : ℚ) (p : List (NPoly k)) (y : Fin k → ℝ) (t : ℝ) :
    horner (fun q => eval k q y) ((lo : ℝ) + h * t) p = horner (fun q => eval k q y) t (shift k lo h p) := by
  rw [horner_eq_sum, horner_eq_sum, length_shift, taylor_shift]
  apply Finset.sum_congr rfl
  intro g hg
  rw [Finset.mem_range] at hg
  rw [cf_eq_eval, coeffAt_shift k lo h p y g hg]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [cf_eq_eval]

/-- The Bernstein coefficient i of a coefficient list of degree d = length - 1. -/
def bern (k : ℕ) (p : List (NPoly k)) (i : ℕ) : NPoly k :=
  lincomb k ((List.range (i + 1)).map fun j =>
    ((i.choose j : ℚ) / ((p.length - 1).choose j : ℚ), coeffAt k p j))

theorem eval_bern (k : ℕ) (p : List (NPoly k)) (y : Fin k → ℝ) (i : ℕ) :
    eval k (bern k p i) y = Bernstein.coeff (p.length - 1) (cf (fun q => eval k q y) p) i := by
  rw [bern, eval_lincomb, List.map_map, sum_map_range, Bernstein.coeff]
  apply Finset.sum_congr rfl
  intro j _
  simp [cf_eq_eval]

/-! ### The box lower bound -/

def minList : List ℚ → ℚ
  | [] => 0
  | [a] => a
  | a :: b :: rest => min a (minList (b :: rest))

theorem minList_le : ∀ (l : List ℚ), ∀ x ∈ l, minList l ≤ x
  | [], _, h => by simp at h
  | [a], x, h => by simp at h; simp [minList, h]
  | a :: b :: rest, x, h => by
    rw [minList]
    rcases List.mem_cons.mp h with h | h
    · rw [h]; exact min_le_left _ _
    · exact (min_le_right _ _).trans (minList_le (b :: rest) x h)

/-- A lower bound of the polynomial on the box Π [lo_i, lo_i + h_i] (box i = (lo_i, h_i)):
shift the first variable to [0, 1], take its Bernstein coefficients (polynomials in the
remaining variables) and recurse; at the leaves, the rational lower enclosure. -/
def lower : (k : ℕ) → NPoly k → (Fin k → ℚ × ℚ) → ℚ
  | 0, c, _ => IcoQ.lo c
  | k + 1, p, box =>
    let q := shift k (box 0).1 (box 0).2 p
    minList ((List.range q.length).map fun i => lower k (bern k q i) (Fin.tail box))

def InBox {k : ℕ} (box : Fin k → ℚ × ℚ) (y : Fin k → ℝ) : Prop :=
  ∀ i, ((box i).1 : ℝ) ≤ y i ∧ y i ≤ (box i).1 + (box i).2

theorem lower_le_eval : ∀ (k : ℕ) (p : NPoly k) (box : Fin k → ℚ × ℚ) (y : Fin k → ℝ),
    (∀ i, 0 ≤ (box i).2) → InBox box y → (lower k p box : ℝ) ≤ eval k p y
  | 0, c, _, _, _, _ => IcoQ.lo_le_val c
  | k + 1, p, box, y, hh, hy => by
    set lo := (box 0).1
    set h := (box 0).2
    have h0 : (0 : ℝ) ≤ h := by exact_mod_cast hh 0
    obtain ⟨hlo, hhi⟩ := hy 0
    -- y 0 = lo + h t with t ∈ [0, 1].
    obtain ⟨t, ht0, ht1, hx⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y 0 = lo + h * t := by
      rcases h0.lt_or_eq with hp | hz
      · refine ⟨(y 0 - lo) / h, div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith), ?_⟩
        field_simp
        ring
      · exact ⟨0, le_refl _, zero_le_one, by rw [← hz] at hhi; linarith⟩
    have hyt : InBox (Fin.tail box) (Fin.tail y) := fun i => hy i.succ
    have hht : ∀ i, 0 ≤ (Fin.tail box i).2 := fun i => hh i.succ
    set q := shift k lo h (p : List (NPoly k))
    show (minList ((List.range q.length).map fun i => lower k (bern k q i) (Fin.tail box)) : ℝ) ≤
      horner (fun q => eval k q (Fin.tail y)) (y 0) (p : List (NPoly k))
    rw [hx, horner_shift, horner_eq_sum]
    rcases Nat.eq_zero_or_pos q.length with hq | hq
    · rw [hq]
      simp [minList]
    obtain ⟨d, hd⟩ : ∃ d, q.length = d + 1 := ⟨q.length - 1, by omega⟩
    rw [hd]
    apply Bernstein.bernstein_lower d _ _ _ ht0 ht1
    intro i hi
    have hmem : lower k (bern k q i) (Fin.tail box) ∈
        (List.range q.length).map fun i => lower k (bern k q i) (Fin.tail box) :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
    have h1 := minList_le _ _ hmem
    rw [hd] at h1
    have h2 := lower_le_eval k (bern k q i) (Fin.tail box) (Fin.tail y) hht hyt
    rw [eval_bern, hd, Nat.add_sub_cancel] at h2
    calc _ ≤ ((lower k (bern k q i) (Fin.tail box) : ℚ) : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2

end NPoly

end Noperthedron.PentagonalHexecontahedron
