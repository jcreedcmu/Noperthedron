import Mathlib.Analysis.InnerProductSpace.PiL2

import Noperthedron.EuclideanSpaceNotation

namespace RationalApprox

/--
Two sequences of matrices A₁,...,Aₖ and B₁,...,Bₖ with sizes that make
the products A₁...Aₖ and B₁...Bₖ well-defined, as in [SY25] Lemma 42.
-/
inductive MatVec : (n m : ℕ) → Type where
  | nil : {n : ℕ} → MatVec n n
  | cons : {n m p : ℕ} → (tl : MatVec n m) → (A B : (Euc(p) →L[ℝ] Euc(m))) → MatVec n p

@[simp]
noncomputable
def MatVec.maxNormList {n m : ℕ} (mv : MatVec n m) : List ℝ := match mv with
  | .nil => []
  | .cons tl A B => tl.maxNormList ++ [max (max ‖A‖ ‖B‖) 1]

@[simp]
noncomputable
def MatVec.allNormsBelow {n m : ℕ} (mv : MatVec n m) (bs : List ℝ) : Prop := go mv bs.reverse where
  go : {n m : ℕ} → MatVec n m → List ℝ → Prop := fun
  | .nil, [] => True
  | .cons tl A B, b::bsr => go tl bsr ∧ ‖A‖ ≤ b ∧ ‖B‖ ≤ b
  | .nil, _::_ => False
  | .cons _ _ _, [] => False

@[simp]
def MatVec.DiffBoundedBy {n m : ℕ} (mv : MatVec n m) (κ : ℝ) : Prop :=
  match mv with
  | .nil => True
  | .cons tl A B => tl.DiffBoundedBy κ ∧  ‖A - B‖ ≤ κ

@[simp]
def MatVec.compA {n m : ℕ} (mv : MatVec n m) : Euc(m) →L[ℝ] Euc(n) :=
  match mv with
  | nil  => ContinuousLinearMap.id ℝ Euc(n)
  | cons tl A _ => tl.compA ∘L A

@[simp]
def MatVec.compB {n m : ℕ} (mv : MatVec n m) : Euc(m) →L[ℝ] Euc(n) :=
  match mv with
  | nil  => ContinuousLinearMap.id ℝ Euc(n)
  | cons tl _ B => tl.compB ∘L B

@[simp]
noncomputable
def MatVec.valA (mv : MatVec 1 1) : ℝ :=  mv.compA (EuclideanSpace.single 0 1) 0

@[simp]
noncomputable
def MatVec.valB (mv : MatVec 1 1) : ℝ :=  mv.compB (EuclideanSpace.single 0 1) 0

@[simp]
def MatVec.size {n m : ℕ} (mv : MatVec n m) : ℕ :=
  match mv with
  | nil  => 0
  | cons tl _ _ => tl.size + 1

lemma norm_comp_a_le_prod_max_norm_list_prod
    {n m : ℕ} (mv : MatVec n m) :
    ‖mv.compA‖ ≤ mv.maxNormList.prod := by
  match mv with
  | .nil =>
      simp only [MatVec.compA, MatVec.maxNormList, List.prod_nil, ge_iff_le];
      exact ContinuousLinearMap.norm_id_le
  | .cons tl A B =>
      simp only [MatVec.compA, MatVec.maxNormList, List.prod_append, List.prod_cons, List.prod_nil,
        mul_one, ge_iff_le]
      have : ‖tl.compA.comp A‖ ≤ ‖tl.compA‖ * ‖A‖ :=
        ContinuousLinearMap.opNorm_comp_le tl.compA A
      grw [this]
      have : ‖tl.compA‖ ≤ tl.maxNormList.prod := norm_comp_a_le_prod_max_norm_list_prod tl
      grw [← this]
      gcongr
      simp

@[simp]
lemma MatVec.maxNormList_non_neg {m n : ℕ} (mv : MatVec n m) :
    0 ≤ mv.maxNormList.prod := by
  match mv with
  | .nil => simp
  | .cons tl A B =>
    simp only [maxNormList, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one, lt_sup_iff, zero_lt_one, or_true, mul_nonneg_iff_of_pos_right]
    exact tl.maxNormList_non_neg

/-- [SY25] Lemma 42 -/
lemma norm_sub_le_prod {n m : ℕ} (mv : MatVec n m)
    (κ : ℝ) (κ_pos : κ > 0) (hκ : mv.DiffBoundedBy κ) :
    ‖mv.compA - mv.compB‖ ≤ mv.size * κ * mv.maxNormList.prod := by
  induction mv with
  | nil =>
    simp only  [MatVec.compA, MatVec.compB, MatVec.size, sub_self,
     ContinuousLinearMap.opNorm_zero, CharP.cast_eq_zero, zero_mul, le_refl]
  | cons tl A B ih =>
    obtain ⟨ hκtl, hκ ⟩ := hκ
    specialize ih hκtl
    simp only [MatVec.compA, MatVec.compB, MatVec.size, MatVec.maxNormList]
    calc ‖tl.compA.comp A - tl.compB.comp B‖
      _ ≤ ‖tl.compA.comp A - tl.compA.comp B‖ + ‖tl.compA.comp B - tl.compB.comp B‖ :=
        norm_sub_le_norm_sub_add_norm_sub (tl.compA.comp A) (tl.compA.comp B) (tl.compB.comp B)
      _ = ‖tl.compA.comp (A - B)‖ + ‖(tl.compA - tl.compB).comp B‖ := by simp
      _ ≤ ‖tl.compA‖ * ‖(A - B)‖ + ‖(tl.compA - tl.compB).comp B‖ := by
        gcongr; exact ContinuousLinearMap.opNorm_comp_le tl.compA (A - B)
      _ ≤ ‖tl.compA‖ * ‖(A - B)‖ + ‖(tl.compA - tl.compB)‖ * ‖B‖ := by
        gcongr; exact ContinuousLinearMap.opNorm_comp_le (tl.compA - tl.compB) B
      _ ≤ ‖tl.compA‖ * κ + (↑tl.size * κ * tl.maxNormList.prod) * ‖B‖ := by
        grw [ih, hκ]
      _ ≤ (tl.maxNormList.prod) * κ + (↑tl.size * κ * tl.maxNormList.prod) * ‖B‖ := by
        grw [norm_comp_a_le_prod_max_norm_list_prod tl]
      _ ≤ (tl.size + 1) * κ * (tl.maxNormList ++ [max (max ‖A‖ ‖B‖) 1]).prod := by
         simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one]
         ring_nf
         have : max (max ‖A‖ ‖B‖) 1 ≥ ‖B‖ := by simp
         have side : 0 ≤ tl.maxNormList.prod * κ * tl.size := by
           grw [← tl.maxNormList_non_neg]; simp
         nth_grw 1 [this]
         have : max (max ‖A‖ ‖B‖) 1 ≥ 1 := by simp
         have side : 0 ≤ tl.maxNormList.prod * κ := by
           grw [← tl.maxNormList_non_neg]; simp
         grw [this]
         ring_nf
         apply le_refl
    simp [le_refl]

lemma allNormsBelow_def {n m : ℕ} (mv : MatVec n m)
    {bs : List ℝ} (hbs1 : ∀ b ∈ bs, 1 ≤ b) (hb : mv.allNormsBelow bs) :
    mv.maxNormList.prod ≤ bs.prod := by
  induction mv generalizing bs with
  | nil =>
    simp only [MatVec.maxNormList, List.prod_nil, MatVec.allNormsBelow] at hb ⊢
    exact List.one_le_prod hbs1
  | cons tl A B ih =>
    simp only [MatVec.maxNormList, MatVec.allNormsBelow] at hb ⊢
    cases hbsr : bs.reverse with
    | nil => simp only [hbsr, MatVec.allNormsBelow.go] at hb
    | cons b bsr =>
      simp only [hbsr, MatVec.allNormsBelow.go] at hb
      obtain ⟨htl, hA, hB⟩ := hb
      have htl' : tl.allNormsBelow bsr.reverse := by simpa [MatVec.allNormsBelow]
      rw [List.reverse_eq_cons_iff] at hbsr
      have hbsr1 : ∀ x ∈ bsr.reverse, 1 ≤ x := fun x hx ↦ hbs1 x (hbsr ▸ List.mem_append_left _ hx)
      have ih_bound := ih hbsr1 htl'
      have hb1 : 1 ≤ b := hbs1 b (by simp [hbsr])
      rw [hbsr, List.prod_append, List.prod_singleton, List.prod_append, List.prod_singleton]
      have h_max_le : max (max ‖A‖ ‖B‖) 1 ≤ b := max_le_iff.mpr ⟨max_le hA hB, hb1⟩
      have h_bsr_nonneg : 0 ≤ bsr.reverse.prod := le_trans tl.maxNormList_non_neg ih_bound
      exact mul_le_mul ih_bound h_max_le (le_of_lt (lt_max_of_lt_right one_pos)) h_bsr_nonneg

lemma norm_sub_le_bound {n m : ℕ} (mv : MatVec n m)
    (κ : ℝ) (κ_pos : κ > 0) (hκ : mv.DiffBoundedBy κ)
    {bs : List ℝ} (hbs1 : ∀ b ∈ bs, 1 ≤ b) (hb : mv.allNormsBelow bs) :
    ‖mv.compA - mv.compB‖ ≤ mv.size * κ * bs.prod := by
  grw [norm_sub_le_prod mv κ κ_pos hκ, allNormsBelow_def mv hbs1 hb]

lemma norm_sub_le_prod1 (mv : MatVec 1 1)
    (κ : ℝ) (κ_pos : κ > 0) (hκ : mv.DiffBoundedBy κ) :
    |mv.valA - mv.valB| ≤ mv.size * κ * mv.maxNormList.prod := by
  simp only [MatVec.valA, Fin.isValue, MatVec.valB]
  have (v w : Euc(1)) : ‖v - w‖ = |v 0 - w 0| := by
    rw [PiLp.norm_eq_of_L2]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, PiLp.sub_apply,
      Real.norm_eq_abs, sq_abs, Finset.sum_singleton]
    exact Real.sqrt_sq_eq_abs (v.ofLp 0 - w.ofLp 0)
  rw [← this]
  calc ‖mv.compA (EuclideanSpace.single 0 1) - mv.compB (EuclideanSpace.single 0 1)‖
  _ = ‖(mv.compA - mv.compB) (EuclideanSpace.single 0 1)‖ := by rfl
  _ ≤ ‖(mv.compA - mv.compB)‖ * ‖EuclideanSpace.single 0 1‖ :=
    (mv.compA - mv.compB).le_opNorm _
  _ ≤ ‖(mv.compA - mv.compB)‖ := by simp
  _ ≤ ↑mv.size * κ * mv.maxNormList.prod := norm_sub_le_prod mv κ κ_pos hκ

lemma norm_sub_le_bound1 (mv : MatVec 1 1)
    (κ : ℝ) (κ_pos : κ > 0) (hκ : mv.DiffBoundedBy κ)
    {bs : List ℝ} (hbs1 : ∀ b ∈ bs, 1 ≤ b) (hb : mv.allNormsBelow bs) :
    |mv.valA - mv.valB| ≤ mv.size * κ * bs.prod := by
  grw [norm_sub_le_prod1 mv κ κ_pos hκ, allNormsBelow_def mv hbs1 hb]

end RationalApprox

syntax "⟦" term,* "⟧" : term

def buildMatVec (ps : List (List (Lean.Syntax))) : Lean.MacroM (Lean.Syntax) :=
    match ps with
    | [] => ``(RationalApprox.MatVec.nil)
    | [a, b] :: rest => do
      let tail ← buildMatVec rest
      ``(RationalApprox.MatVec.cons $(⟨tail⟩) $(⟨a⟩) $(⟨b⟩))
    | _ => Lean.Macro.throwError s!"MatVec list should have an even number of elements"

macro_rules
  | `(⟦$rest,*⟧) =>
    buildMatVec (rest.getElems.toList.reverse.toChunks 2)
