import Mathlib.Analysis.InnerProductSpace.PiL2

namespace RationalApprox

notation "Euc(" n:arg ")" => EuclideanSpace ℝ (Fin n)

inductive MatVec : (n m : ℕ) → Type where
  | nil : {n : ℕ} → MatVec n n
  | cons : {n m p : ℕ} → (tl : MatVec n m) → (A B : (Euc(p) →L[ℝ] Euc(m))) → MatVec n p

@[simp]
noncomputable
def MatVec.maxNormList {n m : ℕ} (mv : MatVec n m) : List ℝ := match mv with
  | .nil => []
  | .cons tl A B => tl.maxNormList ++ [max (max ‖A‖ ‖B‖) 1]

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
def MatVec.size {n m : ℕ} (mv : MatVec n m) : ℕ :=
  match mv with
  | nil  => 0
  | cons tl _ _ => tl.size + 1

lemma norm_comp_a_le_prod_max_norm_list_prod
    {n m : ℕ} (mv : MatVec n m) :
    ‖mv.compA‖ ≤ mv.maxNormList.prod := by
  sorry

@[simp]
lemma MatVec.maxNormList_non_neg {m n : ℕ} (mv : MatVec n m) :
    0 ≤ mv.maxNormList.prod := by
  sorry

def norm_sub_le_prod {n m : ℕ} (mv : MatVec n m)
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

end RationalApprox
