import Noperthedron.Basic
import Noperthedron.Bounding.OpNorm
import Noperthedron.Bounding.RaRa

namespace Bounding

theorem norm_RxRy_minus_id_le_wlog {d d' : Fin 3} {α β : ℝ} :
    d ≠ d' → |α| ≤ 2 → |β| ≤ 2 → ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α^2 + β^2) := by
  sorry

namespace PreferComp
  variable {R A B C : Type*}
  variable [Semiring R]
  variable [AddCommMonoid A] [Module R A] [TopologicalSpace A]
  variable [AddCommMonoid B] [Module R B] [TopologicalSpace B]
  variable [AddCommMonoid C] [Module R C] [TopologicalSpace C]
  def mul_eq_comp {f g : A →L[R] A} : g * f = g ∘L f := by rfl
  @[simp] def comp_image S (g : B →L[R] C) (f : A →L[R] B) : ⇑(g ∘L f) '' S = ⇑g '' (⇑f '' S) := by ext p; simp
end PreferComp

open PreferComp

theorem lemma12_2a {d d' : Fin 3} {α β : ℝ} (dne : d ≠ d') :
    ‖(rot3 d (2 * α)) ∘L (rot3 d' (2 * β)) - (rot3 d α) ∘L (rot3 d' β)‖  =
        ‖((rot3 d α) ∘L (rot3 d α)) ∘L ((rot3 d' β) ∘L (rot3 d' β)) - (rot3 d α) ∘L (rot3 d' β)‖  := by
  fin_cases d, d' <;> {
    try contradiction
    try simp only [rot3]
    try repeat rw [two_mul, AddChar.map_add_eq_mul, mul_eq_comp]
  }

theorem lemma12_2 {d d' : Fin 3} {α β : ℝ} :
    d ≠ d' → ‖rot3 d (2 * α) ∘L rot3 d' (2 * β) - 1‖ ≤ 2 * ‖rot3 d α ∘L rot3 d' β - 1‖ := by
    intro d_ne_d'
    calc
    _ = ‖(rot3 d (2 * α) ∘L rot3 d' (2 * β) - rot3 d α ∘L rot3 d' β) + (rot3 d α ∘L rot3 d' β - 1)‖ := by simp
    _ ≤ ‖rot3 d (2 * α) ∘L rot3 d' (2 * β) - rot3 d α ∘L rot3 d' β‖ + ‖rot3 d α ∘L rot3 d' β - 1‖ := by apply norm_add_le
    _ = ‖(rot3 d α ∘L rot3 d α) ∘L (rot3 d' β ∘L rot3 d' β) - rot3 d α ∘L rot3 d' β‖ + ‖rot3 d α ∘L rot3 d' β - 1‖ := by rw [lemma12_2a d_ne_d']
    _ ≤ ‖rot3 d α ∘L rot3 d' β - 1‖ + ‖rot3 d α ∘L rot3 d' β - 1‖ := by
      gcongr 1
      calc
        _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β) ∘L rot3 d' β - rot3 d α ∘L rot3 d' β‖ := by congr 1
        _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β) ∘L rot3 d' β - rot3 d α ∘L 1 ∘L rot3 d' β‖ := by congr 1
        _ = ‖rot3 d α ∘L (rot3 d α ∘L rot3 d' β - 1) ∘L rot3 d' β‖ := by simp
        _ ≤ ‖(rot3 d α ∘L rot3 d' β - 1)‖ := by
          repeat grw [ContinuousLinearMap.opNorm_comp_le]
          repeat rw [lemma9]
          simp
    _ = 2 * ‖rot3 d α ∘L rot3 d' β - 1‖ := by ring

theorem lemma12_3 {d d' : Fin 3} {α β : ℝ} (n : ℕ) (d_ne_d' : d ≠ d') (α_in : |α| ≤ 2^(n+1)) (β_in : |β| ≤ 2^(n+1)) :
  ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α^2 + β^2) := by
    induction n generalizing α β with
    | zero => apply norm_RxRy_minus_id_le_wlog <;> grind
    | succ n' h =>
      calc ‖rot3 d α ∘L rot3 d' β - 1‖
        _ = ‖rot3 d (2 * (α / 2)) ∘L rot3 d' (2 * (β / 2)) - 1‖ := by
          field_simp
        _ ≤ 2 * ‖rot3 d (α / 2) ∘L rot3 d' (β / 2) - 1‖ := lemma12_2 d_ne_d'
        _ ≤ 2 * √((α / 2)^2 + (β / 2)^2) := by
          grw [h] <;> {
            simp only [abs_div, Nat.abs_ofNat]
            field_simp
            rw [pow_succ'] at α_in β_in
            assumption
          }
        _ = √(α^2 + β^2) := by
          field_simp
          rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by norm_num)]
          field_simp

theorem lemma12 {d d' : Fin 3} {α β : ℝ} (d_ne_d' : d ≠ d') :
  ‖rot3 d α ∘L rot3 d' β - 1‖ ≤ √(α^2 + β^2) := by
    let n : ℕ := Nat.clog 2 ⌈max |α| |β|⌉₊
    apply lemma12_3 n d_ne_d' <;> {
      unfold n
      rw [← Real.rpow_natCast, Nat.cast_add]
      simp only [Nat.cast_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Real.rpow_add_one,
        Real.rpow_natCast]
      calc
        _ ≤ max |α| |β| := by simp
        _ ≤ ⌈max |α| |β|⌉₊ := by apply Nat.le_ceil
        _ = ⌈max |α| |β|⌉₊ * 1 := by simp
        _ ≤ ⌈max |α| |β|⌉₊ * 2 := by gcongr; simp
        _ ≤ (2 ^ (Nat.clog 2 ⌈max |α| |β|⌉₊) : ℕ) * 2 := by
          gcongr
          apply Nat.le_pow_clog
          simp
        _ ≤ 2 ^ (Nat.clog 2 ⌈max |α| |β|⌉₊) * 2 := by simp
    }

end Bounding
