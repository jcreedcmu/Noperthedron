import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic

import Noperthedron.Vertices.Exact
import Noperthedron.Local.Congruent

namespace Noperthedron

open Real

abbrev SymmetryGroup := Multiplicative (ZMod 2 × ZMod 15)

instance : MulAction SymmetryGroup VertexIndex where
  smul g j :=
    ⟨⟨(j.k.val + ((Multiplicative.toAdd g).2).val) % 15, Nat.mod_lt _ (by omega)⟩,
     ⟨(j.ℓ.val + ((Multiplicative.toAdd g).1).val) % 2, Nat.mod_lt _ (by omega)⟩,
     j.i⟩
  one_smul := by
    rintro ⟨k, ℓ, i⟩
    show (⟨⟨(k.val + ((Multiplicative.toAdd (1 : SymmetryGroup)).2).val) % 15,
            Nat.mod_lt _ (by omega)⟩,
           ⟨(ℓ.val + ((Multiplicative.toAdd (1 : SymmetryGroup)).1).val) % 2,
            Nat.mod_lt _ (by omega)⟩,
           i⟩ : VertexIndex) = ⟨k, ℓ, i⟩
    refine VertexIndex.mk.injEq .. |>.mpr ⟨?_, ?_, rfl⟩
    · apply Fin.val_injective
      show (k.val + ((Multiplicative.toAdd (1 : SymmetryGroup)).2).val) % 15 = k.val
      rw [toAdd_one]
      show (k.val + ((0 : ZMod 2 × ZMod 15).2).val) % 15 = k.val
      simp [ZMod.val_zero, Nat.mod_eq_of_lt k.is_lt]
    · apply Fin.val_injective
      show (ℓ.val + ((Multiplicative.toAdd (1 : SymmetryGroup)).1).val) % 2 = ℓ.val
      rw [toAdd_one]
      show (ℓ.val + ((0 : ZMod 2 × ZMod 15).1).val) % 2 = ℓ.val
      simp [ZMod.val_zero, Nat.mod_eq_of_lt ℓ.is_lt]
  mul_smul := by
    rintro g h ⟨k, ℓ, i⟩
    show (⟨⟨(k.val + ((Multiplicative.toAdd (g * h)).2).val) % 15,
            Nat.mod_lt _ (by omega)⟩,
           ⟨(ℓ.val + ((Multiplicative.toAdd (g * h)).1).val) % 2,
            Nat.mod_lt _ (by omega)⟩,
           i⟩ : VertexIndex) =
         ⟨⟨((k.val + ((Multiplicative.toAdd h).2).val) % 15 + ((Multiplicative.toAdd g).2).val) % 15,
            Nat.mod_lt _ (by omega)⟩,
          ⟨((ℓ.val + ((Multiplicative.toAdd h).1).val) % 2 + ((Multiplicative.toAdd g).1).val) % 2,
            Nat.mod_lt _ (by omega)⟩,
          i⟩
    refine VertexIndex.mk.injEq .. |>.mpr ⟨?_, ?_, rfl⟩
    · apply Fin.val_injective
      show (k.val + ((Multiplicative.toAdd (g * h)).2).val) % 15 =
           ((k.val + ((Multiplicative.toAdd h).2).val) % 15 + ((Multiplicative.toAdd g).2).val) % 15
      rw [toAdd_mul]
      show (k.val + ((Multiplicative.toAdd g + Multiplicative.toAdd h).2).val) % 15 = _
      rw [Prod.snd_add, ZMod.val_add]
      omega
    · apply Fin.val_injective
      show (ℓ.val + ((Multiplicative.toAdd (g * h)).1).val) % 2 =
           ((ℓ.val + ((Multiplicative.toAdd h).1).val) % 2 + ((Multiplicative.toAdd g).1).val) % 2
      rw [toAdd_mul]
      show (ℓ.val + ((Multiplicative.toAdd g + Multiplicative.toAdd h).1).val) % 2 = _
      rw [Prod.fst_add, ZMod.val_add]
      omega

private lemma RzL_periodic (x : ℝ) (z : ℤ) : RzL (x + z * (2 * π)) = RzL x := by
  simp only [RzL, Rz_mat_add_int_mul_two_pi]

private lemma RzL_apply_add (α β : ℝ) (v : ℝ³) : RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

theorem congruent_of_rotated (Pi Qi : Fin 3 → VertexIndex) (g : SymmetryGroup)
    (hpq : ∀ j, Pi j = g • Qi j) :
    Local.Triangle.Congruent (exactVertex ∘ Pi) (exactVertex ∘ Qi) := by
  set m : ZMod 2 := (Multiplicative.toAdd g).1 with hm_def
  set n : ZMod 15 := (Multiplicative.toAdd g).2 with hn_def
  set s : ℝ := (-1 : ℝ)^m.val with hs_def
  set φ : ℝ := 2 * π * (n.val : ℝ) / 15 with hφ_def
  have hs_abs : |s| = 1 := by
    rw [hs_def, abs_pow, abs_neg, abs_one, one_pow]
  have hnorm : ∀ v : ℝ³, ‖(s • (RzL φ).toLinearMap) v‖ = ‖v‖ := by
    intro v
    rw [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, hs_abs, one_mul]
    exact Bounding.Rz_preserves_norm φ v
  refine ⟨⟨s • (RzL φ).toLinearMap, hnorm⟩, ?_⟩
  intro j
  simp only [Function.comp_apply, hpq]
  obtain ⟨k, ℓ, i⟩ := Qi j
  show exactVertex ⟨⟨(k.val + n.val) % 15, Nat.mod_lt _ (by omega)⟩,
                   ⟨(ℓ.val + m.val) % 2, Nat.mod_lt _ (by omega)⟩,
                   i⟩
      = (s • (RzL φ).toLinearMap) (exactVertex ⟨k, ℓ, i⟩)
  simp only [exactVertex]
  rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, (RzL φ).map_smul_of_tower]
  set θ : ℝ := 2 * π * (k.val : ℝ) / 15 with hθ_def
  set z : ℤ := -((k.val + n.val) / 15 : ℕ) with hz_def
  have h_eq : 2 * π * (((⟨(k.val + n.val) % 15, Nat.mod_lt _ (by omega)⟩ : Fin 15).val : ℝ)) / 15
            = (φ + θ) + (z : ℝ) * (2 * π) := by
    show 2 * π * (((k.val + n.val) % 15 : ℕ) : ℝ) / 15 = _
    have hnat : (k.val + n.val) % 15 + 15 * ((k.val + n.val) / 15) = k.val + n.val := by omega
    have hreal : (((k.val + n.val) % 15 : ℕ) : ℝ) +
                  15 * (((k.val + n.val) / 15 : ℕ) : ℝ) =
                  (k.val : ℝ) + (n.val : ℝ) := by exact_mod_cast hnat
    simp only [hz_def, Int.cast_neg, Int.cast_natCast, hφ_def, hθ_def]
    field_simp
    linarith [hreal]
  rw [h_eq, RzL_periodic, RzL_apply_add]
  set w := RzL φ (RzL θ (Cpt i))
  have cast_eq : ∀ (j : ℕ), (-1 : ℤ)^j • w = ((-1 : ℝ)^j) • w := fun j => by
    rw [← Int.cast_smul_eq_zsmul ℝ]; push_cast; rfl
  rw [cast_eq, cast_eq, hs_def, smul_smul, ← pow_add, add_comm m.val ℓ.val,
      ← neg_one_pow_eq_pow_mod_two]
