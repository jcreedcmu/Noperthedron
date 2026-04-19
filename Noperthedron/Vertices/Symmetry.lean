import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.ZMod.Basic

import Noperthedron.Vertices.Exact
import Noperthedron.Local.Congruent

namespace Noperthedron

open Real

/-!
# Triangle symmetries

A finite collection of vertex-index permutations, each of which corresponds to
a linear isometry of ℝ³ when applied to the triangles it is "applicable" to.

* `rotation m n` is a polyhedron-wide symmetry — applicable to any triangle.
* `reflection m n` is an orbit-restricted symmetry — only applicable to
  triangles whose three vertices share the same orbit index `i`.

There is no group structure here: the reflections are genuinely different
objects from the rotations, because the underlying linear isometry of ℝ³
depends on which orbit `i ∈ {0,1,2}` the triangle lives in.
-/

inductive TriangleSymmetry where
  | rotation (m : ZMod 2) (n : ZMod 15)
  | reflection (m : ZMod 2) (n : ZMod 15)
deriving DecidableEq, Fintype, Repr, Nonempty

namespace TriangleSymmetry

/-- Apply a symmetry to a vertex index. For `reflection`, the result is only
meaningful (corresponds to a linear isometry) when restricted to triangles all
of whose vertices share the same orbit `i`. -/
def apply : TriangleSymmetry → VertexIndex → VertexIndex
  | .rotation m n, ⟨k, ℓ, i⟩ =>
      ⟨⟨(k.val + n.val) % 15, Nat.mod_lt _ (by omega)⟩,
       ⟨(ℓ.val + m.val) % 2, Nat.mod_lt _ (by omega)⟩,
       i⟩
  | .reflection m n, ⟨k, ℓ, i⟩ =>
      ⟨⟨(15 - k.val + n.val) % 15, Nat.mod_lt _ (by omega)⟩,
       ⟨(ℓ.val + m.val) % 2, Nat.mod_lt _ (by omega)⟩,
       i⟩

/-- When the symmetry has a linear-isometry witness on a given triangle. -/
def applicable : TriangleSymmetry → (Fin 3 → VertexIndex) → Prop
  | .rotation _ _, _ => True
  | .reflection _ _, Q => (Q 0).i = (Q 1).i ∧ (Q 1).i = (Q 2).i

instance (s : TriangleSymmetry) (Q : Fin 3 → VertexIndex) : Decidable (s.applicable Q) := by
  cases s <;> unfold applicable <;> infer_instance

private lemma RzL_periodic (x : ℝ) (z : ℤ) : RzL (x + z * (2 * π)) = RzL x := by
  simp only [RzL, Rz_mat_add_int_mul_two_pi]

private lemma RzL_apply_add (α β : ℝ) (v : ℝ³) : RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

/-- The angle `2π * (x % 15) / 15` is equivalent to `2π * x / 15` for `RzL`
(they differ by an integer multiple of `2π`). -/
private lemma RzL_nat_mod_15 (x : ℕ) :
    RzL (2 * π * ((x % 15 : ℕ) : ℝ) / 15) = RzL (2 * π * (x : ℝ) / 15) := by
  have hreal : ((x % 15 : ℕ) : ℝ) + 15 * ((x / 15 : ℕ) : ℝ) = (x : ℝ) := by
    exact_mod_cast Nat.mod_add_div x 15
  have hcast : ((-((x / 15 : ℕ) : ℤ) : ℤ) : ℝ) = -((x / 15 : ℕ) : ℝ) := by
    push_cast; rfl
  rw [show 2 * π * ((x % 15 : ℕ) : ℝ) / 15
        = 2 * π * (x : ℝ) / 15 + ((-((x / 15 : ℕ) : ℤ) : ℤ) : ℝ) * (2 * π) by
      rw [hcast]; linear_combination (2 * π / 15) * hreal,
      RzL_periodic]

/-! ### Orbit reflection

For a vector `(a, b, _) ≠ 0` in the `xy`-plane, the reflection through the plane
containing the z-axis and `(a, b, 0)` is realized by a 3×3 orthogonal matrix. -/

private noncomputable def orbitReflMat (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(a^2 - b^2) / (a^2 + b^2), 2 * a * b / (a^2 + b^2), 0;
     2 * a * b / (a^2 + b^2), (b^2 - a^2) / (a^2 + b^2), 0;
     0, 0, 1]

private noncomputable def orbitReflL (a b : ℝ) : ℝ³ →L[ℝ] ℝ³ :=
  (orbitReflMat a b).toEuclideanLin.toContinuousLinearMap

private lemma orbitReflL_apply_coord (a b : ℝ) (w : ℝ³) :
    (orbitReflL a b w 0 = ((a^2 - b^2) * w 0 + 2 * a * b * w 1) / (a^2 + b^2))
    ∧ (orbitReflL a b w 1 = (2 * a * b * w 0 + (b^2 - a^2) * w 1) / (a^2 + b^2))
    ∧ (orbitReflL a b w 2 = w 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [orbitReflL, orbitReflMat, LinearMap.coe_toContinuousLinearMap',
        Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply,
        Matrix.vec3_dotProduct, Fin.isValue, Matrix.cons_val]; ring)

private lemma orbitReflL_preserves_norm (a b : ℝ) (hab : a^2 + b^2 ≠ 0) (w : ℝ³) :
    ‖orbitReflL a b w‖ = ‖w‖ := by
  suffices h : ‖orbitReflL a b w‖^2 = ‖w‖^2 by
    have h1 : 0 ≤ ‖orbitReflL a b w‖ := norm_nonneg _
    have h2 : 0 ≤ ‖w‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖orbitReflL a b w‖ - ‖w‖),
               sq_nonneg (‖orbitReflL a b w‖ + ‖w‖)]
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
  obtain ⟨h0, h1, h2⟩ := orbitReflL_apply_coord a b w
  rw [h0, h1, h2]
  field_simp
  ring

/-- The key identity: the orbit reflection applied to `RzL θ` of a vector
`(a, b, c)` (in its own orbit) yields `RzL (-θ)` of that vector. -/
private lemma orbitReflL_RzL_eq (a b c θ : ℝ) (hab : a^2 + b^2 ≠ 0) :
    orbitReflL a b (RzL θ !₂[a, b, c]) = RzL (-θ) !₂[a, b, c] := by
  -- Compute RzL θ !₂[a, b, c] componentwise.
  have hRz : ∀ α : ℝ, RzL α !₂[a, b, c] =
      !₂[a * Real.cos α - b * Real.sin α, a * Real.sin α + b * Real.cos α, c] := by
    intro α
    ext i
    simp only [RzL, Rz_mat, LinearMap.coe_toContinuousLinearMap',
      Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply,
      Matrix.vec3_dotProduct, Fin.isValue, Matrix.cons_val]
    fin_cases i <;> simp <;> ring
  rw [hRz θ, hRz (-θ), Real.cos_neg, Real.sin_neg]
  obtain ⟨h0, h1, h2⟩ := orbitReflL_apply_coord a b
    (!₂[a * Real.cos θ - b * Real.sin θ, a * Real.sin θ + b * Real.cos θ, c])
  ext i
  fin_cases i
  · rw [show (⟨0, by omega⟩ : Fin 3) = (0 : Fin 3) from rfl, h0]
    simp only [Matrix.cons_val, Fin.isValue]
    field_simp
    ring
  · rw [show (⟨1, by omega⟩ : Fin 3) = (1 : Fin 3) from rfl, h1]
    simp only [Matrix.cons_val, Fin.isValue]
    field_simp
    ring
  · rw [show (⟨2, by omega⟩ : Fin 3) = (2 : Fin 3) from rfl, h2]
    simp [Matrix.cons_val]

private lemma Cpt_eq_vec (i₀ : Fin 3) :
    Cpt i₀ = !₂[Cpt i₀ 0, Cpt i₀ 1, Cpt i₀ 2] := by
  ext j; fin_cases j <;> rfl

private lemma Cpt_xy_sq_pos (i₀ : Fin 3) : 0 < (Cpt i₀ 0)^2 + (Cpt i₀ 1)^2 := by
  fin_cases i₀ <;> simp [Cpt, C1R, C2R, C3R, C1, C2, C3] <;> norm_num

/-- The rotation case: the map `(k, ℓ, i) ↦ (k + n, ℓ + m, i)` corresponds to
`v ↦ (-1)^m • RzL(2π n / 15)(v)`, which is a polyhedron-wide linear isometry. -/
private theorem congruent_of_rotation (Pi Qi : Fin 3 → VertexIndex)
    (m : ZMod 2) (n : ZMod 15)
    (hpq : ∀ j, Pi j = TriangleSymmetry.apply (.rotation m n) (Qi j)) :
    Local.Triangle.Congruent (exactVertex ∘ Pi) (exactVertex ∘ Qi) := by
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
  show exactVertex (apply (.rotation m n) ⟨k, ℓ, i⟩)
      = (s • (RzL φ).toLinearMap) (exactVertex ⟨k, ℓ, i⟩)
  unfold apply
  simp only [exactVertex, LinearMap.smul_apply, ContinuousLinearMap.coe_coe]
  rw [(RzL φ).map_smul_of_tower]
  set θ : ℝ := 2 * π * (k.val : ℝ) / 15 with hθ_def
  rw [show 2 * π * (((⟨(k.val + n.val) % 15, Nat.mod_lt _ (by omega)⟩ : Fin 15).val : ℝ)) / 15
       = 2 * π * (((k.val + n.val) % 15 : ℕ) : ℝ) / 15 from rfl,
      RzL_nat_mod_15,
      show 2 * π * ((k.val + n.val : ℕ) : ℝ) / 15 = φ + θ by push_cast; rw [hφ_def, hθ_def]; ring,
      RzL_apply_add]
  set w := RzL φ (RzL θ (Cpt i))
  have cast_eq : ∀ (j : ℕ), (-1 : ℤ)^j • w = ((-1 : ℝ)^j) • w := fun j => by
    rw [← Int.cast_smul_eq_zsmul ℝ]; push_cast; rfl
  rw [cast_eq, cast_eq, hs_def, smul_smul, ← pow_add, add_comm m.val ℓ.val,
      ← neg_one_pow_eq_pow_mod_two]

/-- The reflection case: for a triangle with all three vertices in orbit `i₀`,
the map `(k, ℓ, i₀) ↦ (-k + n, ℓ + m, i₀)` corresponds to a linear isometry
of ℝ³ (the composition of `±I`, a rotation about `z`, and the reflection
through the plane spanned by `Cpt i₀` and the `z`-axis). -/
private theorem congruent_of_reflection (Pi Qi : Fin 3 → VertexIndex)
    (m : ZMod 2) (n : ZMod 15)
    (h_app : (Qi 0).i = (Qi 1).i ∧ (Qi 1).i = (Qi 2).i)
    (hpq : ∀ j, Pi j = TriangleSymmetry.apply (.reflection m n) (Qi j)) :
    Local.Triangle.Congruent (exactVertex ∘ Pi) (exactVertex ∘ Qi) := by
  set i₀ : Fin 3 := (Qi 0).i with hi₀
  have hQi_i : ∀ j, (Qi j).i = i₀ := by
    intro j
    fin_cases j
    · rfl
    · exact h_app.1.symm
    · exact h_app.2.symm.trans h_app.1.symm
  set a : ℝ := Cpt i₀ 0 with ha_def
  set b : ℝ := Cpt i₀ 1 with hb_def
  set c : ℝ := Cpt i₀ 2 with hc_def
  have hab : a ^ 2 + b ^ 2 ≠ 0 := ne_of_gt (Cpt_xy_sq_pos i₀)
  have hCpt_eq : Cpt i₀ = !₂[a, b, c] := Cpt_eq_vec i₀
  set s : ℝ := (-1 : ℝ) ^ m.val with hs_def
  set φ : ℝ := 2 * π * (n.val : ℝ) / 15 with hφ_def
  have hs_abs : |s| = 1 := by rw [hs_def, abs_pow, abs_neg, abs_one, one_pow]
  have hnorm : ∀ v : ℝ³,
      ‖(s • ((RzL φ).toLinearMap ∘ₗ (orbitReflL a b).toLinearMap)) v‖ = ‖v‖ := by
    intro v
    rw [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, hs_abs, one_mul,
        LinearMap.comp_apply]
    show ‖(RzL φ) ((orbitReflL a b) v)‖ = ‖v‖
    rw [Bounding.Rz_preserves_norm, orbitReflL_preserves_norm _ _ hab]
  refine ⟨⟨s • ((RzL φ).toLinearMap ∘ₗ (orbitReflL a b).toLinearMap), hnorm⟩, ?_⟩
  intro j
  have hij : (Qi j).i = i₀ := hQi_i j
  simp only [Function.comp_apply, hpq]
  rcases heq : Qi j with ⟨k, ℓ, i⟩
  rw [heq] at hij
  subst hij
  show exactVertex (apply (.reflection m n) ⟨k, ℓ, i₀⟩)
      = (s • ((RzL φ).toLinearMap ∘ₗ (orbitReflL a b).toLinearMap))
          (exactVertex ⟨k, ℓ, i₀⟩)
  unfold apply
  simp only [exactVertex, LinearMap.smul_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]
  rw [(orbitReflL a b).map_smul_of_tower]
  nth_rewrite 2 [hCpt_eq]
  rw [orbitReflL_RzL_eq _ _ _ _ hab, ← hCpt_eq,
      (RzL φ).map_smul_of_tower, ← RzL_apply_add]
  set θ : ℝ := 2 * π * (k.val : ℝ) / 15 with hθ_def
  have hk_le : k.val ≤ 15 := by omega
  rw [show 2 * π * (((⟨(15 - k.val + n.val) % 15, Nat.mod_lt _ (by omega)⟩ : Fin 15).val : ℝ))
          / 15
        = 2 * π * (((15 - k.val + n.val) % 15 : ℕ) : ℝ) / 15 from rfl,
      RzL_nat_mod_15,
      show 2 * π * ((15 - k.val + n.val : ℕ) : ℝ) / 15 = (φ + -θ) + (1 : ℤ) * (2 * π) by
        push_cast [Nat.cast_sub hk_le]; rw [hφ_def, hθ_def]; ring,
      RzL_periodic]
  set w := RzL (φ + -θ) (Cpt i₀) with hw_def
  have cast_eq : ∀ (j : ℕ), (-1 : ℤ)^j • w = ((-1 : ℝ)^j) • w := fun j => by
    rw [← Int.cast_smul_eq_zsmul ℝ]; push_cast; rfl
  rw [cast_eq, cast_eq, hs_def, smul_smul, ← pow_add, add_comm m.val ℓ.val,
      ← neg_one_pow_eq_pow_mod_two]

/-- Key theorem: whenever `Pi j = s.apply (Qi j)` for all `j` and the symmetry
is applicable to `Qi`, the triangles `Pi` and `Qi` are congruent. -/
theorem congruent_of_apply (s : TriangleSymmetry) (Pi Qi : Fin 3 → VertexIndex)
    (h_app : s.applicable Qi) (hpq : ∀ j, Pi j = s.apply (Qi j)) :
    Local.Triangle.Congruent (exactVertex ∘ Pi) (exactVertex ∘ Qi) := by
  cases s with
  | rotation m n => exact congruent_of_rotation Pi Qi m n hpq
  | reflection m n => exact congruent_of_reflection Pi Qi m n h_app hpq

end TriangleSymmetry

end Noperthedron
