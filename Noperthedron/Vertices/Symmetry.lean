module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic

public import Noperthedron.Vertices.Exact
public import Noperthedron.Local.Congruent

@[expose] public section


namespace Noperthedron

open Real

/-!
# Triangle symmetries

A finite collection of vertex-index permutations, each realized by a linear
isometry of ℝ³ on the triangles it is `applicable` to
(`congruent_of_apply`). The checker (`Row.ValidLocal.exists_symmetry`) uses
this to establish that the triangles `Pi` and `Qi` of a local row are
congruent.

Recall `exactVertex ⟨k, ℓ, i⟩ = (-1)^ℓ • Rz(2πk/15) (Cpt i)`, so the vertices
form three orbits of 30 (indexed by `i`), each generated from the base point
`Cpt i` by the z-rotation index `k` and the negation index `ℓ`.

* `rotation m n` sends `⟨k, ℓ, i⟩ ↦ ⟨k + n, ℓ + m, i⟩`, realized by
  `v ↦ (-1)^m • Rz(2πn/15) v` — a symmetry of the whole polyhedron, hence
  applicable to any triangle.
* `reflection m n` sends `⟨k, ℓ, i⟩ ↦ ⟨n - k, ℓ + m, i⟩`, realized by
  `v ↦ (-1)^m • Rz(2πn/15) (refl v)` where `refl` is the reflection across
  the vertical plane through the z-axis and `Cpt i`. That plane depends on
  the orbit `i`, so this is a different isometry for each orbit, and it maps
  vertices to vertices only within that orbit — hence a reflection is
  applicable only to triangles whose vertices all lie in a single orbit.

The constructor names describe the action on the 15-fold index
(`k ↦ k + n` vs `k ↦ n - k`), not orientation: e.g. `rotation 1 n` is
realized by the rotoreflection `-Rz(2πn/15)`.

The index permutations would form a group under composition
(≅ `ZMod 2 × DihedralGroup 15`), but we never need that structure, and the
realizing isometries do not assemble into a single action of it on ℝ³ (for
reflections the isometry depends on the triangle's orbit).
-/

inductive TriangleSymmetry where
  | rotation (m : ZMod 2) (n : ZMod 15)
  | reflection (m : ZMod 2) (n : ZMod 15)
deriving DecidableEq, Fintype, Repr, Nonempty

namespace TriangleSymmetry

/-- Apply a symmetry to a vertex index: `rotation m n` sends
`⟨k, ℓ, i⟩ ↦ ⟨k + n, ℓ + m, i⟩` and `reflection m n` sends
`⟨k, ℓ, i⟩ ↦ ⟨n - k, ℓ + m, i⟩`. For `reflection`, the result corresponds to
a linear isometry only on triangles all of whose vertices share the same
orbit `i`. -/
def apply : TriangleSymmetry → VertexIndex → VertexIndex
  | .rotation m n, ⟨k, ℓ, i⟩ =>
      ⟨⟨(k.val + n.val) % 15, Nat.mod_lt _ (by simp)⟩,
       ⟨(ℓ.val + m.val) % 2, Nat.mod_lt _ (by simp)⟩,
       i⟩
  | .reflection m n, ⟨k, ℓ, i⟩ =>
      ⟨⟨(15 - k.val + n.val) % 15, Nat.mod_lt _ (by simp)⟩,
       ⟨(ℓ.val + m.val) % 2, Nat.mod_lt _ (by simp)⟩,
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

private lemma int_neg_one_pow_smul (j : ℕ) (w : ℝ³) :
    (-1 : ℤ)^j • w = ((-1 : ℝ)^j) • w := by norm_cast

/-! ### Orbit reflection

For `(a, b) ≠ (0, 0)`, the reflection of ℝ³ across the vertical plane
containing the z-axis and the point `(a, b, 0)`, as a 3×3 orthogonal matrix. -/

noncomputable def orbitReflMat (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(a^2 - b^2) / (a^2 + b^2), 2 * a * b / (a^2 + b^2), 0;
     2 * a * b / (a^2 + b^2), (b^2 - a^2) / (a^2 + b^2), 0;
     0, 0, 1]

noncomputable def orbitReflL (a b : ℝ) : ℝ³ →L[ℝ] ℝ³ :=
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

/-- The key identity: `(a, b, c)` lies in the mirror plane of
`orbitReflL a b`, so it is fixed by the reflection, and reflecting reverses
the direction of rotation about the z-axis:
`refl (Rz θ v) = Rz (-θ) (refl v) = Rz (-θ) v` for `v = (a, b, c)`. -/
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

/-- A unit-|scalar| multiple of a norm-preserving linear map is norm-preserving. -/
private lemma norm_smul_apply_of_abs_eq_one {s : ℝ} (hs : |s| = 1)
    {L : ℝ³ →ₗ[ℝ] ℝ³} (hL : ∀ v, ‖L v‖ = ‖v‖) (v : ℝ³) : ‖(s • L) v‖ = ‖v‖ := by
  rw [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, hs, one_mul, hL]

/-- Shared closing step of the rotation/reflection congruence proofs: collect the
`(-1)^m` witness scalar and the vertex's `(-1)^ℓ` sign into a single mod-2 power. -/
private lemma neg_one_pow_mod_two_smul (m ℓ : ℕ) (w : ℝ³) :
    (-1 : ℤ) ^ ((ℓ + m) % 2) • w = (-1 : ℝ) ^ m • ((-1 : ℤ) ^ ℓ • w) := by
  rw [int_neg_one_pow_smul, int_neg_one_pow_smul, smul_smul, ← pow_add, add_comm m ℓ,
      ← neg_one_pow_eq_pow_mod_two]

/-- The rotation case: `⟨k, ℓ, i⟩ ↦ ⟨k + n, ℓ + m, i⟩` is realized by
`v ↦ (-1)^m • Rz(2πn/15) v`, the same linear isometry for every triangle. -/
private theorem congruent_of_rotation (Pi Qi : Fin 3 → VertexIndex)
    (m : ZMod 2) (n : ZMod 15)
    (hpq : ∀ j, Pi j = TriangleSymmetry.apply (.rotation m n) (Qi j)) :
    Local.Triangle.Congruent (exactVertex ∘ Pi) (exactVertex ∘ Qi) := by
  set s : ℝ := (-1 : ℝ)^m.val with hs_def
  set φ : ℝ := 2 * π * (n.val : ℝ) / 15 with hφ_def
  have hs_abs : |s| = 1 := abs_neg_one_pow m.val
  have hnorm : ∀ v : ℝ³, ‖(s • (RzL φ).toLinearMap) v‖ = ‖v‖ :=
    norm_smul_apply_of_abs_eq_one hs_abs (Bounding.Rz_preserves_norm φ)
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
  exact neg_one_pow_mod_two_smul m.val ℓ.val _

/-- The reflection case: on a triangle whose vertices all lie in orbit `i₀`,
`⟨k, ℓ, i₀⟩ ↦ ⟨n - k, ℓ + m, i₀⟩` is realized by the linear isometry
`v ↦ (-1)^m • Rz(2πn/15) (refl v)`, where `refl` is the reflection across the
vertical plane through the z-axis and `Cpt i₀`. -/
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
  have hs_abs : |s| = 1 := abs_neg_one_pow m.val
  have hnorm : ∀ v : ℝ³,
      ‖(s • ((RzL φ).toLinearMap ∘ₗ (orbitReflL a b).toLinearMap)) v‖ = ‖v‖ :=
    norm_smul_apply_of_abs_eq_one hs_abs fun v => by
      rw [LinearMap.comp_apply]
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
  exact neg_one_pow_mod_two_smul m.val ℓ.val _

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

end
