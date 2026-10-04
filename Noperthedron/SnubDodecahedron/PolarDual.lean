module

public import Noperthedron.SnubDodecahedron.IcoInstance

@[expose] public section

/-!
# Facet poles

The polar dual of a polytope containing the origin in its interior has as
vertices the *poles* of its facet planes: the plane {x : ⟪x, y⟫ = 1} has
pole y. `facetPoles S` is the set of such y for the convex hull of a finite
set S: ⟪x, y⟫ ≤ 1 on S, with equality at three affinely independent points
of S. This file has the algebra used to determine that set exactly
(Statement.lean): Cramer's rule in the form `level_identity`, the uniqueness
of a pole (`eq_of_level`), the explicit `pole`, and the invariance of
`facetPoles` under orthogonal maps preserving S.
-/

namespace Noperthedron.SnubDodecahedron

open scoped RealInnerProductSpace Matrix

/-- The poles of the facet planes of the convex hull of `S`. -/
def facetPoles (S : Set ℝ³) : Set ℝ³ :=
  {y | (∀ x ∈ S, ⟪x, y⟫ ≤ 1) ∧ ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S,
    AffineIndependent ℝ ![a, b, c] ∧ ⟪a, y⟫ = 1 ∧ ⟪b, y⟫ = 1 ∧ ⟪c, y⟫ = 1}

/-- det(u, v, w) = ⟪u, v × w⟫, in coordinates. -/
def det3 (u v w : ℝ³) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

theorem inner_eq3 (x y : ℝ³) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three]
  ring

/-- Cramer's rule, dotted with y. -/
theorem cramer (a b c x y : ℝ³) :
    det3 a b c * ⟪x, y⟫ = det3 x b c * ⟪a, y⟫ + det3 a x c * ⟪b, y⟫ + det3 a b x * ⟪c, y⟫ := by
  simp only [inner_eq3, det3]
  ring

/-- If a, b, c are on the plane ⟪·, y⟫ = 1, then for every x,
det(a, b, c) (⟪x, y⟫ − 1) = det(b − a, c − a, x − a). -/
theorem level_identity {a b c x y : ℝ³} (ha : ⟪a, y⟫ = 1) (hb : ⟪b, y⟫ = 1) (hc : ⟪c, y⟫ = 1) :
    det3 a b c * (⟪x, y⟫ - 1) = det3 (b - a) (c - a) (x - a) := by
  have h := cramer a b c x y
  rw [ha, hb, hc] at h
  simp only [det3, PiLp.sub_apply] at h ⊢
  linear_combination h

/-- Points strictly on both sides of the plane through a, b, c rule out every
y with ⟪·, y⟫ = 1 on a, b, c and ≤ 1 on the two points. -/
theorem not_two_sided {a b c x₁ x₂ y : ℝ³} (ha : ⟪a, y⟫ = 1) (hb : ⟪b, y⟫ = 1)
    (hc : ⟪c, y⟫ = 1) (h₁ : ⟪x₁, y⟫ ≤ 1) (h₂ : ⟪x₂, y⟫ ≤ 1)
    (hd₁ : 0 < det3 (b - a) (c - a) (x₁ - a)) (hd₂ : det3 (b - a) (c - a) (x₂ - a) < 0) :
    False := by
  have e₁ := level_identity (x := x₁) ha hb hc
  have e₂ := level_identity (x := x₂) ha hb hc
  rcases le_or_gt 0 (det3 a b c) with hd | hd
  · have : det3 a b c * (⟪x₁, y⟫ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd (by linarith)
    linarith
  · have : 0 ≤ det3 a b c * (⟪x₂, y⟫ - 1) := mul_nonneg_of_nonpos_of_nonpos hd.le (by linarith)
    linarith

/-- A plane through three linearly independent points has one pole. -/
theorem eq_of_level {a b c y y' : ℝ³} (hd : det3 a b c ≠ 0) (ha : ⟪a, y⟫ = 1)
    (hb : ⟪b, y⟫ = 1) (hc : ⟪c, y⟫ = 1) (ha' : ⟪a, y'⟫ = 1) (hb' : ⟪b, y'⟫ = 1)
    (hc' : ⟪c, y'⟫ = 1) : y = y' := by
  have key : ∀ x, ⟪x, y⟫ = ⟪x, y'⟫ := by
    intro x
    have h₁ := cramer a b c x y
    have h₂ := cramer a b c x y'
    rw [ha, hb, hc] at h₁
    rw [ha', hb', hc'] at h₂
    exact mul_left_cancel₀ hd (h₁.trans h₂.symm)
  have h := key (y - y')
  rw [← sub_eq_zero, ← inner_sub_right, inner_self_eq_zero, sub_eq_zero] at h
  exact h

/-- The pole of the plane through a, b, c: (b × c + c × a + a × b) / det(a, b, c). -/
noncomputable def pole (a b c : ℝ³) : ℝ³ :=
  (det3 a b c)⁻¹ • WithLp.toLp 2 ![
    (b 1 * c 2 - b 2 * c 1) + (c 1 * a 2 - c 2 * a 1) + (a 1 * b 2 - a 2 * b 1),
    (b 2 * c 0 - b 0 * c 2) + (c 2 * a 0 - c 0 * a 2) + (a 2 * b 0 - a 0 * b 2),
    (b 0 * c 1 - b 1 * c 0) + (c 0 * a 1 - c 1 * a 0) + (a 0 * b 1 - a 1 * b 0)]

theorem pole_level {a b c : ℝ³} (hd : det3 a b c ≠ 0) :
    ⟪a, pole a b c⟫ = 1 ∧ ⟪b, pole a b c⟫ = 1 ∧ ⟪c, pole a b c⟫ = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [pole, inner_smul_right, inner_eq3, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [inv_mul_eq_one₀ hd]
    simp only [det3]
    ring

theorem affineIndependent_of_det {a b c : ℝ³} (hd : det3 a b c ≠ 0) :
    AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv i
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hv
  have hcoord : ∀ r, w 0 * a r + w 1 * b r + w 2 * c r = 0 := by
    intro r
    have := congrArg (fun v : ℝ³ => v r) hv
    simpa using this
  have h0 : w 0 * det3 a b c = 0 := by
    have := hcoord 0; have := hcoord 1; have := hcoord 2
    have e : w 0 * det3 a b c = det3 (w 0 • a + w 1 • b + w 2 • c) b c := by
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e, hv]; simp [det3]
  have h1 : w 1 * det3 a b c = 0 := by
    have e : w 1 * det3 a b c = det3 a (w 0 • a + w 1 • b + w 2 • c) c := by
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e, hv]; simp [det3]
  have h2 : w 2 * det3 a b c = 0 := by
    have e : w 2 * det3 a b c = det3 a b (w 0 • a + w 1 • b + w 2 • c) := by
      simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e, hv]; simp [det3]
  fin_cases i
  · exact (mul_eq_zero.mp h0).resolve_right hd
  · exact (mul_eq_zero.mp h1).resolve_right hd
  · exact (mul_eq_zero.mp h2).resolve_right hd

theorem inner_toEuclideanLin (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : ℝ³) :
    ⟪x, A.toEuclideanLin y⟫ = ⟪Aᵀ.toEuclideanLin x, y⟫ := by
  simp only [inner_eq3, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.transpose_apply, PiLp.toLp_apply, WithLp.ofLp_toLp]
  ring

/-- An orthogonal map preserving S (with its transpose) preserves its facet poles. -/
theorem facetPoles_map {S : Set ℝ³} {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ * G = 1)
    (hS : ∀ x ∈ S, G.toEuclideanLin x ∈ S) (hS' : ∀ x ∈ S, Gᵀ.toEuclideanLin x ∈ S)
    {y : ℝ³} (hy : y ∈ facetPoles S) : G.toEuclideanLin y ∈ facetPoles S := by
  obtain ⟨hle, a, ha, b, hb, c, hc, hind, hay, hby, hcy⟩ := hy
  have hpres : ∀ x, ⟪G.toEuclideanLin x, G.toEuclideanLin y⟫ = ⟪x, y⟫ := by
    intro x
    rw [inner_toEuclideanLin, ← IModel.toEuclideanLin_mul, hG]
    simp
  have hinj : Function.Injective G.toEuclideanLin := by
    intro u v huv
    have := congrArg Gᵀ.toEuclideanLin huv
    rwa [← IModel.toEuclideanLin_mul, ← IModel.toEuclideanLin_mul, hG, Matrix.toLpLin_one,
      LinearMap.id_apply, LinearMap.id_apply] at this
  refine ⟨fun x hx => ?_, G.toEuclideanLin a, hS a ha, G.toEuclideanLin b, hS b hb,
    G.toEuclideanLin c, hS c hc, ?_, by rw [hpres]; exact hay, by rw [hpres]; exact hby,
    by rw [hpres]; exact hcy⟩
  · rw [inner_toEuclideanLin]
    exact hle _ (hS' x hx)
  · have h := hind.map' (G.toEuclideanLin.toAffineMap) hinj
    have e : ![G.toEuclideanLin a, G.toEuclideanLin b, G.toEuclideanLin c] =
        (G.toEuclideanLin.toAffineMap) ∘ ![a, b, c] := by
      funext i
      fin_cases i <;> rfl
    rw [e]
    exact h

end Noperthedron.SnubDodecahedron
