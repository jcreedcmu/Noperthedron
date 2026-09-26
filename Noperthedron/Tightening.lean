module

public import Noperthedron.Rupert.Basic
public import Noperthedron.PoseClasses
public import Noperthedron.Basic
public import Noperthedron.PoseInterval
public import Noperthedron.PointSym
public import Mathlib.Algebra.Order.ToIntervalMod
public import Noperthedron.Vertices.Exact

@[expose] public section


open Real
namespace Noperthedron.Tightening

lemma rotation_preserves_nopert_vertices (x : ℝ³) (hx : x ∈ exactVerts) (k : ℤ) :
    RzC (2 * π * k / 15) x ∈ exactVerts := by
  simp only [exactVerts, exactVertex, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨⟨j, ℓ, i⟩, rfl⟩ := hx
  have hnn := Int.emod_nonneg ((j : ℤ) + k) (by norm_num : (15 : ℤ) ≠ 0)
  refine ⟨⟨⟨(((j : ℤ) + k) % 15).toNat, by omega⟩, ℓ, i⟩, ?_⟩
  rw [ContinuousLinearMap.map_smul_of_tower, ← RzC_coe, ← mul_apply_eq_comp,
    ← AddChar.map_add_eq_mul, RzC_coe, ← RzL_add_int_mul_two_pi (((j : ℤ) + k) / 15)]
  congr 3
  have h : ((((j : ℤ) + k) % 15 : ℤ) : ℝ) + 15 * ((((j : ℤ) + k) / 15 : ℤ) : ℝ) = j + k := by
    exact_mod_cast Int.emod_add_mul_ediv ((j : ℤ) + k) 15
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  linear_combination (2 * π / 15) * h

lemma nopert_vertices_rotation_invariant (k : ℤ) :
    (RzC (2 * π * k / 15)) '' exactVerts = exactVerts := by
  refine Set.Subset.antisymm ?_ fun x hx => ⟨RzC (2 * π * ((-k : ℤ) : ℝ) / 15) x,
    rotation_preserves_nopert_vertices x hx (-k), ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact rotation_preserves_nopert_vertices y hy k
  · rw [← mul_apply_eq_comp, ← AddChar.map_add_eq_mul,
      show 2 * π * k / 15 + 2 * π * ((-k : ℤ) : ℝ) / 15 = 0 by push_cast; ring,
      AddChar.map_zero_eq_one, one_apply_eq_self]

lemma exact_hull_image_eq_of_vertices_image_eq {f g : ℝ³ →L[ℝ] ℝ²}
    (h : f '' (exactVerts : Set ℝ³) = g '' (exactVerts : Set ℝ³)) :
    f '' exactPolyhedron.hull = g '' exactPolyhedron.hull := by
  rw [exactPolyhedron_hull]
  change (f : ℝ³ →ₗ[ℝ] ℝ²) '' convexHull ℝ (exactVerts : Set ℝ³) =
    (g : ℝ³ →ₗ[ℝ] ℝ²) '' convexHull ℝ (exactVerts : Set ℝ³)
  rw [LinearMap.image_convexHull, LinearMap.image_convexHull]
  simpa using congrArg (convexHull ℝ) h

/-- Precomposing a projection with a rotation by a multiple of `2π/15` does not change
the shadow it casts, since that rotation permutes the vertices. -/
lemma hull_image_eq_of_eq_comp_RzC {f g : ℝ³ →L[ℝ] ℝ²} (k : ℤ)
    (h : f = g ∘L RzC (2 * π * k / 15)) :
    f '' exactPolyhedron.hull = g '' exactPolyhedron.hull := by
  apply exact_hull_image_eq_of_vertices_image_eq
  rw [h, ContinuousLinearMap.coe_comp, Set.image_comp, nopert_vertices_rotation_invariant]

/-- Since the Noperthedron is point-symmetric, negating a projection does not change
the shadow it casts. -/
lemma neg_image_hull (f : ℝ³ →L[ℝ] ℝ²) :
    (-f) '' exactPolyhedron.hull = f '' exactPolyhedron.hull := by
  rw [show ⇑(-f) = (fun x => -x) ∘ ⇑f from funext fun _ => by simp, Set.image_comp]
  exact neg_image_eq_if_pointsym _
    (continuousLinearMap_preserves_point_sym f exactPolyhedron_point_symmetric)

/- [SY25] Lemma 7 -/

theorem lemma7_1_iterated {θ φ : ℝ} (k : ℤ) :
    (rotM (θ + k * (2 * π / 15)) φ) '' exactPolyhedron.hull =
      rotM θ φ '' exactPolyhedron.hull := by
  apply hull_image_eq_of_eq_comp_RzC (-k)
  have : RzL (-(θ + k * (2 * π / 15))) = RzL (-θ) ∘L RzC (2 * π * ((-k : ℤ) : ℝ) / 15) := by
    rw [← RzC_coe, ← ContinuousLinearMap.mul_def, ← AddChar.map_add_eq_mul]
    congr 1; push_cast; ring
  rw [rotM_identity, rotM_identity, this, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.comp_assoc]

theorem lemma7_1 (θ φ : ℝ) :
    (rotM (θ + 2/15*π) φ) '' exactPolyhedron.hull = rotM θ φ '' exactPolyhedron.hull := by
  rw [show θ + 2/15*π = θ + ((1 : ℤ) : ℝ) * (2 * π / 15) by push_cast; ring]
  exact lemma7_1_iterated 1

theorem lemma7_2 (θ φ α : ℝ) :
    (rotR (α + π) ∘ rotM θ φ) '' exactPolyhedron.hull = (rotR α ∘ rotM θ φ) '' exactPolyhedron.hull := by
  rw [rotR_add_pi_eq_neg_rotR]
  exact neg_image_hull (rotR α ∘L rotM θ φ)

theorem lemma7_2_iterated {θ φ α : ℝ} (k : ℤ) :
    (rotR (α + k * π) ∘L rotM θ φ) '' exactPolyhedron.hull =
      (rotR α ∘L rotM θ φ) '' exactPolyhedron.hull := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · rw [show α + ((2 * m : ℤ) : ℝ) * π = α + m * (2 * π) by push_cast; ring,
      rotR_add_int_mul_two_pi]
  · rw [show α + ((2 * m + 1 : ℤ) : ℝ) * π = (α + π) + m * (2 * π) by push_cast; ring,
      rotR_add_int_mul_two_pi, rotR_add_pi_eq_neg_rotR, ContinuousLinearMap.neg_comp,
      neg_image_hull]

lemma lemma7_3_calculation (θ φ : ℝ) :
    flip_y ∘L rotM θ φ = -(rotM (θ + π / 15) (π - φ) ∘L RzC (16 * π / 15)) := by
  obtain ⟨ψ, rfl⟩ : ∃ ψ, θ = ψ - π / 15 := ⟨θ + π / 15, by ring⟩
  rw [show 16 * π / 15 = π / 15 + π by ring, sub_add_cancel]
  ext v i
  fin_cases i <;> simp only [flip_y, flip_y_mat, rotM, rotM_mat, sin_sub, neg_sub, cos_sub,
    neg_add_rev, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
    Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    Matrix.cons_mulVec, Matrix.cons_dotProduct, Matrix.vecHead, Matrix.vecTail,
    Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, zero_mul, Matrix.dotProduct_of_isEmpty, add_zero, Matrix.empty_mulVec,
    Matrix.mulVec_cons, Matrix.mulVec_empty, Pi.add_apply, Pi.smul_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, smul_eq_mul, mul_one, Matrix.cons_val_one,
    mul_zero, cos_pi, neg_mul, one_mul, sin_pi, mul_neg, neg_neg, sub_neg_eq_add, zero_add, RzC,
    RzL, Rz_mat, AddChar.coe_mk, cos_add_pi, sin_add_pi, neg_apply, PiLp.neg_apply,
    Matrix.cons_val] <;> ring

theorem lemma7_3 (θ φ : ℝ) :
    (flip_y ∘L rotM θ φ) '' exactPolyhedron.hull = (rotM (θ + π / 15) (π - φ)) '' exactPolyhedron.hull := by
  rw [lemma7_3_calculation, neg_image_hull]
  exact hull_image_eq_of_eq_comp_RzC 8 (by congr 2; push_cast; ring)

lemma flip_rotR_swap_minus (α : ℝ) : flip_y ∘L rotR α = rotR (-α) ∘L flip_y := by
  unfold flip_y
  ext v i; fin_cases i <;> (simp [rotR]; ring_nf)

noncomputable
def flip_phi2 (p : Pose ℝ) : Pose ℝ := {
  θ₁ := p.θ₁ + π/15,
  φ₁ := π - p.φ₁,
  θ₂ := p.θ₂ + π/15,
  φ₂ := π - p.φ₂,
  α := -p.α,
}

theorem rupert_imp_flip_phi2_rupert2 {p : Pose ℝ} (r : RupertPose p exactPolyhedron.hull) :
    RupertPose (flip_phi2 p) exactPolyhedron.hull := by
  have hin : (rotR (-p.α) ∘L rotM (p.θ₁ + π / 15) (π - p.φ₁)) '' exactPolyhedron.hull =
      flip_y '' ((rotR p.α ∘L rotM p.θ₁ p.φ₁) '' exactPolyhedron.hull) := by
    rw [← Set.image_comp, ← ContinuousLinearMap.coe_comp, ← ContinuousLinearMap.comp_assoc,
      flip_rotR_swap_minus, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_comp, Set.image_comp, Set.image_comp, lemma7_3]
  have hout : rotM (p.θ₂ + π / 15) (π - p.φ₂) '' exactPolyhedron.hull =
      flip_y '' (rotM p.θ₂ p.φ₂ '' exactPolyhedron.hull) := by
    rw [← Set.image_comp, ← ContinuousLinearMap.coe_comp, lemma7_3]
  have hcl : ∀ s, closure (flip_y '' s) = flip_y '' closure s :=
    fun s => (flip_y_equiv.toHomeomorph.image_closure s).symm
  have hint : ∀ s, flip_y '' interior s = interior (flip_y '' s) :=
    flip_y_equiv.toHomeomorph.image_interior
  change closure ((rotR (-p.α) ∘L rotM (p.θ₁ + π / 15) (π - p.φ₁)) '' _) ⊆
    interior (rotM (p.θ₂ + π / 15) (π - p.φ₂) '' _)
  rw [hin, hout, hcl, ← hint]
  exact Set.image_mono r

/-- Any real number is, up to an integer multiple of `b`, in `[a, a + b)`. -/
lemma toIcoMod_eq_add_int_mul {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    toIcoMod hb a x = x + ((-toIcoDiv hb a x : ℤ) : ℝ) * b := by
  have := self_sub_toIcoMod_eq_mul hb a x
  push_cast
  linarith

/-- A pose casting the same inner and outer shadows of the Noperthedron as a Rupert
pose is itself a Rupert pose. Every tightening step below is an instance of this. -/
lemma rupert_of_shadows_eq {p q : Pose ℝ} (r : RupertPose p exactPolyhedron.hull)
    (hinner : (rotR q.α ∘L rotM q.θ₁ q.φ₁) '' exactPolyhedron.hull =
      (rotR p.α ∘L rotM p.θ₁ p.φ₁) '' exactPolyhedron.hull)
    (houter : rotM q.θ₂ q.φ₂ '' exactPolyhedron.hull = rotM p.θ₂ p.φ₂ '' exactPolyhedron.hull) :
    RupertPose q exactPolyhedron.hull := by
  change closure ((rotR q.α ∘L rotM q.θ₁ q.φ₁) '' _) ⊆ interior (rotM q.θ₂ q.φ₂ '' _)
  rw [hinner, houter]
  exact r

theorem tighten_φ₂ (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ φ₂ ∈ Set.Ico 0 (2 * π), RupertPose {p with φ₂} exactPolyhedron.hull := by
  refine ⟨toIcoMod two_pi_pos 0 p.φ₂, toIcoMod_mem_Ico' _ _, rupert_of_shadows_eq r rfl ?_⟩
  rw [toIcoMod_eq_add_int_mul, rotM_periodic_φ]

theorem tighten_φ₂_π (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull)
    (hφ₂ : p.φ₂ ∈ Set.Icc 0 (2 * π)) :
    ∃ θ₂ φ₂, φ₂ ∈ Set.Icc 0 π ∧ RupertPose {p with θ₂, φ₂} exactPolyhedron.hull := by
  by_cases h : p.φ₂ ≤ π
  · exact ⟨p.θ₂, p.φ₂, ⟨hφ₂.1, h⟩, by cases p; exact r⟩
  · refine ⟨p.θ₂ + π, 2 * π - p.φ₂, ⟨by linarith [hφ₂.2], by linarith⟩,
      rupert_of_shadows_eq r rfl ?_⟩
    rw [rotM_mod_eq_neg_rotM, neg_image_hull]

theorem tighten_φ₂_π2 (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull)
    (hφ₂ : p.φ₂ ∈ Set.Icc 0 π) :
    ∃ q : Pose ℝ, q.φ₂ ∈ Set.Icc 0 (π/2) ∧ RupertPose q exactPolyhedron.hull := by
  by_cases h : p.φ₂ < π / 2
  · exact ⟨p, ⟨hφ₂.1, le_of_lt h⟩, r⟩
  · exact ⟨flip_phi2 p, ⟨show 0 ≤ π - p.φ₂ by linarith [hφ₂.2], show π - p.φ₂ ≤ π / 2 by linarith⟩,
      rupert_imp_flip_phi2_rupert2 r⟩

theorem tighten_φ₁ (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ φ₁ ∈ Set.Ico 0 (2 * π), RupertPose {p with φ₁} exactPolyhedron.hull := by
  refine ⟨toIcoMod two_pi_pos 0 p.φ₁, toIcoMod_mem_Ico' _ _, rupert_of_shadows_eq r ?_ rfl⟩
  rw [toIcoMod_eq_add_int_mul, rotM_periodic_φ]

theorem tighten_φ₁_π (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull)
    (hφ₁ : p.φ₁ ∈ Set.Icc 0 (2 * π)) :
    ∃ θ₁ φ₁, φ₁ ∈ Set.Icc 0 π ∧ RupertPose {p with θ₁, φ₁} exactPolyhedron.hull := by
  by_cases h : p.φ₁ ≤ π
  · exact ⟨p.θ₁, p.φ₁, ⟨hφ₁.1, h⟩, by cases p; exact r⟩
  · refine ⟨p.θ₁ + π, 2 * π - p.φ₁, ⟨by linarith [hφ₁.2], by linarith⟩,
      rupert_of_shadows_eq r ?_ rfl⟩
    rw [rotM_mod_eq_neg_rotM, ContinuousLinearMap.comp_neg, neg_image_hull]

theorem tighten_θ (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ θ₁ ∈ Set.Ico 0 (2 * π / 15), ∃ θ₂ ∈ Set.Ico 0 (2 * π / 15),
      RupertPose {p with θ₁, θ₂} exactPolyhedron.hull := by
  have h15 : (0 : ℝ) < 2 * π / 15 := by positivity
  refine ⟨toIcoMod h15 0 p.θ₁, toIcoMod_mem_Ico' _ _, toIcoMod h15 0 p.θ₂, toIcoMod_mem_Ico' _ _,
    rupert_of_shadows_eq r ?_ ?_⟩
  · simp only [ContinuousLinearMap.coe_comp, Set.image_comp, toIcoMod_eq_add_int_mul,
      lemma7_1_iterated]
  · simp only [toIcoMod_eq_add_int_mul, lemma7_1_iterated]

theorem tighten_α (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ α ∈ Set.Icc (-(π/2)) (π/2), RupertPose {p with α} exactPolyhedron.hull := by
  have hmem := toIcoMod_mem_Ico pi_pos (-(π / 2)) p.α
  refine ⟨toIcoMod pi_pos (-(π / 2)) p.α, ⟨hmem.1, by linarith [hmem.2]⟩,
    rupert_of_shadows_eq r ?_ rfl⟩
  rw [toIcoMod_eq_add_int_mul, lemma7_2_iterated]

-- [SY25] Corollary 8 (§2.2)
-- This is a piece that relies on symmetry of the Noperthedron
theorem rupert_tightening (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ p' : Pose ℝ, tightInterval.contains p' ∧ RupertPose p' exactPolyhedron.hull := by
  obtain ⟨φ₂, hφ₂, r⟩ := tighten_φ₂ p r
  obtain ⟨θ₂, φ₂', hφ₂', r⟩ := tighten_φ₂_π _ r (Set.Ico_subset_Icc_self hφ₂)
  obtain ⟨q, hqφ₂, r⟩ := tighten_φ₂_π2 _ r hφ₂'
  obtain ⟨φ₁, hφ₁, r⟩ := tighten_φ₁ q r
  obtain ⟨θ₁, φ₁', hφ₁', r⟩ := tighten_φ₁_π _ r (Set.Ico_subset_Icc_self hφ₁)
  obtain ⟨θ₁', hθ₁, θ₂', hθ₂, r⟩ := tighten_θ _ r
  obtain ⟨α, hα, r⟩ := tighten_α _ r
  refine ⟨_, ?_, r⟩
  exact PoseInterval.contains_iff_components.mpr
    ⟨Set.Ico_subset_Icc_self hθ₁, Set.Ico_subset_Icc_self hθ₂, hφ₁', hqφ₂, hα⟩

end Tightening
end Noperthedron

end
