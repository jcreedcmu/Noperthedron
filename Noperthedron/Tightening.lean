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
  simp only [exactVerts, exactVertex,
    Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨⟨k, ℓ, i⟩, hb⟩ := hx
  rename_i K
  subst hb
  simp only [exactVerts, exactVertex, Finset.mem_image, Finset.mem_univ, true_and]
  rw [ContinuousLinearMap.map_smul_of_tower]
  simp only [← RzC_coe, ← mul_apply_eq_comp, ← AddChar.map_add_eq_mul RzC]
  refine ⟨⟨⟨(((↑↑k : ℤ) + K) % 15).toNat, by omega⟩, ℓ, i⟩, ?_⟩
  congr 1
  simp only [RzC, RzL, AddChar.coe_mk]
  congr 1; congr 1
  rw [← Rz_mat_add_int_mul_two_pi ((↑↑k + K) / 15)]
  congr 1; congr 1
  have hnn := Int.emod_nonneg (↑↑k + K) (show (15 : ℤ) ≠ 0 by simp)
  field_simp
  norm_cast
  rw [Int.toNat_of_nonneg hnn]
  omega

lemma nopert_vertices_rotation_invariant (k : ℤ) :
    (RzC (2 * π * k / 15)) '' exactVerts = exactVerts := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact rotation_preserves_nopert_vertices y hy k
  · intro hx
    simp_all only [Set.mem_image, SetLike.mem_coe]
    use (RzC (2 * π * -k / 15) x)
    refine ⟨?_, ?_⟩
    · have q := rotation_preserves_nopert_vertices x hx (-k)
      push_cast at q
      ring_nf at q ⊢
      exact q
    · change (RzC (2 * π * ↑k / 15) * (RzC (2 * π * -↑k / 15))) x = x
      rw [← AddChar.map_add_eq_mul RzC]
      ring_nf; simp

lemma exact_hull_image_eq_of_vertices_image_eq {f g : ℝ³ →L[ℝ] ℝ²}
    (h : f '' (exactVerts : Set ℝ³) = g '' (exactVerts : Set ℝ³)) :
    f '' exactPolyhedron.hull = g '' exactPolyhedron.hull := by
  rw [exactPolyhedron_hull]
  change (f : ℝ³ →ₗ[ℝ] ℝ²) '' convexHull ℝ (exactVerts : Set ℝ³) =
    (g : ℝ³ →ₗ[ℝ] ℝ²) '' convexHull ℝ (exactVerts : Set ℝ³)
  rw [LinearMap.image_convexHull, LinearMap.image_convexHull]
  simpa using congrArg (convexHull ℝ) h

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
  apply exact_hull_image_eq_of_vertices_image_eq
  suffices h : (RzL (-(θ + k * (2 * π / 15)))) '' exactVerts = (RzL (-θ)) '' exactVerts by
    repeat rw [rotM_identity]
    push_cast
    repeat rw [Set.image_comp]
    rw [h]
  change (RzC (-(θ + k * (2 * π / 15)))) '' exactVerts = (RzC (-θ)) '' exactVerts
  rw [show -(θ + k * (2 * π / 15)) = -θ + 2 * π * ((-k : ℤ) : ℝ) / 15 by push_cast; ring,
    AddChar.map_add_eq_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.coe_comp,
    Set.image_comp, nopert_vertices_rotation_invariant]

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
  induction k using Int.induction_on with
  | zero => simp
  | succ n hn =>
    rw [← hn]; push_cast
    have := lemma7_2 θ φ (α + n * π)
    ring_nf at this ⊢
    rw [← this]
  | pred n hn =>
    rw [← hn]; push_cast
    have := lemma7_2 θ φ  (α + (-1 - n) * π)
    ring_nf at this ⊢
    rw [← this]

lemma lemma7_3_calculation (θ φ : ℝ) (v : ℝ³) :
    flip_y (rotM θ φ v) = - rotM (θ + π / 15) (π - φ) (RzC (16 * π / 15) v) := by
  simp only [flip_y, flip_y_mat, rotM, RzC, rotM_mat]
  ext i
  simp only [neg_mul, LinearMap.coe_toContinuousLinearMap',
    Function.comp_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.cons_mulVec,
    Matrix.cons_dotProduct, Matrix.vecHead, Fin.isValue, Matrix.vecTail, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, zero_mul,
    Matrix.dotProduct_of_isEmpty, add_zero, Matrix.empty_mulVec, Matrix.mulVec_cons,
    Matrix.mulVec_empty, Pi.add_apply, Pi.smul_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, smul_eq_mul, Matrix.cons_val_one, cos_pi_sub, mul_neg, neg_neg,
    sin_pi_sub, RzL, Rz_mat, AddChar.coe_mk, PiLp.neg_apply, one_mul, zero_add, Matrix.cons_val,
    neg_add_rev]
  have h0 : sin θ = sin (16 * π / 15) * cos (θ + π / 15) - cos (16 * π / 15) * sin (θ + π / 15) := calc
    sin θ
    _ = sin (-θ + π) := by simp
    _ = sin ((- (θ + π / 15)) + (16 * π / 15)) := by ring_nf
    _ = sin (16 * π / 15) * cos (- (θ + π / 15)) + cos (16 * π / 15) * sin (- (θ + π / 15)) := by
      rw [sin_add]; ring_nf
    _ = sin (16 * π / 15) * cos (θ + π / 15) - cos (16 * π / 15) * sin (θ + π / 15) := by
      rw [sin_neg, cos_neg]; ring_nf

  have h1 : cos θ = -cos (16 * π / 15) * cos (θ + π / 15) - sin (16 * π / 15) * sin (θ + π / 15) := calc
    cos θ
    _ = -(cos (θ - π)) := by simp
    _ = -(cos (-(16 * π / 15) + (θ + π / 15))) := by ring_nf
    _ = -cos (-(16 * π / 15)) * cos (θ + π / 15) + sin (- (16 * π / 15)) * sin (θ + π / 15) := by
      rw [cos_add]; ring_nf
    _ = -cos (16 * π / 15) * cos (θ + π / 15) - sin (16 * π / 15) * sin (θ + π / 15) := by
      rw [sin_neg, cos_neg]; ring_nf

  fin_cases i
  · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, mul_one, mul_zero, add_zero,
    neg_zero, zero_add, mul_neg, neg_neg]
    rw [h0, h1]
    ring_nf
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, mul_zero, mul_neg, mul_one,
    neg_add_rev, neg_neg, zero_add];
    nth_rw 1 [h0, h1]
    ring_nf

lemma neg_lin_eq_lin_neg (f : ℝ³ →L[ℝ] ℝ²) : ⇑(-f) = f ∘ (fun x => -x) := by ext; simp

theorem lemma7_3 (θ φ : ℝ) :
    (flip_y ∘L rotM θ φ) '' exactPolyhedron.hull = (rotM (θ + π / 15) (π - φ)) '' exactPolyhedron.hull := by
  apply exact_hull_image_eq_of_vertices_image_eq
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, lemma7_3_calculation]
  have h1 : (fun a ↦ -(rotM (θ + π / 15) (π - φ)) ((RzC (16 * π / 15)) a)) =
    (fun a ↦ -(rotM (θ + π / 15) (π - φ)) a) ∘ (RzC (16 * π / 15)) := rfl
  have h2 : (rotM (θ + π / 15) (π - φ)) '' ↑exactVerts =
      (-rotM (θ + π / 15) (π - φ)) '' ↑exactVerts := by
    rw [neg_lin_eq_lin_neg (rotM (θ + π / 15) (π - φ)), Set.image_comp]
    congr
    rw [neg_image_eq_if_pointsym]
    exact exactVerts_pointsym
  rw [h2, h1, Set.image_comp]
  congr
  convert_to (RzC (2 * π * ↑8 / 15)) '' ↑exactVerts = ↑exactVerts
  · ring_nf
  exact nopert_vertices_rotation_invariant 8

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
  simp_all only [RupertPose, Pose.inner_shadow_eq_RM, Pose.outer_shadow_eq_M]
  let fh := flip_y_equiv.toHomeomorph
  calc closure ((rotR (-p.α) ∘ rotM (p.θ₁ + π / 15) (π - p.φ₁)) '' exactPolyhedron.hull)
    _ = closure (rotR (-p.α) '' ((flip_y ∘L p.rotM₁) '' exactPolyhedron.hull)) := by rw [Set.image_comp, ← lemma7_3]; rfl
    _ = closure (((rotR (-p.α) ∘L flip_y) ∘L p.rotM₁) '' exactPolyhedron.hull) := by rw [← Set.image_comp]; rfl
    _ = closure (((flip_y ∘ (p.rotR ∘L p.rotM₁))) '' exactPolyhedron.hull) := by rw [← flip_rotR_swap_minus]; rfl
    _ = closure (flip_y '' ((p.rotR ∘L p.rotM₁) '' exactPolyhedron.hull)) := by rw [Set.image_comp]
    _ = flip_y '' closure ((p.rotR ∘L p.rotM₁) '' exactPolyhedron.hull) := fh.image_closure _ |>.symm
    _ ⊆ flip_y '' interior (p.rotM₂ '' exactPolyhedron.hull) := Set.image_mono r
    _ = interior (flip_y '' (p.rotM₂ '' exactPolyhedron.hull)) := fh.image_interior _
    _ = interior ((flip_y ∘L rotM p.θ₂ p.φ₂) '' exactPolyhedron.hull) := by rw [← Set.image_comp]; rfl
    _ = interior ((rotM (p.θ₂ + π / 15) (π - p.φ₂)) '' exactPolyhedron.hull) := by rw [lemma7_3]

/-- Any real number is, up to an integer multiple of `b`, in `[a, a + b)`. -/
lemma toIcoMod_eq_add_int_mul {b : ℝ} (hb : 0 < b) (a x : ℝ) :
    toIcoMod hb a x = x + ((-toIcoDiv hb a x : ℤ) : ℝ) * b := by
  have := self_sub_toIcoMod_eq_mul hb a x
  push_cast
  linarith

/-- A pose casting the same inner and outer shadows of the Noperthedron as a Rupert
pose is itself a Rupert pose. Every tightening step below is an instance of this. -/
lemma rupert_of_shadows_eq {p q : Pose ℝ} (r : RupertPose p exactPolyhedron.hull)
    (hinner : (q.rotR ∘L q.rotM₁) '' exactPolyhedron.hull =
      (p.rotR ∘L p.rotM₁) '' exactPolyhedron.hull)
    (houter : q.rotM₂ '' exactPolyhedron.hull = p.rotM₂ '' exactPolyhedron.hull) :
    RupertPose q exactPolyhedron.hull := by
  change closure ((q.rotR ∘L q.rotM₁) '' _) ⊆ interior (q.rotM₂ '' _)
  rw [hinner, houter]
  exact r

theorem tighten_φ₂ (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ φ₂ ∈ Set.Ico 0 (2 * π), RupertPose {p with φ₂} exactPolyhedron.hull := by
  refine ⟨toIcoMod two_pi_pos 0 p.φ₂, toIcoMod_mem_Ico' _ _, rupert_of_shadows_eq r rfl ?_⟩
  change rotM p.θ₂ (toIcoMod two_pi_pos 0 p.φ₂) '' _ = rotM p.θ₂ p.φ₂ '' _
  rw [toIcoMod_eq_add_int_mul, rotM_periodic_φ]

theorem tighten_φ₂_π (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull)
    (hφ₂ : p.φ₂ ∈ Set.Icc 0 (2 * π)) :
    ∃ θ₂ φ₂, φ₂ ∈ Set.Icc 0 π ∧ RupertPose {p with θ₂, φ₂} exactPolyhedron.hull := by
  by_cases h : p.φ₂ ≤ π
  · exact ⟨p.θ₂, p.φ₂, ⟨hφ₂.1, h⟩, by cases p; exact r⟩
  · refine ⟨p.θ₂ + π, 2 * π - p.φ₂, ⟨by linarith [hφ₂.2], by linarith⟩,
      rupert_of_shadows_eq r rfl ?_⟩
    change rotM (p.θ₂ + π) (2 * π - p.φ₂) '' _ = rotM p.θ₂ p.φ₂ '' _
    rw [rotM_mod_eq_neg_rotM, neg_image_hull]

theorem tighten_φ₂_π2 (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull)
    (hφ₂ : p.φ₂ ∈ Set.Icc 0 π) :
    ∃ q : Pose ℝ, q.φ₂ ∈ Set.Icc 0 (π/2) ∧ RupertPose q exactPolyhedron.hull := by
  by_cases h : p.φ₂ < π / 2
  · exact ⟨p, ⟨hφ₂.1, le_of_lt h⟩, r⟩
  · use flip_phi2 p
    constructor
    · simp only [flip_phi2, Set.mem_Icc, sub_nonneg, tsub_le_iff_right]; grind
    · exact rupert_imp_flip_phi2_rupert2 r

theorem tighten_φ₁ (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ φ₁ ∈ Set.Ico 0 (2 * π), RupertPose {p with φ₁} exactPolyhedron.hull := by
  refine ⟨toIcoMod two_pi_pos 0 p.φ₁, toIcoMod_mem_Ico' _ _, rupert_of_shadows_eq r ?_ rfl⟩
  change (rotR p.α ∘L rotM p.θ₁ (toIcoMod two_pi_pos 0 p.φ₁)) '' _ =
    (rotR p.α ∘L rotM p.θ₁ p.φ₁) '' _
  rw [toIcoMod_eq_add_int_mul, rotM_periodic_φ]

theorem tighten_φ₁_π (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull)
    (hφ₁ : p.φ₁ ∈ Set.Icc 0 (2 * π)) :
    ∃ θ₁ φ₁, φ₁ ∈ Set.Icc 0 π ∧ RupertPose {p with θ₁, φ₁} exactPolyhedron.hull := by
  by_cases h : p.φ₁ ≤ π
  · exact ⟨p.θ₁, p.φ₁, ⟨hφ₁.1, h⟩, by cases p; exact r⟩
  · refine ⟨p.θ₁ + π, 2 * π - p.φ₁, ⟨by linarith [hφ₁.2], by linarith⟩,
      rupert_of_shadows_eq r ?_ rfl⟩
    change (rotR p.α ∘L rotM (p.θ₁ + π) (2 * π - p.φ₁)) '' _ =
      (rotR p.α ∘L rotM p.θ₁ p.φ₁) '' _
    rw [rotM_mod_eq_neg_rotM, ContinuousLinearMap.comp_neg, neg_image_hull]

theorem tighten_θ (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ θ₁ ∈ Set.Ico 0 (2 * π / 15), ∃ θ₂ ∈ Set.Ico 0 (2 * π / 15),
      RupertPose {p with θ₁, θ₂} exactPolyhedron.hull := by
  have h15 : (0 : ℝ) < 2 * π / 15 := by positivity
  refine ⟨toIcoMod h15 0 p.θ₁, toIcoMod_mem_Ico' _ _, toIcoMod h15 0 p.θ₂, toIcoMod_mem_Ico' _ _,
    rupert_of_shadows_eq r ?_ ?_⟩
  · change (rotR p.α ∘L rotM (toIcoMod h15 0 p.θ₁) p.φ₁) '' _ =
      (rotR p.α ∘L rotM p.θ₁ p.φ₁) '' _
    rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp, Set.image_comp,
      Set.image_comp, toIcoMod_eq_add_int_mul, lemma7_1_iterated]
  · change rotM (toIcoMod h15 0 p.θ₂) p.φ₂ '' _ = rotM p.θ₂ p.φ₂ '' _
    rw [toIcoMod_eq_add_int_mul, lemma7_1_iterated]

theorem tighten_α (p : Pose ℝ) (r : RupertPose p exactPolyhedron.hull) :
    ∃ α ∈ Set.Icc (-(π/2)) (π/2), RupertPose {p with α} exactPolyhedron.hull := by
  have hmem := toIcoMod_mem_Ico pi_pos (-(π / 2)) p.α
  refine ⟨toIcoMod pi_pos (-(π / 2)) p.α, ⟨hmem.1, by linarith [hmem.2]⟩,
    rupert_of_shadows_eq r ?_ rfl⟩
  change (rotR (toIcoMod pi_pos (-(π / 2)) p.α) ∘L rotM p.θ₁ p.φ₁) '' _ =
    (rotR p.α ∘L rotM p.θ₁ p.φ₁) '' _
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
