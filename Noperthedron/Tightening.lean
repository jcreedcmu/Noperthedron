import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Basic
import Noperthedron.Nopert
import Noperthedron.ViewPose
import Noperthedron.PoseInterval
import Noperthedron.RealMod

open Real
namespace Tightening

lemma rotM_preserves_pointsymmetry {θ φ : ℝ} (X : Finset ℝ³) (hX : PointSym (X : Set ℝ³)) :
    PointSym (rotM θ φ '' X) := by
  intro x hx
  simp only [Set.mem_image] at hx ⊢
  obtain ⟨y, hy, hy2⟩ := hx
  exact ⟨-y, hX y hy, by rw [← hy2, (rotM θ φ).map_neg]⟩

lemma rotR_preserves_pointsymmetry {α : ℝ} (X : Set ℝ²) (hX : PointSym X) :
    PointSym (rotR α '' X) := by
  intro x hx
  simp only [Set.mem_image] at hx ⊢
  obtain ⟨y, hy, hy2⟩ := hx
  exact ⟨-y, hX y hy, by rw [← hy2, (rotR α).map_neg]⟩

lemma neg_image_eq_if_pointsym (X : Set ℝ²) (hX : PointSym X) : (-·) '' X = X := by
  simp only [Set.image_neg_eq_neg]; ext x
  constructor
  · simp only [Set.mem_neg]; intro hx; specialize hX (-x) hx; simpa [neg_neg] using hX
  · simp only [Set.mem_neg]; intro hx; specialize hX x hx; exact hX

lemma rotR_add_pi_eq_if_pointsym {α : ℝ} (X : Set ℝ²) (hX : PointSym X) :
    rotR (α + π) '' X = rotR α '' X := by
  have : rotR (α + π) = (-·) ∘ rotR α := by
    ext x i; fin_cases i <;> (simp [Matrix.vecHead, Matrix.vecTail]; ring_nf)
  rw [this, Set.image_comp]
  exact neg_image_eq_if_pointsym (rotR α '' X) (rotR_preserves_pointsymmetry X hX)

lemma rotation_preserves_c15_vertices {x y : ℝ³} (hx : x ∈ (Nopert.C15 y)) (k : ℤ) :
    RzC (2 * π * k / 15) x ∈ (Nopert.C15 y) := by
  simp_all only [Nopert.C15, Finset.mem_image]
  obtain ⟨a, ha, ha2⟩ := hx
  rw [← ha2]
  use (a + k).natMod 15
  simp only [Finset.mem_range]
  refine ⟨Int.natMod_lt (by norm_num), ?_⟩
  change RzC (2 * π * (a + k).natMod 15 / 15) y = (RzC (2 * π * k / 15) * RzC (2 * π * a / 15)) y
  rw [← AddChar.map_add_eq_mul RzC]
  rw [show 2 * π * k / 15 + 2 * π * a / 15 = 2 * π * (a + k) / 15 by ring_nf]
  let apk : ℤ := a + k
  convert_to RzC (2 * π * ↑(apk.natMod 15) / 15) y = RzC (2 * π * apk / 15) y
  · simp [apk]
  rw [show (↑(apk.natMod 15) : ℝ) = (↑(↑(apk.natMod 15) : ℤ) : ℝ) by rfl]
  have (z : ℤ) : (z.natMod 15 : ℤ) = z % 15 := by
    simp only [Int.natMod]; grind
  rw [this]
  -- at this point we are proving
  -- (RzC (2 * π * (apk % 15) / 15)) y = (RzC (2 * π * apk / 15)) y
  rw [Int.emod_def]; push_cast; rw [mul_sub, sub_div]
  have :
      2 * π * (↑apk : ℝ) / 15 - 2 * π * (15 * (↑(apk / 15) : ℝ)) / 15 =
      2 * π * (↑apk : ℝ) / 15 + 2 * π * ((↑(-(apk / 15)) : ℝ)) := by
    push_cast; ring_nf
  rw [this, AddChar.map_add_eq_mul, RzC_periodic (-↑(apk / 15))]
  simp

lemma rotation_preserves_pointsym_c15_vertices {x y : ℝ³} (hx : x ∈ pointsymmetrize (Nopert.C15 y)) (k : ℤ) :
    RzC (2 * π * k / 15) x ∈ pointsymmetrize (Nopert.C15 y) := by
  simp_all only [pointsymmetrize, Finset.mem_union]
  rcases hx with h | h
  · left; exact rotation_preserves_c15_vertices h k
  · right
    simp_all only [Finset.mem_image]
    obtain ⟨a, ha, ha2⟩ := h
    rw [← ha2]
    use RzC (2 * π * k / 15) a
    exact ⟨rotation_preserves_c15_vertices ha k, by simp⟩

open Nopert in
lemma every_nopert_vert_in_c15 (x : ℝ³) (hx : x ∈ nopert.vertices) :
    ∃ (y : ℝ³), x ∈ pointsymmetrize (Nopert.C15 y) ∧ pointsymmetrize (Nopert.C15 y) ⊆ nopert.vertices := by
  simp only [nopert, nopertVerts, pointsymmetrize] at hx
  simp only [Finset.mem_union, Finset.mem_image] at hx
  rcases hx with h | h
  · simp only [halfNopertVerts, Finset.mem_union] at h
    rcases h with (h | h) | h
    · use Nopert.C1R
      constructor
      · simp only [pointsymmetrize, Finset.mem_union]; left; exact h
      · exact pointsym_c1r_sub_nopert
    · use Nopert.C2R
      constructor
      · simp only [pointsymmetrize, Finset.mem_union]; left; exact h
      · exact pointsym_c2r_sub_nopert
    · use Nopert.C3R
      constructor
      · simp only [pointsymmetrize, Finset.mem_union]; left; exact h
      · exact pointsym_c3r_sub_nopert
  · obtain ⟨a, ha, ha2⟩ := h
    simp only [halfNopertVerts, Finset.mem_union] at ha
    rcases ha with (h | h) | h
    · use Nopert.C1R
      rw [← ha2]
      constructor
      · simp only [pointsymmetrize, Finset.mem_union]; right; simpa using h
      · exact pointsym_c1r_sub_nopert
    · use Nopert.C2R
      rw [← ha2]
      constructor
      · simp only [pointsymmetrize, Finset.mem_union]; right; simpa using h
      · exact pointsym_c2r_sub_nopert
    · use Nopert.C3R
      rw [← ha2]
      constructor
      · simp only [pointsymmetrize, Finset.mem_union]; right; simpa using h
      · exact pointsym_c3r_sub_nopert

lemma rotation_preserves_nopert_vertices (x : ℝ³) (hx : x ∈ nopert.vertices) (k : ℤ) :
    RzC (2 * π * k / 15) x ∈ nopert.vertices := by
  obtain ⟨y, hx2, ysub⟩ := every_nopert_vert_in_c15 x hx
  exact ysub (rotation_preserves_pointsym_c15_vertices hx2 k)

lemma nopert_vertices_rotation_invariant (k : ℤ) :
    (RzC (2 * π * k / 15)) '' nopert.vertices = nopert.vertices := by
  ext x
  constructor
  · intro hx
    simp_all only [Set.mem_image, SetLike.mem_coe]
    obtain ⟨y, hy, hy2⟩ := hx
    rw [← hy2]
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

lemma app_hull_eq_hull_app (s : Shape) (f : ℝ³ →L[ℝ] ℝ²) : f '' s.hull = convexHull ℝ (f '' s.vertices) :=
  f.image_convexHull s.vertices

theorem lemma7_1 (θ φ : ℝ) :
    (rotM (θ + 2/15*π) φ) '' nopert.hull = rotM θ φ '' nopert.hull := by
  suffices h : (rotM (θ + 2/15*π) φ) '' nopert.vertices = rotM θ φ '' nopert.vertices by
    rw [app_hull_eq_hull_app, app_hull_eq_hull_app, h]
  suffices h : (RzL (-(θ + 2/15*π))) '' nopert.vertices = (RzL (-θ)) '' nopert.vertices by
    repeat rw [rotM_identity]
    push_cast
    repeat rw [Set.image_comp]
    rw [h]
  change (RzC (-(θ + 2 / 15 * π))) '' nopert.vertices = (RzC (-θ)) '' nopert.vertices
  ring_nf
  conv => arg 1; arg 1; intro a; simp only [AddChar.map_add_eq_mul]
  rw [ContinuousLinearMap.coe_mul, Set.image_comp,
    show π * (-2 / 15) = 2 * π * (-1:ℤ) / 15 by ring_nf,
    nopert_vertices_rotation_invariant]

theorem lemma7_2 (θ φ α : ℝ) :
    (rotR (α + π) ∘L rotM θ φ) '' nopert.hull = (rotR α ∘L rotM θ φ) '' nopert.hull := by
  suffices h : (rotR (α + π) ∘L rotM θ φ) '' nopert.vertices = (rotR α ∘L rotM θ φ) '' nopert.vertices by
    rw [app_hull_eq_hull_app, app_hull_eq_hull_app, h]
  push_cast
  repeat rw [Set.image_comp]
  exact rotR_add_pi_eq_if_pointsym (rotM θ φ '' nopert.vertices)
    (rotM_preserves_pointsymmetry nopert.vertices nopert_verts_pointsym)

lemma lemma7_3_calculation (θ φ : ℝ) (v : ℝ³) :
    flip_y (rotM θ φ v) = - rotM (θ + π / 15) (π - φ) (RzC (16 * π / 15) v) := by
  simp only [flip_y, flip_y_mat, rotM, RzC, rotM_mat]
  ext i
  simp only [neg_mul, LinearMap.coe_toContinuousLinearMap',
    Function.comp_apply, Matrix.piLp_ofLp_toEuclideanLin, Matrix.toLin'_apply, Matrix.cons_mulVec,
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
    (flip_y ∘L rotM θ φ) '' nopert.hull = (rotM (θ + π / 15) (π - φ)) '' nopert.hull := by
  suffices h : (flip_y ∘L rotM θ φ) '' nopert.vertices = (rotM (θ + π / 15) (π - φ)) '' nopert.vertices by
    rw [app_hull_eq_hull_app, app_hull_eq_hull_app, h]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, lemma7_3_calculation]
  have h1 : (fun a ↦ -(rotM (θ + π / 15) (π - φ)) ((RzC (16 * π / 15)) a)) =
    (fun a ↦ -(rotM (θ + π / 15) (π - φ)) a) ∘ (RzC (16 * π / 15)) := by rfl
  have h2 : (rotM (θ + π / 15) (π - φ)) '' ↑nopert.vertices =
      (-rotM (θ + π / 15) (π - φ)) '' ↑nopert.vertices := by
    rw [neg_lin_eq_lin_neg (rotM (θ + π / 15) (π - φ)), Set.image_comp]
    congr
    rw [pointsym_imp_neg_image_eq]
    exact nopert_verts_pointsym
  rw [h2, h1, Set.image_comp]
  congr
  convert_to (RzC (2 * π * ↑8 / 15)) '' ↑nopert.vertices = ↑nopert.vertices
  · ring_nf
  exact nopert_vertices_rotation_invariant 8

lemma flip_rotR_swap_minus (α : ℝ) : flip_y ∘L rotR α = rotR (-α) ∘L flip_y := by
  ext v i; fin_cases i <;> (simp; ring_nf)

noncomputable
def flip_phi2 (p : Pose) : Pose := {
  θ₁ := p.θ₁ + π/15,
  φ₁ := π - p.φ₁,
  θ₂ := p.θ₂ + π/15,
  φ₂ := π - p.φ₂,
  α := -p.α,
}

theorem rupert_imp_flip_phi2_rupert2 {p : Pose} (r : RupertPose p nopert.hull) :
    RupertPose (flip_phi2 p) nopert.hull := by
  simp_all only [RupertPose, Pose.inner_shadow_eq_RM, Pose.outer_shadow_eq_M]
  let fh := flip_y_equiv.toHomeomorph
  calc closure ((rotR (-p.α) ∘ rotM (p.θ₁ + π / 15) (π - p.φ₁)) '' nopert.hull)
    _ = closure (rotR (-p.α) '' ((flip_y ∘L p.rotM₁) '' nopert.hull)) := by rw [Set.image_comp, ← lemma7_3]; rfl
    _ = closure (((rotR (-p.α) ∘L flip_y) ∘L p.rotM₁) '' nopert.hull) := by rw [← Set.image_comp]; rfl
    _ = closure (((flip_y ∘ (p.rotR ∘L p.rotM₁))) '' nopert.hull) := by rw [← flip_rotR_swap_minus]; rfl
    _ = closure (flip_y '' ((p.rotR ∘L p.rotM₁) '' nopert.hull)) := by rw [Set.image_comp]
    _ = flip_y '' closure ((p.rotR ∘L p.rotM₁) '' nopert.hull) := fh.image_closure _ |>.symm
    _ ⊆ flip_y '' interior (p.rotM₂ '' nopert.hull) := Set.image_mono r
    _ = interior (flip_y '' (p.rotM₂ '' nopert.hull)) := fh.image_interior _
    _ = interior ((flip_y ∘L rotM p.θ₂ p.φ₂) '' nopert.hull) := by rw [← Set.image_comp]; rfl
    _ = interior ((rotM (p.θ₂ + π / 15) (π - p.φ₂)) '' nopert.hull) := by rw [lemma7_3]

theorem rupert_tighten_φ₁ (θ₁ θ₂ φ₁ φ₂ α : ℝ) (hφ₁ : φ₁ ∈ Set.Icc 0 (2 * π)) :
    ∃ θ₁' α', ∃ φ₁' ∈ Set.Icc 0 π, Pose.equiv ⟨θ₁, θ₂, φ₁, φ₂, α⟩ ⟨θ₁', θ₂, φ₁', φ₂, α'⟩ := by
  by_cases h : φ₁ < π
  · use θ₁, α, φ₁
    refine ⟨⟨ hφ₁.1, le_of_lt h⟩, ?_⟩
    exact Pose.matrix_eq_imp_pose_equiv rfl rfl rfl
  · use θ₁ + π, α + π, 2 * π - φ₁
    refine ⟨by grind, ?_⟩
    refine Pose.matrix_rm_eq_imp_pose_equiv ?_ ?_
    · simp only [Pose.rotR, Pose.rotM₁, rotR_add_pi_eq_neg_rotR, rotM_mod_eq_neg_rotM]
      ext; simp
    · simp only [Pose.rotM₂]

theorem rupert_tighten_φ₂ (θ₁ θ₂ φ₁ φ₂ α : ℝ) (hφ₂ : φ₂ ∈ Set.Icc 0 (2 * π)) :
    ∃ θ₂' α', ∃ φ₂' ∈ Set.Icc 0 π, Pose.equiv ⟨θ₁, θ₂, φ₁, φ₂, α⟩ ⟨θ₁, θ₂', φ₁, φ₂', α'⟩ := by
  by_cases h : φ₂ < π
  · use θ₂, α, φ₂
    refine ⟨⟨hφ₂.1, le_of_lt h⟩, ?_⟩
    exact Pose.matrix_eq_imp_pose_equiv rfl rfl rfl
  · use θ₂ + π, α + π, 2 * π - φ₂
    refine ⟨by grind, ?_⟩
    refine Pose.matrix_rm_eq_neg_imp_pose_equiv ?_ ?_
    · simp only [Pose.rotR, Pose.rotM₁, rotR_add_pi_eq_neg_rotR]
      ext; simp
    · simp [Pose.rotM₂, rotM_mod_eq_neg_rotM]

theorem rupert_tighten_θ₁ (θ₁ θ₂ φ₁ φ₂ α : ℝ) :
    ∃ θ₁' ∈ Set.Ico 0 (2 * π), Pose.equiv ⟨θ₁, θ₂, φ₁, φ₂, α⟩ ⟨θ₁', θ₂, φ₁, φ₂, α⟩ := by
  use Real.emod θ₁ (2 * π)
  use Real.emod_in_interval two_pi_pos
  obtain ⟨k, hk⟩ := Real.emod_exists_multiple θ₁ (2 * π) two_pi_pos
  rw [hk]
  refine Pose.matrix_eq_imp_pose_equiv ?_ ?_ ?_ <;>
  · simp [Pose.rotR, Pose.rotM₁, Pose.rotM₂, rotM_periodic_θ]

theorem rupert_tighten_θ₂ (θ₁ θ₂ φ₁ φ₂ α : ℝ) :
    ∃ θ₂' ∈ Set.Ico 0 (2 * π), Pose.equiv ⟨θ₁, θ₂, φ₁, φ₂, α⟩ ⟨θ₁, θ₂', φ₁, φ₂, α⟩ := by
  use Real.emod θ₂ (2 * π)
  use Real.emod_in_interval two_pi_pos
  obtain ⟨k, hk⟩ := Real.emod_exists_multiple θ₂ (2 * π) two_pi_pos
  rw [hk]
  refine Pose.matrix_eq_imp_pose_equiv ?_ ?_ ?_ <;>
  · simp [Pose.rotR, Pose.rotM₁, Pose.rotM₂, rotM_periodic_θ]

theorem rupert_tighten_α (θ₁ θ₂ φ₁ φ₂ α : ℝ) :
    ∃ α' ∈ Set.Icc (-π) π, Pose.equiv ⟨θ₁, θ₂, φ₁, φ₂, α⟩ ⟨θ₁, θ₂, φ₁, φ₂, α'⟩ := by
  sorry

theorem rupert_tighten_φ₂' (p : Pose) (r : RupertPose p nopert.hull) :
    ∃ p' : Pose, RupertPose p' nopert.hull ∧ p'.φ₂ ∈ Set.Icc 0 π := by
  sorry

theorem rupert_post_tightening (p : Pose) (r : RupertPose p nopert.hull)
     (hφ₂ : p.φ₂ ∈ Set.Icc 0 (π/2)) :
    ∃ p' : Pose, tightInterval.contains p' ∧ RupertPose p' nopert.hull := by
  sorry

-- [SY25] §2.2, Corollary 8
-- This is a piece that relies on symmetry of the Noperthedron
theorem rupert_tightening (p : Pose) (r : RupertPose p nopert.hull) :
    ∃ p' : Pose, tightInterval.contains p' ∧ RupertPose p' nopert.hull := by
  have ⟨p₁, hrup, hφ₂⟩ := rupert_tighten_φ₂' p r
  have : π > 0 := pi_pos
  have φ₂_range : p₁.φ₂ ∈ Set.Icc 0 π := hφ₂
  have ⟨p₂, p₂_rup, p₂_tight_φ₂⟩ :
      ∃ p₂ : Pose, RupertPose p₂ nopert.hull ∧ p₂.φ₂ ∈ Set.Icc 0 (π/2) := by
    by_cases h : p₁.φ₂ < π / 2
    · exact Exists.intro p₁ ⟨hrup, ⟨φ₂_range.1, le_of_lt h⟩⟩
    · replace h : p₁.φ₂ ≥ π / 2 := Std.not_lt.mp h
      use flip_phi2 p₁, rupert_imp_flip_phi2_rupert2 hrup
      grind [flip_phi2]
  exact rupert_post_tightening p₂ p₂_rup p₂_tight_φ₂

end Tightening
