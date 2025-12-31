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

theorem lemma7_1_iterated {θ φ : ℝ} (k : ℤ) :
    (rotM (θ + k * (2 * π / 15)) φ) '' nopert.hull = rotM θ φ '' nopert.hull := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n hn =>
    rw [← hn]; push_cast
    have := lemma7_1 (θ + n * (2 * π / 15)) φ
    ring_nf at this ⊢
    rw [← this]
  | pred n hn =>
    rw [← hn]; push_cast
    have := lemma7_1 (θ + (-1 - n) * (2 * π / 15)) φ
    ring_nf at this ⊢
    rw [← this]

theorem lemma7_2 (θ φ α : ℝ) :
    (rotR (α + π) ∘ rotM θ φ) '' nopert.hull = (rotR α ∘ rotM θ φ) '' nopert.hull := by
  suffices h : (rotR (α + π) ∘L rotM θ φ) '' nopert.vertices = (rotR α ∘L rotM θ φ) '' nopert.vertices by
    change (rotR (α + π) ∘L rotM θ φ) '' nopert.hull = (rotR α ∘L rotM θ φ) '' nopert.hull
    rw [app_hull_eq_hull_app, app_hull_eq_hull_app, h]
  push_cast
  repeat rw [Set.image_comp]
  exact rotR_add_pi_eq_if_pointsym (rotM θ φ '' nopert.vertices)
    (rotM_preserves_pointsymmetry nopert.vertices nopert_verts_pointsym)

theorem lemma7_2_iterated {θ φ α : ℝ} (k : ℤ) :
        (rotR (α + k * π) ∘L rotM θ φ) '' nopert.hull = (rotR α ∘L rotM θ φ) '' nopert.hull := by
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

theorem tighten_φ₁_π (p : Pose) (hφ₁ : p.φ₁ ∈ Set.Icc 0 (2 * π)) :
    ∃ θ₁ α, ∃ φ₁ ∈ Set.Icc 0 π, Pose.equiv p {p with θ₁, φ₁, α} := by
  by_cases h : p.φ₁ < π
  · use p.θ₁, p.α, p.φ₁
    refine ⟨⟨ hφ₁.1, le_of_lt h⟩, ?_⟩
    exact Pose.matrix_eq_imp_pose_equiv rfl rfl rfl
  · use p.θ₁ + π, p.α + π, 2 * π - p.φ₁
    refine ⟨by grind, ?_⟩
    refine Pose.matrix_rm_eq_imp_pose_equiv ?_ ?_
    · simp only [Pose.rotR, Pose.rotM₁, rotR_add_pi_eq_neg_rotR, rotM_mod_eq_neg_rotM]
      ext; simp
    · simp only [Pose.rotM₂]

theorem tighten_φ₂_π (p : Pose) (hφ₂ : p.φ₂ ∈ Set.Icc 0 (2 * π)) :
    ∃ θ₂ α, ∃ φ₂ ∈ Set.Icc 0 π, Pose.equiv p {p with θ₂, φ₂, α} := by
  by_cases h : p.φ₂ < π
  · use p.θ₂, p.α, p.φ₂
    refine ⟨⟨hφ₂.1, le_of_lt h⟩, ?_⟩
    exact Pose.matrix_eq_imp_pose_equiv rfl rfl rfl
  · use p.θ₂ + π, p.α + π, 2 * π - p.φ₂
    refine ⟨by grind, ?_⟩
    refine Pose.matrix_rm_eq_neg_imp_pose_equiv ?_ ?_
    · simp only [Pose.rotR, Pose.rotM₁, rotR_add_pi_eq_neg_rotR]
      ext; simp
    · simp [Pose.rotM₂, rotM_mod_eq_neg_rotM]

theorem tighten_φ₂_π2 (p : Pose) (r : RupertPose p nopert.hull) (hφ₂ : p.φ₂ ∈ Set.Icc 0 π) :
    ∃ q : Pose, q.φ₂ ∈ Set.Icc 0 (π/2) ∧ RupertPose q nopert.hull := by
  by_cases h : p.φ₂ < π / 2
  · exact ⟨p, ⟨hφ₂.1, le_of_lt h⟩, r⟩
  · use flip_phi2 p
    constructor
    · simp only [flip_phi2, Set.mem_Icc, sub_nonneg, tsub_le_iff_right]; grind
    · exact rupert_imp_flip_phi2_rupert2 r

theorem tighten_φ₁ (p : Pose) :
    ∃ φ₁ ∈ Set.Ico 0 (2 * π), Pose.equiv p {p with φ₁} := by
  use Real.emod p.φ₁ (2 * π)
  use Real.emod_in_interval two_pi_pos
  obtain ⟨k, hk⟩ := Real.emod_exists_multiple p.φ₁ (2 * π) two_pi_pos
  rw [hk]
  refine Pose.matrix_eq_imp_pose_equiv ?_ ?_ ?_ <;>
  · simp [Pose.rotR, Pose.rotM₁, Pose.rotM₂, rotM_periodic_φ]

theorem tighten_φ₂ (p : Pose) :
    ∃ φ₂ ∈ Set.Ico 0 (2 * π), Pose.equiv p {p with φ₂} := by
  use Real.emod p.φ₂ (2 * π)
  use Real.emod_in_interval two_pi_pos
  obtain ⟨k, hk⟩ := Real.emod_exists_multiple p.φ₂ (2 * π) two_pi_pos
  rw [hk]
  refine Pose.matrix_eq_imp_pose_equiv ?_ ?_ ?_ <;>
  · simp [Pose.rotR, Pose.rotM₁, Pose.rotM₂, rotM_periodic_φ]

def NopertEquiv (p q : Pose) : Prop :=
  RupertPose p nopert.hull ↔ RupertPose q nopert.hull

def inner_outer_imp_nopert_equiv {p q : Pose}
    (hinner : p.inner '' nopert.hull = q.inner '' nopert.hull)
    (houter : p.outer '' nopert.hull = q.outer '' nopert.hull) :
    NopertEquiv p q := by
  constructor <;>
  · simp only [RupertPose]
    repeat rw [Pose.inner_shadow_eq_img_inner, Pose.outer_shadow_eq_img_outer]
    rw [hinner, houter]
    tauto

theorem tighten_θ (p : Pose) :
    ∃ θ₁ ∈ Set.Ico 0 (2 * π / 15),
    ∃ θ₂ ∈ Set.Ico 0 (2 * π / 15),
    NopertEquiv p {p with θ₁, θ₂} := by

  have two_pi_15_pos : 2 * π / 15 > 0 :=
    div_pos (two_pi_pos) (by norm_num)

  let θ₁ := Real.emod p.θ₁ (2 * π / 15)
  let θ₂ := Real.emod p.θ₂ (2 * π / 15)
  use θ₁, Real.emod_in_interval two_pi_15_pos,
      θ₂, Real.emod_in_interval two_pi_15_pos
  obtain ⟨k₁, hk₁⟩ := Real.emod_exists_multiple p.θ₁ (2 * π / 15) two_pi_15_pos
  obtain ⟨k₂, hk₂⟩ := Real.emod_exists_multiple p.θ₂ (2 * π / 15) two_pi_15_pos
  simp only [θ₁, θ₂]
  rw [hk₁, hk₂]
  let p1 := {p  with θ₁ := p.θ₁ + k₁ * (2 * π / 15) }
  let p2 := {p1 with θ₂ := p.θ₂ + k₂ * (2 * π / 15) }
  refine inner_outer_imp_nopert_equiv ?_ ?_
  · calc p.inner '' nopert.hull
    _ = (p.rotR ∘ p.rotM₁) '' nopert.hull := by rw [Pose.inner_eq_RM]
    _ = p.rotR '' (p.rotM₁ '' nopert.hull) := by rw [Set.image_comp]
    _ = p.rotR '' (rotM p.θ₁ p.φ₁ '' nopert.hull) := by rfl
    _ = p.rotR '' (rotM (p.θ₁ + k₁ * (2 * π / 15)) p.φ₁ '' nopert.hull) := by
        rw [← lemma7_1_iterated k₁]
    _ = p.rotR '' (p2.rotM₁ '' nopert.hull) := by rfl
    _ = (p.rotR ∘ p2.rotM₁) '' nopert.hull := by rw [Set.image_comp]
    _ = (p2.rotR ∘ p2.rotM₁) '' nopert.hull := by rfl
    _ = p2.inner '' nopert.hull := by rw [Pose.inner_eq_RM]
  · calc p.outer '' nopert.hull
    _ = p.rotM₂ '' nopert.hull := by rw [Pose.outer_eq_M]
    _ = rotM p.θ₂ p.φ₂ '' nopert.hull := by rfl
    _ = rotM (p.θ₂ + k₂ * (2 * π / 15)) p.φ₂ '' nopert.hull := by
        rw [← lemma7_1_iterated k₂]
    _ = p2.rotM₂ '' nopert.hull := by rfl
    _ = p2.outer '' nopert.hull := by rw [Pose.outer_eq_M]

theorem tighten_α (p : Pose) :
    ∃ α ∈ Set.Icc (-(π/2)) (π/2),
    NopertEquiv p {p with α} := by
  use Real.emod (p.α + π/2) π - π/2
  have hα1 : (p.α + π/2).emod π ∈ Set.Ico 0 π :=
    Real.emod_in_interval pi_pos
  have hα2 : (p.α + π / 2).emod π - π / 2 ∈ Set.Icc (-(π / 2)) (π / 2) := by
    grind
  use hα2
  obtain ⟨k, hk⟩ := Real.emod_exists_multiple (p.α + π/2) π pi_pos
  rw [hk]
  let p1 : Pose := {p with α := p.α + k * π}
  refine inner_outer_imp_nopert_equiv ?_ rfl
  convert_to _ = ({ p with α := p.α + k * π} : Pose).inner '' nopert.hull
  · ring_nf
  calc p.inner '' nopert.hull
  _ = (p.rotR ∘ p.rotM₁) '' nopert.hull := by rw [Pose.inner_eq_RM]
  _ = (rotR (p.α) ∘L rotM p.θ₁ p.φ₁) '' nopert.hull := by rfl
  _ = (rotR (p.α + k * π) ∘L rotM p.θ₁ p.φ₁) '' nopert.hull := by rw [lemma7_2_iterated k]
  _ = (p1.rotR ∘ p1.rotM₁) '' nopert.hull := by rfl
  _ = p1.inner '' nopert.hull := by rw [Pose.inner_eq_RM]

theorem rupert_post_tightening (p : Pose) (r : RupertPose p nopert.hull)
     (hφ₁ : p.φ₁ ∈ Set.Icc 0 π) (hφ₂ : p.φ₂ ∈ Set.Icc 0 (π/2)) :
    ∃ p' : Pose, tightInterval.contains p' ∧ RupertPose p' nopert.hull := by
  obtain ⟨θ₁, hθ₁, θ₂, hθ₂, eq⟩ := tighten_θ p
  let p2 := {p with θ₁, θ₂}
  obtain ⟨α, hα, eq2⟩ := tighten_α p2
  use {p2 with α}
  use ⟨Set.Ico_subset_Icc_self hθ₁, Set.Ico_subset_Icc_self hθ₂,
       hφ₁, hφ₂, hα⟩
  exact  eq2.mp (eq.mp r)

-- [SY25] §2.2, Corollary 8
-- This is a piece that relies on symmetry of the Noperthedron
theorem rupert_tightening (p : Pose) (r : RupertPose p nopert.hull) :
    ∃ p' : Pose, tightInterval.contains p' ∧ RupertPose p' nopert.hull := by
  obtain ⟨φ₂, hφ₂_2π, eq⟩ := tighten_φ₂ p
  have r1 : RupertPose {p with φ₂} nopert.hull := Pose.equiv_rupert_imp_rupert eq r
  obtain ⟨θ₂, α, φ₂', φ₂'_π, eq'⟩ := tighten_φ₂_π {p with φ₂} (Set.Ico_subset_Icc_self hφ₂_2π)
  have r2 : RupertPose _ nopert.hull := Pose.equiv_rupert_imp_rupert eq' r1
  obtain ⟨q, hqφ₂, r2a⟩ := tighten_φ₂_π2 _ r2 φ₂'_π
  obtain ⟨φ₁, hφ₁, eq2⟩ := tighten_φ₁ q
  have r3 := Pose.equiv_rupert_imp_rupert eq2 r2a
  obtain ⟨θ₁, α, φ₁', hφ₁', eq3⟩ := tighten_φ₁_π {q with φ₁} (Set.Ico_subset_Icc_self hφ₁)
  have r4 := Pose.equiv_rupert_imp_rupert eq3 r3
  simp only at r4
  clear eq eq'
  exact rupert_post_tightening _ r4 hφ₁' hqφ₂

end Tightening
