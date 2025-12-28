import Noperthedron.Rupert.Basic
import Noperthedron.PoseClasses
import Noperthedron.Basic
import Noperthedron.Nopert
import Noperthedron.ViewPose
import Noperthedron.PoseInterval

open Real
namespace Tightening

lemma rotM_neg_comm {θ φ : ℝ} (y : ℝ³) : (rotM θ φ) (-y) = -(rotM θ φ) y := by
  ext i; fin_cases i <;> simp

lemma rotM_preserves_pointsymmetry {θ φ : ℝ} (X : Finset ℝ³) (hX : PointSym (X : Set ℝ³)) :
    PointSym (rotM θ φ '' X) := by
  intro x hx
  simp only [Set.mem_image] at hx ⊢
  obtain ⟨y, hy, hy2⟩ := hx
  exact ⟨-y, hX y hy, by rw [← hy2]; exact rotM_neg_comm y⟩

lemma rotR_neg_comm {α : ℝ} (y : ℝ²) : (rotR α) (-y) = -(rotR α) y := by
  ext i; fin_cases i <;> simp

lemma rotR_preserves_pointsymmetry {α : ℝ} (X : Set ℝ²) (hX : PointSym X) :
    PointSym (rotR α '' X) := by
  intro x hx
  simp only [Set.mem_image] at hx ⊢
  obtain ⟨y, hy, hy2⟩ := hx
  exact ⟨-y, hX y hy, by rw [← hy2]; exact rotR_neg_comm y⟩

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

set_option pp.coercions.types true

lemma rotation_preserves_c15_vertices {x y : ℝ³} (hx : x ∈ (Nopert.C15 y)) (k : ℤ) :
    RzC (2 * π * k / 15) x ∈ (Nopert.C15 y) := by
  sorry

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

lemma nopert_vertices_rotation_invariant :
   (RzC (π * (-2 / 15))) '' nopert.vertices = nopert.vertices := by
  ext x
  constructor
  · intro hx
    simp_all only [Set.mem_image, SetLike.mem_coe]
    obtain ⟨y, hy, hy2⟩ := hx
    rw [← hy2]
    have q := rotation_preserves_nopert_vertices y hy (-1)
    ring_nf at q
    exact q
  · intro hx
    simp_all only [Set.mem_image, SetLike.mem_coe]
    use (RzC (π * (2 / 15)) x)
    refine ⟨?_, ?_⟩
    · have q := rotation_preserves_nopert_vertices x hx 1
      ring_nf at q
      exact q
    · change (RzC (π * (-2 / 15)) * RzC (π * (2 / 15))) x = x
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
  rw [ContinuousLinearMap.coe_mul, Set.image_comp, nopert_vertices_rotation_invariant]

theorem lemma7_2 (θ φ α : ℝ) :
  (rotR (α + π) ∘L rotM θ φ) '' nopert.hull = (rotR α ∘L rotM θ φ) '' nopert.hull := by
    suffices h : (rotR (α + π) ∘L rotM θ φ) '' nopert.vertices = (rotR α ∘L rotM θ φ) '' nopert.vertices by
      rw [app_hull_eq_hull_app, app_hull_eq_hull_app, h]
    push_cast
    repeat rw [Set.image_comp]
    exact rotR_add_pi_eq_if_pointsym (rotM θ φ '' nopert.vertices)
      (rotM_preserves_pointsymmetry nopert.vertices nopert_verts_pointsym)

theorem lemma7_3 (θ φ : ℝ) :
  (flip_y ∘L rotM θ φ) '' nopert.hull = (-rotM (θ + π / 15) (π - φ)) '' nopert.hull := by
    sorry

-- [SY25] §2.2, Corollary 8
-- This is a piece that relies on symmetry of the Noperthedron
theorem rupert_tightening (p : Pose) (r : RupertPose p nopert.hull) :
    ∃ p' : Pose, tightInterval.contains p' ∧ RupertPose p' nopert.hull := by
  sorry -- TODO(medium-hard)

end Tightening
