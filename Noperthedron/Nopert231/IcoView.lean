module

public import Noperthedron.Nopert231.IcoReduction
public import Noperthedron.Nopert231.AtlasProjectiveView

@[expose] public section

/-!
# Reducing the view modulo Ih into the triangle T

nopert229/notes/S.md §2.3, reduction 2. The view of a pose is the third row
of its outer rotation. Composing both rotations on the right with g ∈ I, or
reflecting the view (`viewAntipode`), preserves Rupert-ness for an `IModel`,
and changes the view v to `±G_gᵀ v`.

Let c be a rational point inside the Schwarz chamber, and choose the sign
and g maximizing ⟨±G_gᵀ v, c⟩ (`exists_view_dirichlet`). The chamber's walls
are the mirrors −H_i of three half-turns H_i ∈ I; comparing with the
reflected candidates gives ⟨w, c + H_i c⟩ ≥ 0 for the reduced view w. Each
homogeneous wall m_j of the rational triangle T is a nonnegative
K-combination of the vectors c + H_i c (generated Farkas data, decided
here), so ⟨w, m_j⟩ ≥ 0: w lies in cone(T) (`InViewCone`).
-/

namespace Noperthedron.Nopert231

open scoped Matrix

/-! ### Data access -/

def viewWall (i : Fin 3) : Nat := viewWallIndex.getD i.val 0

def viewCenterZ (r : Fin 3) : Int := viewCenter100.getD r.val 0

def wallVec (i r : Fin 3) : IcoZ := (viewWallVector.getD i.val []).getD r.val ⟨0, 0, 0, 0⟩

def triNormal (j r : Fin 3) : Int := (viewTriangleNormal.getD j.val []).getD r.val 0

def farkasScale (j : Fin 3) : Nat := viewFarkasScale.getD j.val 0

def farkasCoef (j i : Fin 3) : IcoZ := (viewFarkas.getD j.val []).getD i.val ⟨0, 0, 0, 0⟩

/-- `Σ_i 8 Λ_ji D_ir`. -/
def farkasSum (j r : Fin 3) : IcoZ :=
  IcoZ.add (IcoZ.add (IcoZ.mul8 (farkasCoef j 0) (wallVec 0 r))
    (IcoZ.mul8 (farkasCoef j 1) (wallVec 1 r))) (IcoZ.mul8 (farkasCoef j 2) (wallVec 2 r))

/-- `20 c_r · 100 + Σ_j (100 c_j) (20 H)_rj`, which should be `D_ir`. -/
def wallFormula (i r : Fin 3) : IcoZ :=
  let E := (icoEntry (viewWall i)).entry
  IcoZ.add (IcoZ.add (IcoZ.add ⟨20 * viewCenterZ r, 0, 0, 0⟩
    (IcoZ.scale (viewCenterZ 0) (E r 0))) (IcoZ.scale (viewCenterZ 1) (E r 1)))
    (IcoZ.scale (viewCenterZ 2) (E r 2))

def viewDataCheck : Bool :=
  (List.finRange 3).all fun i =>
    decide (viewWall i < 60) &&
      decide (M3.transpose (icoEntry (viewWall i)) = icoEntry (viewWall i)) &&
      (List.finRange 3).all fun r => decide (wallVec i r = wallFormula i r)

def farkasCheck : Bool :=
  (List.finRange 3).all fun j =>
    decide (0 < farkasScale j) &&
      ((List.finRange 3).all fun r =>
        decide (farkasSum j r = ⟨8 * (farkasScale j : Int) * triNormal j r, 0, 0, 0⟩)) &&
      ((List.finRange 3).all fun i => decide (0 ≤ IcoZ.lo (farkasCoef j i)))

theorem viewDataCheck_eq : viewDataCheck = true := by decide +kernel

theorem farkasCheck_eq : farkasCheck = true := by decide +kernel

theorem viewWall_lt (i : Fin 3) : viewWall i < 60 := by
  have h := viewDataCheck_eq
  simp only [viewDataCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h i).1.1

/-- The wall half-turn `H_i`. -/
def wallElem (i : Fin 3) : IcoIndex := ⟨viewWall i, viewWall_lt i⟩

theorem wallElem_symm (i : Fin 3) : (icoMatrix (wallElem i))ᵀ = icoMatrix (wallElem i) := by
  have h := viewDataCheck_eq
  simp only [viewDataCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, decide_eq_true_eq] at h
  have ht := (h i).1.2
  rw [icoMatrix, ico, Matrix.transpose_smul, ← M3.toMatrix_transpose]
  simp only [wallElem, ht]

/-- c, the rational interior point. -/
noncomputable def viewCenter : Fin 3 → ℝ := fun r => (viewCenterZ r : ℝ) / 100

theorem val_wallVec (i r : Fin 3) :
    IcoZ.val (wallVec i r) =
      2000 * (viewCenter r + (icoMatrix (wallElem i) *ᵥ viewCenter) r) := by
  have h := viewDataCheck_eq
  simp only [viewDataCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, decide_eq_true_eq] at h
  rw [(h i).2 r]
  simp only [wallFormula, IcoZ.val_add, IcoZ.val_scale, IcoZ.val_mk_int, viewCenter,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, icoMatrix, ico, wallElem,
    Matrix.smul_apply, M3.toMatrix, Matrix.of_apply, smul_eq_mul]
  push_cast
  ring

/-! ### Farkas: the wall inequalities put w in cone(T) -/

/-- `⟨w, D_i⟩`, a positive multiple of `⟨w, c + H_i c⟩`. -/
noncomputable def wallValue (w : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ r, w r * IcoZ.val (wallVec i r)

/-- w lies in the closed cone over T. -/
def InViewCone (w : Fin 3 → ℝ) : Prop := ∀ j : Fin 3, 0 ≤ ∑ r, w r * (triNormal j r : ℝ)

theorem inViewCone_of_walls {w : Fin 3 → ℝ} (hw : ∀ i, 0 ≤ wallValue w i) : InViewCone w := by
  have h := farkasCheck_eq
  simp only [farkasCheck, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.and_eq_true, decide_eq_true_eq] at h
  intro j
  obtain ⟨⟨hN, hsum⟩, hnonneg⟩ := h j
  have hsumR : ∀ r, IcoZ.val (farkasSum j r) =
      8 * (farkasScale j : ℝ) * (triNormal j r : ℝ) := by
    intro r
    rw [hsum r, IcoZ.val_mk_int]
    push_cast
    ring
  have hlam : ∀ i, 0 ≤ IcoZ.val (farkasCoef j i) := by
    intro i
    have := IcoZ.lo_le_val (farkasCoef j i)
    have h0 : (0 : ℝ) ≤ (IcoZ.lo (farkasCoef j i) : ℝ) := by exact_mod_cast hnonneg i
    linarith
  have hrow : ∀ r, 8 * (farkasScale j : ℝ) * (triNormal j r : ℝ) =
      ∑ i, 8 * IcoZ.val (farkasCoef j i) * IcoZ.val (wallVec i r) := by
    intro r
    rw [← hsumR r]
    simp only [farkasSum, IcoZ.val_add, IcoZ.val_mul8, Fin.sum_univ_three]
    ring
  have hkey : 8 * (farkasScale j : ℝ) * ∑ r, w r * (triNormal j r : ℝ) =
      8 * ∑ i, IcoZ.val (farkasCoef j i) * wallValue w i := by
    have h0 := hrow 0
    have h1 := hrow 1
    have h2 := hrow 2
    simp only [wallValue, Fin.sum_univ_three] at h0 h1 h2 ⊢
    linear_combination w 0 * h0 + w 1 * h1 + w 2 * h2
  have hrhs : 0 ≤ 8 * ∑ i, IcoZ.val (farkasCoef j i) * wallValue w i := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (hw i)
  have hNpos : (0 : ℝ) < 8 * (farkasScale j : ℝ) := by
    have : (0 : ℝ) < (farkasScale j : ℝ) := by exact_mod_cast hN
    linarith
  rw [← hkey] at hrhs
  exact (mul_nonneg_iff_of_pos_left hNpos).mp hrhs

/-! ### The Dirichlet choice over Ih -/

/-- The candidate views `s · G_gᵀ v`. -/
noncomputable def viewCandidate (v : Fin 3 → ℝ) (s : Bool) (g : IcoIndex) : Fin 3 → ℝ :=
  (if s then (1 : ℝ) else -1) • ((icoMatrix g)ᵀ *ᵥ v)

theorem exists_view_dirichlet (v : Fin 3 → ℝ) :
    ∃ s : Bool, ∃ g : IcoIndex, ∀ i, 0 ≤ wallValue (viewCandidate v s g) i := by
  obtain ⟨⟨s, g⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun sg : Bool × IcoIndex => viewCandidate v sg.1 sg.2 ⬝ᵥ viewCenter)
    Finset.univ_nonempty
  refine ⟨s, g, fun i => ?_⟩
  obtain ⟨k, hk⟩ := exists_icoMatrix_mul g (wallElem i)
  have hle := hmax (!s, k) (Finset.mem_univ _)
  -- G_kᵀ = H_i G_gᵀ, and H_i is symmetric.
  have hkT : (icoMatrix k)ᵀ = icoMatrix (wallElem i) * (icoMatrix g)ᵀ := by
    rw [← hk, Matrix.transpose_mul, wallElem_symm]
  set H := icoMatrix (wallElem i)
  set x := (icoMatrix g)ᵀ *ᵥ v
  have hsymdot : (H *ᵥ x) ⬝ᵥ viewCenter = x ⬝ᵥ (H *ᵥ viewCenter) := by
    have hs : Hᵀ = H := wallElem_symm i
    conv_rhs => rw [← hs]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
    ring
  have hcand : viewCandidate v (!s) k = (if (!s) then (1 : ℝ) else -1) • (H *ᵥ x) := by
    simp only [viewCandidate, hkT, ← Matrix.mulVec_mulVec, H, x]
  have hval : wallValue (viewCandidate v s g) i =
      2000 * (viewCandidate v s g ⬝ᵥ viewCenter -
        viewCandidate v (!s) k ⬝ᵥ viewCenter) := by
    rw [hcand, smul_dotProduct, hsymdot]
    simp only [wallValue, val_wallVec, viewCandidate, smul_dotProduct]
    change ∑ r, ((if s then (1 : ℝ) else -1) • x) r *
        (2000 * (viewCenter r + (H *ᵥ viewCenter) r)) = _
    cases s <;> simp [dotProduct, Fin.sum_univ_three] <;> ring
  rw [hval]
  have : viewCandidate v (!s) k ⬝ᵥ viewCenter ≤ viewCandidate v s g ⬝ᵥ viewCenter := hle
  linarith

/-! ### Realizing the reduced view by a pose -/

/-- Compose both rotations on the right with a rotation of I. -/
noncomputable def _root_.MatrixPose.bothRightIco (p : MatrixPose) (g : IcoIndex) : MatrixPose where
  innerRot := p.innerRot * icoSO3 g
  outerRot := p.outerRot * icoSO3 g
  innerOffset := p.innerOffset

/-- The view of a pose: the third row of its outer rotation. -/
noncomputable def _root_.MatrixPose.view (p : MatrixPose) : Fin 3 → ℝ :=
  fun k => p.outerRot.val 2 k

theorem view_bothRightIco (p : MatrixPose) (g : IcoIndex) :
    (p.bothRightIco g).view = viewCandidate p.view true g := by
  funext k
  simp [MatrixPose.view, MatrixPose.bothRightIco, icoSO3, viewCandidate, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply]
  ring

theorem view_viewAntipode (p : MatrixPose) : p.viewAntipode.view = -p.view := by
  funext k
  simp [MatrixPose.view, MatrixPose.viewAntipode, MatrixPose.viewAntipodeRotation,
    Matrix.mul_apply, Rx_mat, Fin.sum_univ_three]

namespace IModel

variable (P : IModel)

theorem outerShadow_bothRightIco (p : MatrixPose) (g : IcoIndex) :
    outerShadow (p.bothRightIco g) P.toC5.polyhedron.hull =
      outerShadow p P.toC5.polyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (icoMatrix g).toEuclideanLin v ∈ P.toC5.polyhedron.hull := by
      rw [← P.icoMatrix_image_hull g]
      exact ⟨v, hv, rfl⟩
    refine ⟨(icoMatrix g).toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.bothRightIco, icoSO3, PoseLike.outer, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (icoMatrix g).toEuclideanLin '' P.toC5.polyhedron.hull := by
      rwa [P.icoMatrix_image_hull g]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.bothRightIco, icoSO3, PoseLike.outer, Matrix.toLpLin_apply,
      Matrix.mulVec_mulVec]

theorem innerShadow_bothRightIco (p : MatrixPose) (g : IcoIndex) :
    innerShadow (p.bothRightIco g) P.toC5.polyhedron.hull =
      innerShadow p P.toC5.polyhedron.hull := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hgv : (icoMatrix g).toEuclideanLin v ∈ P.toC5.polyhedron.hull := by
      rw [← P.icoMatrix_image_hull g]
      exact ⟨v, hv, rfl⟩
    refine ⟨(icoMatrix g).toEuclideanLin v, hgv, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.bothRightIco, icoSO3,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ (icoMatrix g).toEuclideanLin '' P.toC5.polyhedron.hull := by
      rwa [P.icoMatrix_image_hull g]
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨u, hu, ?_⟩
    simp [MatrixPose.inner_apply, MatrixPose.bothRightIco, icoSO3,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem RupertPose_bothRightIco_iff (p : MatrixPose) (g : IcoIndex) :
    RupertPose (p.bothRightIco g) P.toC5.polyhedron.hull ↔
      RupertPose p P.toC5.polyhedron.hull := by
  simp only [RupertPose, P.innerShadow_bothRightIco, P.outerShadow_bothRightIco]

/-- Every pose is equivalent to one whose view lies in cone(T). -/
theorem exists_viewCone_pose (p : MatrixPose) :
    ∃ p' : MatrixPose, InViewCone p'.view ∧
      (RupertPose p' P.toC5.polyhedron.hull ↔ RupertPose p P.toC5.polyhedron.hull) := by
  obtain ⟨s, g, hwalls⟩ := exists_view_dirichlet p.view
  have hcone := inViewCone_of_walls hwalls
  cases s
  · refine ⟨(p.bothRightIco g).viewAntipode, ?_, ?_⟩
    · rw [view_viewAntipode, view_bothRightIco]
      convert hcone using 1
      funext k
      simp [viewCandidate]
    · rw [MatrixPose.RupertPose_viewAntipode_iff, P.RupertPose_bothRightIco_iff]
  · exact ⟨p.bothRightIco g, by rwa [view_bothRightIco], P.RupertPose_bothRightIco_iff p g⟩

end IModel

/-! ### cone(T) as a view triangle -/

open AtlasProjectiveView AtlasEdgeCertificate Noperthedron.Atlas.ProjectiveView in
/-- The rational view triangle T (`icoViewTriangleCorners`), in the root-0 face. -/
def icoViewTriangle : AtlasProjectiveView.Triangle ℚ :=
  fun k c => (icoViewTriangleCorners.getD k.val []).getD c.val 0

/-- Wall `(k + 1) % 3` of cone(T) is the one opposite corner `k`. -/
def oppositeWall (k : Fin 3) : Fin 3 := ⟨(k.val + 1) % 3, Nat.mod_lt _ (by omega)⟩

theorem viewCone_coords_nonneg {w : Fin 3 → ℝ} (h : InViewCone w) : ∀ c, 0 ≤ w c := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [triNormal, viewTriangleNormal, Fin.sum_univ_three] at h0 h1 h2
  intro c
  fin_cases c <;> simp <;> linarith

open AtlasProjectiveView AtlasEdgeCertificate Noperthedron.Atlas.ProjectiveView in
theorem viewCone_mem_icoViewTriangle (p : AtlasPose ℝ)
    (h : InViewCone fun c => viewVector p c) :
    1 ≤ viewScale 0 p ∧ InTriangle (toReal icoViewTriangle) (normalizedView 0 p) := by
  have hnn := viewCone_coords_nonneg h
  have hsign : ∀ c, 0 ≤ (rootSign 0 c : ℝ) * viewVector p c := by
    intro c
    fin_cases c <;> simpa [rootSign] using hnn _
  have hscale := one_le_viewScale_of_sign hsign
  have hscale0 : 0 < viewScale 0 p := lt_of_lt_of_le (by norm_num) hscale
  refine ⟨hscale, ?_⟩
  have hscaleEq : viewScale 0 p = viewVector p 0 + viewVector p 1 + viewVector p 2 := by
    simp [viewScale, rootSign, Fin.sum_univ_three]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [triNormal, viewTriangleNormal, Fin.sum_univ_three] at h0 h1 h2
  set x := viewVector p 0
  set y := viewVector p 1
  set z := viewVector p 2
  -- Barycentric weights: corner k gets its opposite wall's value, normalized.
  let weight : Fin 3 → ℝ := ![
    (-19 * x - 26 * y + 20 * z) / 20 / viewScale 0 p,
    (69 * x - 50 * y) / (26500 / 1343) / viewScale 0 p,
    (-8 * x + 25 * y) / (6625 / 1281) / viewScale 0 p]
  refine ⟨weight, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> simp [weight] <;> apply div_nonneg <;> try positivity
    all_goals first | linarith | exact hscale0.le
  · have hne : x + y + z ≠ 0 := hscaleEq ▸ hscale0.ne'
    simp only [weight, Fin.sum_univ_three]
    simp
    rw [hscaleEq]
    field_simp
    ring
  · funext c
    fin_cases c <;>
      simp [normalizedView, affinePoint, icoViewTriangle, icoViewTriangleCorners,
        Noperthedron.Atlas.ProjectiveView.toReal, weight, Fin.sum_univ_three] <;>
      field_simp <;> ring

end Noperthedron.Nopert231
