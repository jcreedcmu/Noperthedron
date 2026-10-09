module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Fin.VecNotation
public import Noperthedron.Atlas.ProjectiveLocalCertificate

@[expose] public section

open scoped BigOperators RealInnerProductSpace
open Noperthedron.Atlas.ProjectiveLocalCertificate

namespace Noperthedron.Nopert231

/-- Inductive quadtree certifying cap coverage by flock axes on an affine plane. -/
inductive QuadCoverTree where
  | outside : QuadCoverTree
  | covered (m : Nat) : QuadCoverTree
  | splitS (mid : ℚ) (left right : QuadCoverTree) : QuadCoverTree
  | splitT (mid : ℚ) (left right : QuadCoverTree) : QuadCoverTree
  deriving DecidableEq, Repr, Inhabited

/-- Orthogonal 2D basis on the affine plane H = {x : ⟨x, u0⟩ = c_cone}. -/
structure QuadBasis where
  u0 : Fin 3 → ℚ
  p0 : Fin 3 → ℚ
  e1 : Fin 3 → ℚ
  e2 : Fin 3 → ℚ
  D1 : ℚ
  D2 : ℚ
  normSqP0 : ℚ

def dotQ (a b : Fin 3 → ℚ) : ℚ :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2

def normSqQ (a : Fin 3 → ℚ) : ℚ :=
  dotQ a a

def computeQuadBasis (u0 : Fin 3 → ℚ) (c_cone : ℚ) : QuadBasis :=
  let u0_sq := normSqQ u0
  let p0 : Fin 3 → ℚ := fun i => (c_cone / u0_sq) * u0 i
  let e1 : Fin 3 → ℚ :=
    if u0 0 ≠ 0 ∨ u0 1 ≠ 0 then
      ![-(u0 1), u0 0, 0]
    else
      ![0, -(u0 2), u0 1]
  let e2 : Fin 3 → ℚ := ![
    u0 1 * e1 2 - u0 2 * e1 1,
    u0 2 * e1 0 - u0 0 * e1 2,
    u0 0 * e1 1 - u0 1 * e1 0
  ]
  {
    u0 := u0
    p0 := p0
    e1 := e1
    e2 := e2
    D1 := normSqQ e1
    D2 := normSqQ e2
    normSqP0 := normSqQ p0
  }

def minCoord (a b : ℚ) : ℚ :=
  if 0 < a then a else if b < 0 then -b else 0

def checkQuadCorner (b : QuadBasis) (axis : Fin 3 → ℚ) (c_core : ℚ) (s t : ℚ) : Bool :=
  let v : Fin 3 → ℚ := fun i => b.p0 i + s * b.e1 i + t * b.e2 i
  let d := dotQ v axis
  0 ≤ d && c_core^2 * normSqQ v ≤ d^2

def checkQuadTree (b : QuadBasis) (flock : Array (Fin 3 → ℚ)) (c_core : ℚ)
    (tree : QuadCoverTree) (s0 s1 t0 t1 : ℚ) : Bool :=
  match tree with
  | .outside =>
      let ms := minCoord s0 s1
      let mt := minCoord t0 t1
      1 < b.normSqP0 + ms^2 * b.D1 + mt^2 * b.D2
  | .covered m =>
      if h : m < flock.size then
        let axis := flock[m]
        checkQuadCorner b axis c_core s0 t0 &&
        checkQuadCorner b axis c_core s1 t0 &&
        checkQuadCorner b axis c_core s0 t1 &&
        checkQuadCorner b axis c_core s1 t1
      else false
  | .splitS mid left right =>
      s0 < mid && mid < s1 &&
      checkQuadTree b flock c_core left s0 mid t0 t1 &&
      checkQuadTree b flock c_core right mid s1 t0 t1
  | .splitT mid left right =>
      t0 < mid && mid < t1 &&
      checkQuadTree b flock c_core left s0 s1 t0 mid &&
      checkQuadTree b flock c_core right s0 s1 mid t1

def QuadCoverTree.Valid (tree : QuadCoverTree) (b : QuadBasis) (flock : Array (Fin 3 → ℚ)) (c_core : ℚ)
    (S_max T_max : ℚ) : Bool :=
  0 ≤ S_max && 0 ≤ T_max &&
  1 ≤ S_max^2 * b.D1 && 1 ≤ T_max^2 * b.D2 &&
  checkQuadTree b flock c_core tree (-S_max) S_max (-T_max) T_max

/-!
## Soundness of `QuadCoverTree.Valid`

`covers_of_valid` was previously an *axiom* stated for an arbitrary `b : QuadBasis`.
That statement is false: `QuadBasis` is a bare record, so nothing ties `normSqP0`, `D1`,
`D2` to the vectors `p0`, `e1`, `e2`. For instance with
`b := { u0 := ![1,0,0], p0 := 0, e1 := 0, e2 := 0, D1 := 1, D2 := 1, normSqP0 := 2 }`,
the empty flock, `c_cone := 1/2`, `S_max = T_max = 1` and `tree := .outside`, the root
leaf check `1 < normSqP0 + 0 + 0` passes, while the unit axis `![1,0,0]` lies in the
cap; the conclusion `∃ m : Fin 0, _` then gives `False`.

The theorem below is stated for the basis actually used, `computeQuadBasis u0 c_cone`,
whose `p0 = (c_cone/|u0|²) u0`, `e1 ⊥ u0`, `e2 = u0 × e1` form an orthogonal frame with
`D1 = |e1|²`, `D2 = |e2|²`, `normSqP0 = |p0|²`. The proof: for a unit `a` in the cap,
`x := (c_cone/⟨a,u0⟩) a` lies on the plane `⟨x,u0⟩ = c_cone` with `|x| ≤ 1`, so
`x = p0 + s e1 + t e2` with `|x|² = normSqP0 + s² D1 + t² D2` and `(s,t)` in the root box;
`checkQuadTree_sound` follows the tree to the leaf containing `(s,t)`: an `.outside` leaf
would force `|x| > 1`, and at a `.covered m` leaf the concave function
`z ↦ ⟨z, flock[m]⟩ - c_core |z|` is nonnegative at the four corners, hence on the
rectangle (`cone_rect`), giving `c_core |x| ≤ ⟨x, flock[m]⟩`; divide by `|x|`.
-/

namespace QuadCoverTree

theorem inner_eq_sum3 (x y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem norm_sq_eq_sum3 (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum3]; ring

theorem inner_toR3_toR3 (v w : Fin 3 → ℚ) :
    inner ℝ (toR3 v) (toR3 w) = ((dotQ v w : ℚ) : ℝ) := by
  rw [inner_eq_sum3]; simp [toR3, dotQ]

theorem norm_sq_toR3 (v : Fin 3 → ℚ) : ‖toR3 v‖ ^ 2 = ((normSqQ v : ℚ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_toR3_toR3]; rfl

/-- The affine parametrization `(s, t) ↦ p0 + s e1 + t e2` of the plane. -/
noncomputable def planePt (b : QuadBasis) (s t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  toR3 b.p0 + s • toR3 b.e1 + t • toR3 b.e2

theorem toR3_corner (b : QuadBasis) (s t : ℚ) :
    toR3 (fun i => b.p0 i + s * b.e1 i + t * b.e2 i) = planePt b s t := by
  ext i; simp [planePt, toR3]

/-- `z ↦ ⟨z, f⟩ - c‖z‖` is concave, so its nonnegativity passes to segments. -/
theorem cone_segment {A B f : EuclideanSpace ℝ (Fin 3)} {c σ0 σ1 σ : ℝ} (hc : 0 ≤ c)
    (h0 : c * ‖A + σ0 • B‖ ≤ inner ℝ (A + σ0 • B) f)
    (h1 : c * ‖A + σ1 • B‖ ≤ inner ℝ (A + σ1 • B) f)
    (hσ0 : σ0 ≤ σ) (hσ1 : σ ≤ σ1) :
    c * ‖A + σ • B‖ ≤ inner ℝ (A + σ • B) f := by
  rcases eq_or_lt_of_le (hσ0.trans hσ1) with heq | hlt
  · have : σ = σ0 := le_antisymm (heq ▸ hσ1) hσ0
    subst this; exact h0
  · set α := (σ - σ0) / (σ1 - σ0) with hα
    have hpos : 0 < σ1 - σ0 := by linarith
    have hα0 : 0 ≤ α := div_nonneg (by linarith) hpos.le
    have hα1 : α ≤ 1 := (div_le_one hpos).2 (by linarith)
    have hσ : σ = (1 - α) * σ0 + α * σ1 := by
      rw [hα]; field_simp; ring
    have hrepr : A + σ • B = (1 - α) • (A + σ0 • B) + α • (A + σ1 • B) := by
      rw [hσ]; module
    rw [hrepr]
    have hn : ‖(1 - α) • (A + σ0 • B) + α • (A + σ1 • B)‖ ≤
        (1 - α) * ‖A + σ0 • B‖ + α * ‖A + σ1 • B‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hα0]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    nlinarith [mul_le_mul_of_nonneg_left hn hc, mul_le_mul_of_nonneg_left h0 (sub_nonneg.2 hα1),
      mul_le_mul_of_nonneg_left h1 hα0]

theorem cone_rect (b : QuadBasis) (f : EuclideanSpace ℝ (Fin 3)) {c : ℝ} (hc : 0 ≤ c)
    {s0 s1 t0 t1 s t : ℝ} (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (ht0 : t0 ≤ t) (ht1 : t ≤ t1)
    (h00 : c * ‖planePt b s0 t0‖ ≤ inner ℝ (planePt b s0 t0) f)
    (h10 : c * ‖planePt b s1 t0‖ ≤ inner ℝ (planePt b s1 t0) f)
    (h01 : c * ‖planePt b s0 t1‖ ≤ inner ℝ (planePt b s0 t1) f)
    (h11 : c * ‖planePt b s1 t1‖ ≤ inner ℝ (planePt b s1 t1) f) :
    c * ‖planePt b s t‖ ≤ inner ℝ (planePt b s t) f := by
  have key : ∀ s' t', planePt b s' t' = (toR3 b.p0 + t' • toR3 b.e2) + s' • toR3 b.e1 := by
    intro s' t'; simp only [planePt]; abel
  have key2 : ∀ s' t', planePt b s' t' = (toR3 b.p0 + s' • toR3 b.e1) + t' • toR3 b.e2 :=
    fun _ _ => rfl
  have hA : c * ‖planePt b s t0‖ ≤ inner ℝ (planePt b s t0) f := by
    rw [key] at h00 h10 ⊢; exact cone_segment hc h00 h10 hs0 hs1
  have hB : c * ‖planePt b s t1‖ ≤ inner ℝ (planePt b s t1) f := by
    rw [key] at h01 h11 ⊢; exact cone_segment hc h01 h11 hs0 hs1
  rw [key2] at hA hB ⊢
  exact cone_segment hc hA hB ht0 ht1

theorem corner_cone (b : QuadBasis) (f : Fin 3 → ℚ) {c : ℚ} (hc : 0 ≤ c) (s t : ℚ)
    (h : checkQuadCorner b f c s t = true) :
    (c : ℝ) * ‖planePt b s t‖ ≤ inner ℝ (planePt b s t) (toR3 f) := by
  simp only [checkQuadCorner, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hd, hsq⟩ := h
  rw [← toR3_corner, inner_toR3_toR3]
  have hn := norm_sq_toR3 (fun i => b.p0 i + s * b.e1 i + t * b.e2 i)
  have hd' : (0 : ℝ) ≤ ((dotQ (fun i => b.p0 i + s * b.e1 i + t * b.e2 i) f : ℚ) : ℝ) := by
    exact_mod_cast hd
  have hsq' : ((c : ℝ) * ‖toR3 (fun i => b.p0 i + s * b.e1 i + t * b.e2 i)‖) ^ 2 ≤
      ((dotQ (fun i => b.p0 i + s * b.e1 i + t * b.e2 i) f : ℚ) : ℝ) ^ 2 := by
    rw [mul_pow, hn]; exact_mod_cast hsq
  have hcn : 0 ≤ (c : ℝ) * ‖toR3 (fun i => b.p0 i + s * b.e1 i + t * b.e2 i)‖ :=
    mul_nonneg (by exact_mod_cast hc) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ hcn hd' two_ne_zero).1 hsq'

theorem minCoord_sq_le (a b : ℚ) (x : ℝ) (ha : (a : ℝ) ≤ x) (hb : x ≤ b) :
    ((minCoord a b : ℚ) : ℝ) ^ 2 ≤ x ^ 2 := by
  unfold minCoord
  split_ifs with h1 h2
  · have : (0 : ℝ) < a := by exact_mod_cast h1
    nlinarith
  · have : (b : ℝ) < 0 := by exact_mod_cast h2
    push_cast; nlinarith
  · simpa using sq_nonneg x

/-- Soundness of `checkQuadTree` for a basis whose `normSqP0`, `D1`, `D2` really are
the squared lengths along the (orthogonal) parametrization `planePt`. -/
theorem checkQuadTree_sound (b : QuadBasis) (flock : Array (Fin 3 → ℚ)) (c_core : ℚ)
    (hc : 0 ≤ c_core) (hD1 : 0 ≤ (b.D1 : ℝ)) (hD2 : 0 ≤ (b.D2 : ℝ))
    (hnorm : ∀ s t : ℝ, ‖planePt b s t‖ ^ 2 = b.normSqP0 + s ^ 2 * b.D1 + t ^ 2 * b.D2)
    (s t : ℝ) (hunit : ‖planePt b s t‖ ≤ 1) :
    ∀ (tree : QuadCoverTree) (s0 s1 t0 t1 : ℚ),
      checkQuadTree b flock c_core tree s0 s1 t0 t1 = true →
      (s0 : ℝ) ≤ s → s ≤ s1 → (t0 : ℝ) ≤ t → t ≤ t1 →
      ∃ m : Fin flock.size,
        (c_core : ℝ) * ‖planePt b s t‖ ≤ inner ℝ (planePt b s t) (toR3 flock[m])
  | .outside, s0, s1, t0, t1, h, hs0, hs1, ht0, ht1 => by
      exfalso
      simp only [checkQuadTree, decide_eq_true_eq] at h
      have h' : (1 : ℝ) < b.normSqP0 + ((minCoord s0 s1 : ℚ) : ℝ) ^ 2 * b.D1 +
          ((minCoord t0 t1 : ℚ) : ℝ) ^ 2 * b.D2 := by exact_mod_cast h
      have hs := mul_le_mul_of_nonneg_right (minCoord_sq_le s0 s1 s hs0 hs1) hD1
      have ht := mul_le_mul_of_nonneg_right (minCoord_sq_le t0 t1 t ht0 ht1) hD2
      have hn := hnorm s t
      have : ‖planePt b s t‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hunit
      linarith
  | .covered m, s0, s1, t0, t1, h, hs0, hs1, ht0, ht1 => by
      simp only [checkQuadTree] at h
      split_ifs at h with hm
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨h00, h10⟩, h01⟩, h11⟩ := h
      exact ⟨⟨m, hm⟩, cone_rect b _ (by exact_mod_cast hc) hs0 hs1 ht0 ht1
        (corner_cone b _ hc _ _ h00) (corner_cone b _ hc _ _ h10)
        (corner_cone b _ hc _ _ h01) (corner_cone b _ hc _ _ h11)⟩
  | .splitS mid l r, s0, s1, t0, t1, h, hs0, hs1, ht0, ht1 => by
      simp only [checkQuadTree, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨_, _⟩, hl⟩, hr⟩ := h
      rcases le_total s mid with hsm | hsm
      · exact checkQuadTree_sound b flock c_core hc hD1 hD2 hnorm s t hunit l s0 mid t0 t1
          hl hs0 hsm ht0 ht1
      · exact checkQuadTree_sound b flock c_core hc hD1 hD2 hnorm s t hunit r mid s1 t0 t1
          hr hsm hs1 ht0 ht1
  | .splitT mid l r, s0, s1, t0, t1, h, hs0, hs1, ht0, ht1 => by
      simp only [checkQuadTree, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨_, _⟩, hl⟩, hr⟩ := h
      rcases le_total t mid with htm | htm
      · exact checkQuadTree_sound b flock c_core hc hD1 hD2 hnorm s t hunit l s0 s1 t0 mid
          hl hs0 hs1 ht0 htm
      · exact checkQuadTree_sound b flock c_core hc hD1 hD2 hnorm s t hunit r s0 s1 mid t1
          hr hs0 hs1 htm ht1


/-! ### The frame produced by `computeQuadBasis` -/

theorem computeQuadBasis_p0 (u0 : Fin 3 → ℚ) (c : ℚ) :
    (computeQuadBasis u0 c).p0 = fun i => c / normSqQ u0 * u0 i := rfl

theorem computeQuadBasis_e2 (u0 : Fin 3 → ℚ) (c : ℚ) :
    (computeQuadBasis u0 c).e2 = ![
      u0 1 * (computeQuadBasis u0 c).e1 2 - u0 2 * (computeQuadBasis u0 c).e1 1,
      u0 2 * (computeQuadBasis u0 c).e1 0 - u0 0 * (computeQuadBasis u0 c).e1 2,
      u0 0 * (computeQuadBasis u0 c).e1 1 - u0 1 * (computeQuadBasis u0 c).e1 0] := rfl

theorem dotQ_u0_e1 (u0 : Fin 3 → ℚ) (c : ℚ) : dotQ u0 (computeQuadBasis u0 c).e1 = 0 := by
  simp only [computeQuadBasis]
  split_ifs <;> simp [dotQ] <;> ring

theorem normSqQ_e1_pos (u0 : Fin 3 → ℚ) (c : ℚ) (hu : 0 < normSqQ u0) :
    0 < normSqQ (computeQuadBasis u0 c).e1 := by
  simp only [normSqQ, dotQ] at hu
  simp only [computeQuadBasis]
  split_ifs with h
  · simp only [normSqQ, dotQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rcases h with h | h
    · nlinarith [mul_self_pos.2 h, mul_self_nonneg (u0 1)]
    · nlinarith [mul_self_pos.2 h, mul_self_nonneg (u0 0)]
  · push Not at h
    obtain ⟨h0, h1⟩ := h
    simp only [normSqQ, dotQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, h0, h1] at hu ⊢
    nlinarith

theorem dotQ_p0_e1 (u0 : Fin 3 → ℚ) (c : ℚ) :
    dotQ (computeQuadBasis u0 c).p0 (computeQuadBasis u0 c).e1 = 0 := by
  have h := dotQ_u0_e1 u0 c
  rw [computeQuadBasis_p0]
  simp only [dotQ] at h ⊢
  linear_combination (c / normSqQ u0) * h

theorem dotQ_p0_e2 (u0 : Fin 3 → ℚ) (c : ℚ) :
    dotQ (computeQuadBasis u0 c).p0 (computeQuadBasis u0 c).e2 = 0 := by
  rw [computeQuadBasis_p0, computeQuadBasis_e2]
  simp only [dotQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dotQ_e1_e2 (u0 : Fin 3 → ℚ) (c : ℚ) :
    dotQ (computeQuadBasis u0 c).e1 (computeQuadBasis u0 c).e2 = 0 := by
  rw [computeQuadBasis_e2]
  simp only [dotQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem normSqQ_e2 (u0 : Fin 3 → ℚ) (c : ℚ) :
    normSqQ (computeQuadBasis u0 c).e2 = normSqQ u0 * normSqQ (computeQuadBasis u0 c).e1 := by
  have h := dotQ_u0_e1 u0 c
  rw [computeQuadBasis_e2]
  simp only [normSqQ, dotQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h ⊢
  linear_combination (-(u0 0 * (computeQuadBasis u0 c).e1 0 + u0 1 * (computeQuadBasis u0 c).e1 1 +
    u0 2 * (computeQuadBasis u0 c).e1 2)) * h

/-- Pythagoras in the orthogonal frame `p0, e1, e2`. -/
theorem norm_sq_planePt (u0 : Fin 3 → ℚ) (c : ℚ) (s t : ℝ) :
    ‖planePt (computeQuadBasis u0 c) s t‖ ^ 2 =
      ((computeQuadBasis u0 c).normSqP0 : ℝ) + s ^ 2 * (computeQuadBasis u0 c).D1 +
        t ^ 2 * (computeQuadBasis u0 c).D2 := by
  have h01 := inner_toR3_toR3 (computeQuadBasis u0 c).p0 (computeQuadBasis u0 c).e1
  have h02 := inner_toR3_toR3 (computeQuadBasis u0 c).p0 (computeQuadBasis u0 c).e2
  have h12 := inner_toR3_toR3 (computeQuadBasis u0 c).e1 (computeQuadBasis u0 c).e2
  rw [dotQ_p0_e1, Rat.cast_zero] at h01
  rw [dotQ_p0_e2, Rat.cast_zero] at h02
  rw [dotQ_e1_e2, Rat.cast_zero] at h12
  have hP := norm_sq_toR3 (computeQuadBasis u0 c).p0
  have hE1 := norm_sq_toR3 (computeQuadBasis u0 c).e1
  have hE2 := norm_sq_toR3 (computeQuadBasis u0 c).e2
  show _ = ((normSqQ (computeQuadBasis u0 c).p0 : ℚ) : ℝ) +
    s ^ 2 * ((normSqQ (computeQuadBasis u0 c).e1 : ℚ) : ℝ) +
    t ^ 2 * ((normSqQ (computeQuadBasis u0 c).e2 : ℚ) : ℝ)
  rw [← hP, ← hE1, ← hE2, planePt, norm_add_sq_real, norm_add_sq_real, norm_smul, norm_smul,
    inner_add_left]
  simp only [real_inner_smul_left, real_inner_smul_right, h01, h02, h12, mul_pow,
    Real.norm_eq_abs, sq_abs]
  ring

/-- The orthogonal frame `u, e, u × e` spans: every `x` is recovered from its coordinates. -/
theorem frame_decomp (x0 x1 x2 u0 u1 u2 e0 e1 e2 : ℝ) (hk : u0 * e0 + u1 * e1 + u2 * e2 = 0) :
    let nU := u0 * u0 + u1 * u1 + u2 * u2
    let nE := e0 * e0 + e1 * e1 + e2 * e2
    let w0 := u1 * e2 - u2 * e1
    let w1 := u2 * e0 - u0 * e2
    let w2 := u0 * e1 - u1 * e0
    let xu := x0 * u0 + x1 * u1 + x2 * u2
    let xe := x0 * e0 + x1 * e1 + x2 * e2
    let xw := x0 * w0 + x1 * w1 + x2 * w2
    x0 * (nU * nE) = xu * nE * u0 + xe * nU * e0 + xw * w0 ∧
    x1 * (nU * nE) = xu * nE * u1 + xe * nU * e1 + xw * w1 ∧
    x2 * (nU * nE) = xu * nE * u2 + xe * nU * e2 + xw * w2 := by
  intro nU nE w0 w1 w2 xu xe xw
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (x0 * (u0 * e0 + u1 * e1 + u2 * e2) - xe * u0 - xu * e0) * hk
  · linear_combination (x1 * (u0 * e0 + u1 * e1 + u2 * e2) - xe * u1 - xu * e1) * hk
  · linear_combination (x2 * (u0 * e0 + u1 * e1 + u2 * e2) - xe * u2 - xu * e2) * hk


/-- Coordinates of a point `x` with `⟨x, u⟩ = c` in the frame `p0 = (c/|u|²) u, e, u × e`
(`u ⊥ e`, both nonzero). -/
theorem frame_solve (x0 x1 x2 u0 u1 u2 e0 e1 e2 c : ℝ) (hk : u0 * e0 + u1 * e1 + u2 * e2 = 0)
    (hnU : u0 * u0 + u1 * u1 + u2 * u2 ≠ 0) (hnE : e0 * e0 + e1 * e1 + e2 * e2 ≠ 0)
    (hxu : x0 * u0 + x1 * u1 + x2 * u2 = c) (s t : ℝ)
    (hs : s = (x0 * e0 + x1 * e1 + x2 * e2) / (e0 * e0 + e1 * e1 + e2 * e2))
    (ht : t = (x0 * (u1 * e2 - u2 * e1) + x1 * (u2 * e0 - u0 * e2) + x2 * (u0 * e1 - u1 * e0)) /
      ((u1 * e2 - u2 * e1) * (u1 * e2 - u2 * e1) + (u2 * e0 - u0 * e2) * (u2 * e0 - u0 * e2) +
        (u0 * e1 - u1 * e0) * (u0 * e1 - u1 * e0))) :
    x0 = c / (u0 * u0 + u1 * u1 + u2 * u2) * u0 + s * e0 + t * (u1 * e2 - u2 * e1) ∧
    x1 = c / (u0 * u0 + u1 * u1 + u2 * u2) * u1 + s * e1 + t * (u2 * e0 - u0 * e2) ∧
    x2 = c / (u0 * u0 + u1 * u1 + u2 * u2) * u2 + s * e2 + t * (u0 * e1 - u1 * e0) := by
  have hW : (u1 * e2 - u2 * e1) * (u1 * e2 - u2 * e1) + (u2 * e0 - u0 * e2) * (u2 * e0 - u0 * e2) +
      (u0 * e1 - u1 * e0) * (u0 * e1 - u1 * e0) =
      (u0 * u0 + u1 * u1 + u2 * u2) * (e0 * e0 + e1 * e1 + e2 * e2) := by
    linear_combination (-(u0 * e0 + u1 * e1 + u2 * e2)) * hk
  rw [hW] at ht
  obtain ⟨h0, h1, h2⟩ := frame_decomp x0 x1 x2 u0 u1 u2 e0 e1 e2 hk
  rw [hxu] at h0 h1 h2
  subst hs ht
  generalize u0 * u0 + u1 * u1 + u2 * u2 = nU at *
  generalize e0 * e0 + e1 * e1 + e2 * e2 = nE at *
  generalize x0 * e0 + x1 * e1 + x2 * e2 = xe at *
  generalize x0 * (u1 * e2 - u2 * e1) + x1 * (u2 * e0 - u0 * e2) + x2 * (u0 * e1 - u1 * e0) = xw at *
  refine ⟨?_, ?_, ?_⟩
  · field_simp; linear_combination h0
  · field_simp; linear_combination h1
  · field_simp; linear_combination h2


/-- Soundness of the rational quadtree witness: every unit vector in the spherical cap
`⟨axis, u0⟩ ≥ c_cone` is within `c_core` of some flock axis. -/
theorem covers_of_valid
    (u0 : Fin 3 → ℚ) (flock : Array (Fin 3 → ℚ)) (c_cone c_core : ℚ)
    (S_max T_max : ℚ) (tree : QuadCoverTree)
    (hvalid : tree.Valid (computeQuadBasis u0 c_cone) flock c_core S_max T_max = true)
    (hc_cone : 0 < c_cone) (hc_core : 0 ≤ c_core)
    (axis : EuclideanSpace ℝ (Fin 3)) (haxis_norm : ‖axis‖ = 1)
    (haxis_cone : (c_cone : ℝ) ≤ inner ℝ axis (toR3 u0)) :
    ∃ m : Fin flock.size, (c_core : ℝ) ≤ inner ℝ axis (toR3 (flock[m])) := by
  simp only [QuadCoverTree.Valid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  obtain ⟨⟨⟨⟨hS0, hT0⟩, hSD⟩, hTD⟩, hcheck⟩ := hvalid
  have hc : (0 : ℝ) < c_cone := by exact_mod_cast hc_cone
  have hdpos : 0 < inner ℝ axis (toR3 u0) := lt_of_lt_of_le hc haxis_cone
  have hUn : inner ℝ axis (toR3 u0) ≤ ‖toR3 u0‖ := by
    have := real_inner_le_norm axis (toR3 u0)
    rwa [haxis_norm, one_mul] at this
  have hnU : 0 < normSqQ u0 := by
    have h1 : (0 : ℝ) < ‖toR3 u0‖ ^ 2 := by
      have := hdpos.trans_le hUn
      positivity
    rw [norm_sq_toR3] at h1
    exact_mod_cast h1
  have hnE := normSqQ_e1_pos u0 c_cone hnU
  have hD1 : (0 : ℝ) < (computeQuadBasis u0 c_cone).D1 := by
    show (0 : ℝ) < ((normSqQ (computeQuadBasis u0 c_cone).e1 : ℚ) : ℝ)
    exact_mod_cast hnE
  have hD2 : (0 : ℝ) < (computeQuadBasis u0 c_cone).D2 := by
    show (0 : ℝ) < ((normSqQ (computeQuadBasis u0 c_cone).e2 : ℚ) : ℝ)
    rw [normSqQ_e2]
    exact_mod_cast mul_pos hnU hnE
  have hP0 : (0 : ℝ) ≤ (computeQuadBasis u0 c_cone).normSqP0 := by
    show (0 : ℝ) ≤ ((normSqQ (computeQuadBasis u0 c_cone).p0 : ℚ) : ℝ)
    rw [← norm_sq_toR3]
    positivity
  -- the point `x = lam • axis` of the plane `⟨x, u0⟩ = c_cone`
  set lam : ℝ := (c_cone : ℝ) / inner ℝ axis (toR3 u0) with hlam
  have hlam0 : 0 < lam := div_pos hc hdpos
  have hlam1 : lam ≤ 1 := (div_le_one hdpos).2 haxis_cone
  have hxnorm : ‖lam • axis‖ = lam := by
    rw [norm_smul, haxis_norm, Real.norm_of_nonneg hlam0.le, mul_one]
  have hxu : inner ℝ (lam • axis) (toR3 u0) = c_cone := by
    rw [real_inner_smul_left, hlam]
    field_simp
  set b := computeQuadBasis u0 c_cone with hb
  set s : ℝ := inner ℝ (lam • axis) (toR3 b.e1) / b.D1 with hs
  set t : ℝ := inner ℝ (lam • axis) (toR3 b.e2) / b.D2 with ht
  have hx : planePt b s t = lam • axis := by
    have hk := dotQ_u0_e1 u0 c_cone
    have hnU' := hnU.ne'
    have hnE' := hnE.ne'
    rw [inner_eq_sum3] at hxu
    rw [inner_eq_sum3] at hs
    rw [inner_eq_sum3] at ht
    rw [← hb] at hk
    simp only [dotQ, normSqQ] at hk hnU' hnE'
    have hk' : ((u0 0 : ℚ) : ℝ) * (b.e1 0 : ℝ) + (u0 1 : ℝ) * (b.e1 1 : ℝ) +
        (u0 2 : ℝ) * (b.e1 2 : ℝ) = 0 := by exact_mod_cast hk
    have hnU'' : ((u0 0 : ℚ) : ℝ) * (u0 0 : ℝ) + (u0 1 : ℝ) * (u0 1 : ℝ) +
        (u0 2 : ℝ) * (u0 2 : ℝ) ≠ 0 := by exact_mod_cast hnU'
    have hnE'' : ((b.e1 0 : ℚ) : ℝ) * (b.e1 0 : ℝ) + (b.e1 1 : ℝ) * (b.e1 1 : ℝ) +
        (b.e1 2 : ℝ) * (b.e1 2 : ℝ) ≠ 0 := by exact_mod_cast hnE'
    have hD1e : (b.D1 : ℝ) = ((b.e1 0 : ℚ) : ℝ) * (b.e1 0 : ℝ) + (b.e1 1 : ℝ) * (b.e1 1 : ℝ) +
        (b.e1 2 : ℝ) * (b.e1 2 : ℝ) := by
      show ((normSqQ b.e1 : ℚ) : ℝ) = _
      simp [normSqQ, dotQ]
    have he2 : b.e2 = ![u0 1 * b.e1 2 - u0 2 * b.e1 1, u0 2 * b.e1 0 - u0 0 * b.e1 2,
        u0 0 * b.e1 1 - u0 1 * b.e1 0] := computeQuadBasis_e2 u0 c_cone
    have hD2e : (b.D2 : ℝ) = ((normSqQ b.e2 : ℚ) : ℝ) := rfl
    have hp0 : b.p0 = fun i => c_cone / normSqQ u0 * u0 i := computeQuadBasis_p0 u0 c_cone
    rw [hD1e] at hs
    rw [hD2e, he2] at ht
    simp only [toR3, normSqQ, dotQ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hs ht hxu
    push_cast at hs ht hxu
    obtain ⟨h0, h1, h2⟩ := frame_solve _ _ _ _ _ _ _ _ _ _ hk' hnU'' hnE'' hxu s t hs ht
    ext i
    fin_cases i
    · simp only [planePt, toR3, hp0, he2, normSqQ, dotQ]
      simpa using h0.symm
    · simp only [planePt, toR3, hp0, he2, normSqQ, dotQ]
      simpa using h1.symm
    · simp only [planePt, toR3, hp0, he2, normSqQ, dotQ]
      simpa using h2.symm
  -- `(s, t)` lies in the root box
  have hst := norm_sq_planePt u0 c_cone s t
  rw [← hb, hx, hxnorm] at hst
  have hlam2 : lam ^ 2 ≤ 1 := pow_le_one₀ hlam0.le hlam1
  have hSD' : (1 : ℝ) ≤ (S_max : ℝ) ^ 2 * b.D1 := by exact_mod_cast hSD
  have hTD' : (1 : ℝ) ≤ (T_max : ℝ) ^ 2 * b.D2 := by exact_mod_cast hTD
  have hss : s ^ 2 ≤ (S_max : ℝ) ^ 2 := by
    have : s ^ 2 * b.D1 ≤ (S_max : ℝ) ^ 2 * b.D1 := by nlinarith [sq_nonneg t]
    exact le_of_mul_le_mul_right this hD1
  have htt : t ^ 2 ≤ (T_max : ℝ) ^ 2 := by
    have : t ^ 2 * b.D2 ≤ (T_max : ℝ) ^ 2 * b.D2 := by nlinarith [sq_nonneg s]
    exact le_of_mul_le_mul_right this hD2
  obtain ⟨hs0, hs1⟩ := abs_le_of_sq_le_sq' hss (by exact_mod_cast hS0)
  obtain ⟨ht0, ht1⟩ := abs_le_of_sq_le_sq' htt (by exact_mod_cast hT0)
  obtain ⟨m, hm⟩ := checkQuadTree_sound b flock c_core hc_core hD1.le hD2.le
    (norm_sq_planePt u0 c_cone) s t (by rw [hx, hxnorm]; exact hlam1)
    tree (-S_max) S_max (-T_max) T_max hcheck (by push_cast; exact hs0) hs1
    (by push_cast; exact ht0) ht1
  refine ⟨m, ?_⟩
  rw [hx, hxnorm, real_inner_smul_left] at hm
  nlinarith

end QuadCoverTree

end Noperthedron.Nopert231
