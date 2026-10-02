module

public import Noperthedron.Nopert229.TightApproximation

@[expose] public section

/-!
# Idealized #231: exact fivefold symmetry and exactly planar quads

`exactVertex` (the verified model) rotates the rational seeds exactly, so its
quads are only planar to about `2e-16`. Idealized #231 keeps seeds 0, 2, 3
and seed 1's x and y, and replaces seed 1's z by `z1`, the unique height that
puts seed 1 in the plane through seed 2, seed 3 and seed 2 rotated by `-72°`.
Then the quad `{v₁, v₂, v₃, v₁₈}` is exactly planar, and so are its four
rotations (`quad_planar`).

`model` packages it as a `C5Model`: every vertex is within `6e-16` of
`rationalVertex` (in fact `4.1e-16`), so the certificates cover it. The bound
goes through `vertexH`, the same construction with 40-digit rational
enclosures of the rotations and of `z1`; `vertexH` is compared with
`rationalVertex` exactly by `decide +kernel`. See nopert229/notes/IDEAL231.md.
-/

open Real

namespace Noperthedron.Nopert229.Ideal231

/-! ### 40-digit rational enclosures of cos and sin of 72° and 144° -/

def cos72H : ℚ := 3090169943749474241022934171828190588602 / 10^40
def sin72H : ℚ := 9510565162951535721164393333793821434057 / 10^40
def cos144H : ℚ := -8090169943749474241022934171828190588602 / 10^40
def sin144H : ℚ := 5877852522924731291687059546390727685977 / 10^40

/-- The error allowed in each trigonometric enclosure (72° enclosures are
ten times tighter, so the 144° double-angle bounds stay within it). -/
def trigErrQ : ℚ := 1 / 10^38
def err72Q : ℚ := 1 / 10^39

theorem sqrt5_bounds :
    (22360679774997896964091736687312762354405 / 10^40 : ℝ) ≤ √5 ∧
      √5 ≤ (22360679774997896964091736687312762354407 / 10^40 : ℝ) := by
  have h0 : 0 ≤ √5 := Real.sqrt_nonneg _
  have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  constructor
  · nlinarith [sq_nonneg (√5 - 22360679774997896964091736687312762354405 / 10^40)]
  · nlinarith [sq_nonneg (√5 - 22360679774997896964091736687312762354407 / 10^40)]

theorem cos72_eq : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [hsq]

theorem cos72_close : |Real.cos (2 * π / 5) - (cos72H : ℝ)| ≤ (err72Q : ℝ) := by
  obtain ⟨hlo, hhi⟩ := sqrt5_bounds
  rw [cos72_eq, abs_le]
  norm_num [cos72H, err72Q]
  constructor <;> linarith

theorem sin72_close : |Real.sin (2 * π / 5) - (sin72H : ℝ)| ≤ (err72Q : ℝ) := by
  have hpos : 0 < Real.sin (2 * π / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc := cos72_close
  have htrig := Real.sin_sq_add_cos_sq (2 * π / 5)
  rw [abs_le] at hc ⊢
  norm_num [cos72H, sin72H, err72Q] at hc ⊢
  obtain ⟨hcl, hcu⟩ := hc
  constructor <;> nlinarith [
    sq_nonneg (Real.sin (2 * π / 5) - (9510565162951535721164393333793821434057 / 10^40 - 1 / 10^39)),
    sq_nonneg (Real.sin (2 * π / 5) - (9510565162951535721164393333793821434057 / 10^40 + 1 / 10^39))]

theorem cos144_close : |Real.cos (4 * π / 5) - (cos144H : ℝ)| ≤ (trigErrQ : ℝ) := by
  have hc := cos72_close
  rw [show 4 * π / 5 = 2 * (2 * π / 5) by ring, Real.cos_two_mul]
  rw [abs_le] at hc ⊢
  norm_num [cos72H, cos144H, err72Q, trigErrQ] at hc ⊢
  obtain ⟨hcl, hcu⟩ := hc
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hcl) (sub_nonneg.2 hcu),
    sq_nonneg (Real.cos (2 * π / 5) - 3090169943749474241022934171828190588602 / 10^40)]

theorem sin144_close : |Real.sin (4 * π / 5) - (sin144H : ℝ)| ≤ (trigErrQ : ℝ) := by
  have hc := cos72_close
  have hs := sin72_close
  rw [show 4 * π / 5 = 2 * (2 * π / 5) by ring, Real.sin_two_mul]
  rw [abs_le] at hc hs ⊢
  norm_num [cos72H, sin72H, sin144H, err72Q, trigErrQ] at hc hs ⊢
  obtain ⟨hcl, hcu⟩ := hc
  obtain ⟨hsl, hsu⟩ := hs
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hcl) (sub_nonneg.2 hsl),
    mul_nonneg (sub_nonneg.2 hcu) (sub_nonneg.2 hsu),
    mul_nonneg (sub_nonneg.2 hcl) (sub_nonneg.2 hsu),
    mul_nonneg (sub_nonneg.2 hcu) (sub_nonneg.2 hsl)]

/-- Rotation enclosures by orbit, as `TightApproximation.tightCos/tightSin`. -/
def cosH : OrbitIndex → ℚ := ![1, cos72H, cos144H, cos144H, cos72H]
def sinH : OrbitIndex → ℚ := ![0, sin72H, sin144H, -sin144H, -sin72H]

theorem cosH_close (k : OrbitIndex) :
    |((cosH k : ℚ) : ℝ) - Real.cos (2 * π * (k : ℝ) / 5)| ≤ (trigErrQ : ℝ) := by
  fin_cases k
  · norm_num [cosH, trigErrQ]
  · simpa [cosH, abs_sub_comm] using cos72_close.trans (by norm_num [err72Q, trigErrQ])
  · simpa [cosH, show 2 * π * (2 : ℝ) / 5 = 4 * π / 5 by ring, abs_sub_comm]
      using cos144_close
  · norm_num [cosH]
    rw [show 2 * π * (3 : ℝ) / 5 = 2 * π - 4 * π / 5 by ring, Real.cos_two_pi_sub]
    simpa [abs_sub_comm] using cos144_close
  · norm_num [cosH]
    rw [show 2 * π * (4 : ℝ) / 5 = 2 * π - 2 * π / 5 by ring, Real.cos_two_pi_sub]
    simpa [abs_sub_comm] using cos72_close.trans (by norm_num [err72Q, trigErrQ])

theorem sinH_close (k : OrbitIndex) :
    |((sinH k : ℚ) : ℝ) - Real.sin (2 * π * (k : ℝ) / 5)| ≤ (trigErrQ : ℝ) := by
  fin_cases k
  · norm_num [sinH, trigErrQ]
  · simpa [sinH, abs_sub_comm] using sin72_close.trans (by norm_num [err72Q, trigErrQ])
  · simpa [sinH, show 2 * π * (2 : ℝ) / 5 = 4 * π / 5 by ring, abs_sub_comm]
      using sin144_close
  · norm_num [sinH]
    rw [show 2 * π * (3 : ℝ) / 5 = 2 * π - 4 * π / 5 by ring, Real.sin_two_pi_sub]
    calc
      _ = |Real.sin (4 * π / 5) - ((sin144H : ℚ) : ℝ)| := by congr 1 <;> ring
      _ ≤ _ := sin144_close
  · norm_num [sinH]
    rw [show 2 * π * (4 : ℝ) / 5 = 2 * π - 2 * π / 5 by ring, Real.sin_two_pi_sub]
    calc
      _ = |Real.sin (2 * π / 5) - ((sin72H : ℚ) : ℝ)| := by congr 1 <;> ring
      _ ≤ _ := sin72_close.trans (by norm_num [err72Q, trigErrQ])

/-! ### The planar height of seed 1 -/

/-- Lean's rational seed coordinates, as reals. -/
noncomputable def sx (j : SeedIndex) (m : Fin 3) : ℝ := (seedVertex j m : ℝ)

/-- `d = R⁻¹ s₂ - s₂` (R the rotation by 72°; no z part) and `e = s₃ - s₂`. -/
noncomputable def dx : ℝ := (Real.cos (2 * π / 5) - 1) * sx 2 0 + Real.sin (2 * π / 5) * sx 2 1
noncomputable def dy : ℝ := -Real.sin (2 * π / 5) * sx 2 0 + (Real.cos (2 * π / 5) - 1) * sx 2 1
noncomputable def ex : ℝ := sx 3 0 - sx 2 0
noncomputable def ey : ℝ := sx 3 1 - sx 2 1
noncomputable def ez : ℝ := sx 3 2 - sx 2 2

/-- The z component of the normal `e × d` of the quad's plane. -/
noncomputable def normalZ : ℝ := ex * dy - ey * dx

/-- `n · (s₁ - s₂)` without its z term, for `n = e × d`. -/
noncomputable def normalXY : ℝ := -ez * dy * (sx 1 0 - sx 2 0) + ez * dx * (sx 1 1 - sx 2 1)

/-- The height that puts seed 1 in the plane through `s₂`, `s₃`, `R⁻¹ s₂`. -/
noncomputable def z1 : ℝ := sx 2 2 - normalXY / normalZ

def z1H : ℚ := 2999124089975388432120944671921453154886 / 10^40

/-- Interval bounds on cos 72° and sin 72°. -/
theorem cs_bounds :
    (cos72H : ℝ) - err72Q ≤ Real.cos (2 * π / 5) ∧ Real.cos (2 * π / 5) ≤ (cos72H : ℝ) + err72Q ∧
      (sin72H : ℝ) - err72Q ≤ Real.sin (2 * π / 5) ∧
        Real.sin (2 * π / 5) ≤ (sin72H : ℝ) + err72Q := by
  have hc := abs_le.mp cos72_close
  have hs := abs_le.mp sin72_close
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem normalZ_pos : 1 / 10 ≤ normalZ := by
  obtain ⟨hcl, hcu, hsl, hsu⟩ := cs_bounds
  norm_num [cos72H, sin72H, err72Q] at hcl hcu hsl hsu
  simp only [normalZ, ex, ey, dx, dy, sx]
  simp [seedVertex]
  norm_num
  nlinarith

theorem z1_close : |z1 - (z1H : ℝ)| ≤ 1 / 10^37 := by
  have hz := normalZ_pos
  have hzpos : 0 < normalZ := by linarith
  have key : z1 - (z1H : ℝ) = ((sx 2 2 - z1H) * normalZ - normalXY) / normalZ := by
    rw [eq_div_iff hzpos.ne']
    simp only [z1]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hzpos, div_le_iff₀ hzpos, abs_le]
  obtain ⟨hcl, hcu, hsl, hsu⟩ := cs_bounds
  norm_num [cos72H, sin72H, err72Q] at hcl hcu hsl hsu
  simp only [normalZ, normalXY, ex, ey, ez, dx, dy, sx]
  simp [seedVertex, z1H]
  norm_num
  constructor <;> nlinarith

/-! ### The idealized model -/

/-- Seeds 0, 2, 3 as in `seedVertex`; seed 1 with height `z1`. -/
noncomputable def seed (j : SeedIndex) : ℝ³ :=
  WithLp.toLp 2 ![sx j 0, sx j 1, if j = 1 then z1 else sx j 2]

/-- The same with `z1H` for `z1`. -/
def seedH (j : SeedIndex) : Fin 3 → ℚ :=
  ![seedVertex j 0, seedVertex j 1, if j = 1 then z1H else seedVertex j 2]

/-- The rational counterpart of the idealized vertex `i`. -/
def vertexH (i : VertexIndex) : Fin 3 → ℚ :=
  let c := cosH (orbitIndex i)
  let s := sinH (orbitIndex i)
  let v := seedH (seedIndex i)
  ![c * v 0 - s * v 1, s * v 0 + c * v 1, v 2]

/-- `vertexH` is within `4.1e-16` of the certified rational vertices. -/
theorem vertexH_sq_close : ∀ i : VertexIndex,
    (rationalVertex i 0 - vertexH i 0) ^ 2 + (rationalVertex i 1 - vertexH i 1) ^ 2 +
      (rationalVertex i 2 - vertexH i 2) ^ 2 ≤ (41 / 10^17 : ℚ) ^ 2 := by
  decide +kernel

theorem vertexH_close (i : VertexIndex) :
    ‖toR3 (rationalVertex i) - toR3 (vertexH i)‖ ≤ 41 / 10^17 := by
  have he : (0 : ℝ) ≤ 41 / 10^17 := by norm_num
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq he]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs, toR3, PiLp.sub_apply]
  have h := vertexH_sq_close i
  have hreal :
      (((rationalVertex i 0 - vertexH i 0) ^ 2 + (rationalVertex i 1 - vertexH i 1) ^ 2 +
        (rationalVertex i 2 - vertexH i 2) ^ 2 : ℚ) : ℝ) ≤ (((41 / 10^17) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at hreal
  norm_num at hreal ⊢
  linarith

private lemma RzL_apply_0' (θ : ℝ) (v : ℝ³) : (RzL θ v) 0 = cos θ * v 0 - sin θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]
  ring

private lemma RzL_apply_1' (θ : ℝ) (v : ℝ³) : (RzL θ v) 1 = sin θ * v 0 + cos θ * v 1 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

private lemma RzL_apply_2' (θ : ℝ) (v : ℝ³) : (RzL θ v) 2 = v 2 := by
  simp [RzL, Rz_mat, Matrix.vecHead, Matrix.vecTail]

private lemma seed_xy_sq_le_one (j : SeedIndex) : sx j 0 ^ 2 + sx j 1 ^ 2 ≤ 1 := by
  fin_cases j <;> norm_num [sx, seedVertex]

/-- The idealized vertex `i`, before packaging as a `C5Model`. -/
noncomputable def vertex (i : VertexIndex) : ℝ³ :=
  RzL (2 * π * (orbitIndex i : ℝ) / 5) (seed (seedIndex i))

theorem vertexH_vertex_close (i : VertexIndex) :
    ‖toR3 (vertexH i) - vertex i‖ ≤ 1 / 10^36 := by
  let k := orbitIndex i
  let j := seedIndex i
  let θ : ℝ := 2 * π * (k : ℝ) / 5
  let ce : ℝ := (cosH k : ℚ) - Real.cos θ
  let se : ℝ := (sinH k : ℚ) - Real.sin θ
  let d := toR3 (vertexH i) - vertex i
  have hce : |ce| ≤ (trigErrQ : ℝ) := cosH_close k
  have hse : |se| ≤ (trigErrQ : ℝ) := sinH_close k
  have hab := seed_xy_sq_le_one j
  have hd0 : d 0 = ce * sx j 0 - se * sx j 1 := by
    simp only [d, vertexH, vertex, seed, seedH, k, j, θ, ce, se, sx, toR3, PiLp.sub_apply,
      Matrix.cons_val_zero, RzL_apply_0']
    simp
    push_cast
    ring
  have hd1 : d 1 = se * sx j 0 + ce * sx j 1 := by
    simp only [d, vertexH, vertex, seed, seedH, k, j, θ, ce, se, sx, toR3, PiLp.sub_apply,
      Matrix.cons_val_one, RzL_apply_1']
    simp
    push_cast
    ring
  have hd2 : |d 2| ≤ 1 / 10^37 := by
    have h2 : d 2 = (if seedIndex i = 1 then ((z1H : ℚ) : ℝ) - z1 else 0) := by
      simp only [d, vertexH, vertex, seed, seedH, toR3, PiLp.sub_apply, RzL_apply_2']
      split_ifs <;> simp_all [sx]
    rw [h2]
    split_ifs
    · rw [abs_sub_comm]
      exact z1_close
    · norm_num
  have hsq : d 0 ^ 2 + d 1 ^ 2 = (ce ^ 2 + se ^ 2) * (sx j 0 ^ 2 + sx j 1 ^ 2) := by
    rw [hd0, hd1]
    ring
  have hce_sq : ce ^ 2 ≤ (trigErrQ : ℝ) ^ 2 := sq_le_sq' (abs_le.mp hce).1 (abs_le.mp hce).2
  have hse_sq : se ^ 2 ≤ (trigErrQ : ℝ) ^ 2 := sq_le_sq' (abs_le.mp hse).1 (abs_le.mp hse).2
  have hd2_sq : d 2 ^ 2 ≤ (1 / 10^37 : ℝ) ^ 2 := sq_le_sq' (abs_le.mp hd2).1 (abs_le.mp hd2).2
  have he : (0 : ℝ) ≤ 1 / 10^36 := by norm_num
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq he]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, norm_eq_abs, sq_abs]
  rw [hsq]
  have hprod : (ce ^ 2 + se ^ 2) * (sx j 0 ^ 2 + sx j 1 ^ 2) ≤ ce ^ 2 + se ^ 2 := by
    nlinarith [add_nonneg (sq_nonneg ce) (sq_nonneg se)]
  have hd2' : ((toR3 (vertexH i)).ofLp 2 - (vertex i).ofLp 2) ^ 2 ≤ (1 / 10^37 : ℝ) ^ 2 := by
    simpa [d] using hd2_sq
  norm_num [trigErrQ] at hce_sq hse_sq hd2' ⊢
  nlinarith

theorem vertex_close (i : VertexIndex) :
    ‖vertex i - toR3 (rationalVertex i)‖ ≤ (modelErrorQ : ℝ) := by
  calc
    ‖vertex i - toR3 (rationalVertex i)‖ =
        ‖(vertex i - toR3 (vertexH i)) + (toR3 (vertexH i) - toR3 (rationalVertex i))‖ := by
      congr 1
      abel
    _ ≤ ‖vertex i - toR3 (vertexH i)‖ + ‖toR3 (vertexH i) - toR3 (rationalVertex i)‖ :=
      norm_add_le _ _
    _ ≤ 1 / 10^36 + 41 / 10^17 := by
      exact add_le_add (by rw [norm_sub_rev]; exact vertexH_vertex_close i)
        (by rw [norm_sub_rev]; exact vertexH_close i)
    _ ≤ (modelErrorQ : ℝ) := by norm_num [modelErrorQ]

/-- Idealized #231 as a `C5Model`: the certificates cover it. -/
noncomputable def model : C5Model where
  seed := seed
  close := vertex_close

/-! ### Exactly planar quads -/

/-- `a · (b × c)`. -/
noncomputable def triple (a b c : ℝ³) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- Quad `k` is `{v(k,1), v(k,2), v(k,3), v(k-1,2)}`; quad 0 is `{v₁, v₂, v₃, v₁₈}`. -/
noncomputable def quadVolume (k : OrbitIndex) : ℝ :=
  let p := model.vertex (vertexIndex k 1)
  triple (model.vertex (vertexIndex k 2) - p) (model.vertex (vertexIndex k 3) - p)
    (model.vertex (vertexIndex ⟨(k.val + 4) % 5, Nat.mod_lt _ (by omega)⟩ 2) - p)

theorem triple_RzL (θ : ℝ) (a b c : ℝ³) :
    triple (RzL θ a) (RzL θ b) (RzL θ c) = triple a b c := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [triple, RzL_apply_0', RzL_apply_1', RzL_apply_2']
  linear_combination (a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) +
    a 2 * (b 0 * c 1 - b 1 * c 0)) * h

private lemma RzL_add (α β : ℝ) (v : ℝ³) : RzL (α + β) v = RzL α (RzL β v) := by
  have h := RzC.map_add_eq_mul α β
  simp only [RzC_coe] at h
  rw [h]
  rfl

private lemma RzL_zero_apply (v : ℝ³) : RzL 0 v = v := by
  ext m
  fin_cases m <;> simp [RzL_apply_0', RzL_apply_1', RzL_apply_2']

private lemma RzL_add_two_pi (θ : ℝ) (v : ℝ³) : RzL (θ + 2 * π) v = RzL θ v := by
  rw [show θ + 2 * π = θ + (1 : ℤ) * (2 * π) by simp]
  simp only [RzL, Rz_mat_add_int_mul_two_pi]

theorem model_vertex (k : OrbitIndex) (j : SeedIndex) :
    model.vertex (vertexIndex k j) = RzL (2 * π * (k : ℝ) / 5) (seed j) := by
  simp [C5Model.vertex, model]

/-- The quad's last vertex, `v(k-1, 2)`, is `R^k` applied to `R⁻¹ s₂ = R⁴ s₂`. -/
theorem model_vertex_prev (k : OrbitIndex) :
    model.vertex (vertexIndex ⟨(k.val + 4) % 5, Nat.mod_lt _ (by omega)⟩ 2) =
      RzL (2 * π * (k : ℝ) / 5) (RzL (2 * π * 4 / 5) (seed 2)) := by
  rw [model_vertex, ← RzL_add]
  fin_cases k
  · norm_num
  all_goals
    simp only [Fin.isValue]
    norm_num
    rw [← RzL_add_two_pi]
    congr 1
    ring

/-- Quad `k` is quad 0 rotated by `2πk/5`. -/
theorem quadVolume_eq (k : OrbitIndex) : quadVolume k = quadVolume 0 := by
  have hrot : ∀ k : OrbitIndex, quadVolume k =
      triple (seed 2 - seed 1) (seed 3 - seed 1) (RzL (2 * π * 4 / 5) (seed 2) - seed 1) := by
    intro k
    simp only [quadVolume]
    rw [model_vertex_prev, model_vertex, model_vertex, model_vertex, ← map_sub, ← map_sub,
      ← map_sub, triple_RzL]
  rw [hrot k, hrot 0]

private lemma cos_eight_pi_fifths : Real.cos (2 * π * 4 / 5) = Real.cos (2 * π / 5) := by
  rw [show 2 * π * 4 / 5 = 2 * π - 2 * π / 5 by ring, Real.cos_two_pi_sub]

private lemma sin_eight_pi_fifths : Real.sin (2 * π * 4 / 5) = -Real.sin (2 * π / 5) := by
  rw [show 2 * π * 4 / 5 = 2 * π - 2 * π / 5 by ring, Real.sin_two_pi_sub]

/-- Quad 0's volume is `-(n · (s₁ - s₂))` for the plane normal `n = e × d`
(`triple` is linear and alternating). -/
theorem quadVolume_zero_eq : quadVolume 0 = -(normalXY + normalZ * (z1 - sx 2 2)) := by
  rw [show quadVolume 0 = triple (seed 2 - seed 1) (seed 3 - seed 1)
      (RzL (2 * π * 4 / 5) (seed 2) - seed 1) by
    simp only [quadVolume]
    rw [model_vertex_prev, model_vertex, model_vertex, model_vertex]
    simp [RzL_zero_apply]]
  simp only [triple, PiLp.sub_apply, RzL_apply_0', RzL_apply_1', RzL_apply_2',
    cos_eight_pi_fifths, sin_eight_pi_fifths, seed]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp only [if_pos (rfl : (1 : SeedIndex) = 1), if_neg (show (2 : SeedIndex) ≠ 1 by decide),
    if_neg (show (3 : SeedIndex) ≠ 1 by decide), ite_true, ↓reduceIte]
  simp only [normalXY, normalZ, dx, dy, ex, ey, ez]
  ring

/-- Quad 0, `{v₁, v₂, v₃, v₁₈}`, is exactly planar: `z1` was chosen for this. -/
theorem quadVolume_zero : quadVolume 0 = 0 := by
  have hz : normalZ ≠ 0 := (lt_of_lt_of_le (by norm_num) normalZ_pos).ne'
  have hz1 : normalZ * (z1 - sx 2 2) = -normalXY := by
    simp only [z1]
    field_simp
    ring
  rw [quadVolume_zero_eq, hz1]
  ring

/-- All five quads of idealized #231 are exactly planar. -/
theorem quad_planar (k : OrbitIndex) : quadVolume k = 0 := by
  rw [quadVolume_eq, quadVolume_zero]

end Noperthedron.Nopert229.Ideal231

end
