import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Local
import Noperthedron.SolutionTable.Global
import Noperthedron.Vertices.Exact

namespace Noperthedron.Solution

lemma mem_pose_interval_iff (q : Pose ℝ) (iv : Interval) :
    q ∈ iv.toReal ↔
      q.θ₁ ∈ Set.Icc (iv.min.θ₁ : ℝ) (iv.max.θ₁ : ℝ) ∧
      q.φ₁ ∈ Set.Icc (iv.min.φ₁ : ℝ) (iv.max.φ₁ : ℝ) ∧
      q.θ₂ ∈ Set.Icc (iv.min.θ₂ : ℝ) (iv.max.θ₂ : ℝ) ∧
      q.φ₂ ∈ Set.Icc (iv.min.φ₂ : ℝ) (iv.max.φ₂ : ℝ) ∧
      q.α ∈ Set.Icc (iv.min.α : ℝ) (iv.max.α : ℝ)
      := by
  show q ∈ Set.Icc iv.minPose iv.maxPose ↔ _
  simp only [Set.mem_Icc, Pose.le_iff, Interval.minPose, Interval.maxPose, Set.mem_Icc]
  tauto

lemma mem_nth_part (q : Pose ℝ) (iv : Interval) (p : Param) (N : ℕ) [hN : NeZero N] (n : Fin N)
    (hq : q ∈ iv.toReal)
    (bound : q.getParam p ∈ Set.Icc (iv.interpolate p N n : ℝ) (iv.interpolate p N (n + 1) : ℝ)) :
    q ∈ (iv.nth_part p N n).toReal := by
  rw [mem_pose_interval_iff] at hq ⊢
  have ⟨_, _, _, _, _⟩ := hq
  fin_cases p <;> simp_all [Interval.nth_part, Pose.getParam, Pose.setParam]

@[push_cast]
lemma iv_max_push_cast (iv : Interval) (p : Param) :
    ((PoseInterval.max iv).getParam p : ℝ) = iv.toReal.max.getParam p := by
  cases p <;>
    simp [Interval.toReal, Interval.minPose, Interval.maxPose, Pose.getParam, Pose.toReal]

@[push_cast]
lemma iv_min_push_cast (iv : Interval) (p : Param) :
    ((PoseInterval.min iv).getParam p : ℝ) = iv.toReal.min.getParam p := by
  cases p <;>
    simp [Interval.toReal, Interval.minPose, Interval.minPose, Pose.getParam, Pose.toReal]

lemma mem_iv_imp_ge_min (iv : Interval) {q : Pose ℝ} (hq : q ∈ iv.toReal) (p : Param) :
    iv.min.getParam p ≤ q.getParam p := by
  simp [Interval.toReal] at hq
  obtain ⟨hq, _⟩ := hq
  push_cast
  exact Pose.le_iff_forall_getParam iv.toReal.min q |>.mp hq p

lemma mem_iv_imp_le_max (iv : Interval) {q : Pose ℝ} (hq : q ∈ iv.toReal) (p : Param) :
    q.getParam p ≤ iv.max.getParam p := by
  simp [Interval.toReal] at hq
  obtain ⟨_, hq⟩ := hq
  push_cast
  exact Pose.le_iff_forall_getParam q iv.toReal.max |>.mp hq p

lemma mem_lower_half (q : Pose ℝ) (iv : Interval) (p : Param)
    (hq : q ∈ iv.toReal)
    (lower : q.getParam p ≤ (((iv.min.getParam p + iv.max.getParam p) / 2 : ℚ) : ℝ)) :
    q ∈ (iv.lower_half p).toReal := by
  apply mem_nth_part q iv p 2 0 hq
  constructor
  · simp [Interval.interpolate, AffineMap.lineMap]
    exact mem_iv_imp_ge_min iv hq p
  · simp [Interval.interpolate, AffineMap.lineMap]
    grw [lower]
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    ring_nf
    rfl

lemma mem_upper_half (q : Pose ℝ) (iv : Interval) (p : Param)
    (hq : q ∈ iv.toReal)
    (upper : (((iv.min.getParam p + iv.max.getParam p) / 2 : ℚ) : ℝ) ≤ q.getParam p) :
    q ∈ (iv.upper_half p).toReal := by
  apply mem_nth_part q iv p 2 1 hq
  constructor
  · simp [Interval.interpolate, AffineMap.lineMap]
    grw [← upper]
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
    ring_nf
    rfl
  · simp [Interval.interpolate, AffineMap.lineMap]
    exact mem_iv_imp_le_max iv hq p

lemma mem_icc_mem_some_part (x : ℝ) (N : ℕ) [NeZero N] (hx : x ∈ Set.Icc 0 (N : ℝ)) :
    ∃ n : Fin N, x ∈ Set.Icc (n : ℝ) (n + 1) := by
  have hz : N ≠ 0 := Ne.symm (NeZero.ne' N)
  if h : x = N then
    use ⟨N - 1, Nat.sub_one_lt (Ne.symm (NeZero.ne' N))⟩
    constructor
    · simp [h]
    · simp only [h]; rw [Nat.cast_sub (show 1 ≤ N by grind)]; simp
  else
    have hN : x < N := Std.lt_of_le_of_ne hx.2 h
    have : ⌊x⌋.toNat < N :=
      (Int.toNat_lt (Int.floor_nonneg.mpr hx.1)).mpr (Int.floor_lt.mpr hN)
    use ⟨⌊x⌋.toNat, this⟩
    constructor
    · change (↑⌊x⌋.toNat : ℤ) ≤ x
      rw [Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx.1)]
      exact Int.floor_le x
    · change x ≤ (⌊x⌋.toNat : ℤ) + 1
      rw [Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx.1)]
      exact_mod_cast le_of_lt (Int.lt_floor_add_one x)

lemma mem_icc_mem_some_part_ab (x : ℝ) (a b : ℚ) (hab : a < b) (N : ℕ)
    [NeZero N] (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    ∃ n : Fin N, x ∈ Set.Icc (interpolate a b N n) (interpolate a b N (n + 1)) := by
    let xx := N * (x - a) / (b - a)
    have h : 0 < (↑b : ℝ) - (↑a : ℝ) := by
      exact_mod_cast (Rat.lt_iff_sub_pos a b).mp hab
    obtain ⟨hx1, hx2⟩ := hx
    have hxx : xx ∈ Set.Icc 0 (N : ℝ) := by
      simp [xx]
      constructor
      · field_simp; simp only [zero_mul];
        exact mul_nonneg (Nat.cast_nonneg N) (by linarith)
      · field_simp;
        have q : 0 < N := Nat.pos_of_ne_zero (Ne.symm (NeZero.ne' N))
        exact mul_le_mul_of_nonneg_left (by grind) (Nat.cast_nonneg' N)
    have q : 0 < N := Nat.pos_of_ne_zero (Ne.symm (NeZero.ne' N))
    obtain ⟨n, h3⟩ := mem_icc_mem_some_part xx N hxx
    simp [xx] at h3
    field_simp at h3
    ring_nf at h3
    use n
    constructor <;>
    · simp [interpolate, AffineMap.lineMap]
      field_simp
      grind

lemma mem_interval_imp_mem_some_part (q : Pose ℝ) (iv : Interval) (p : Param)
     (N : ℕ) [NeZero N] (hq : q ∈ iv.toReal) :
     ∃ n : Fin N, q ∈ (iv.nth_part p N n).toReal := by
  let ivpMin := iv.toReal.min.getParam p
  let ivpMax := iv.toReal.max.getParam p
  have : q.getParam p ∈ Set.Icc ivpMin ivpMax :=
    ⟨(Pose.le_iff_forall_getParam _ _).mp hq.1 p,
     (Pose.le_iff_forall_getParam _ _).mp hq.2 p⟩
  by_cases H : iv.min.getParam p = iv.max.getParam p
  · use 0
    refine mem_nth_part _ _ _ _ _ hq ?_
    sorry
  have h₁ : iv.min.getParam p < iv.max.getParam p := by
    by_contra! H₁
    have h₃ := iv.min_le_max
    rw [Pose.le_iff_forall_getParam] at h₃
    specialize h₃ p
    order
  have h₂ : q.getParam p ∈
             Set.Icc ↑((PoseInterval.min iv).getParam p)
                     ↑((PoseInterval.max iv).getParam p) := by
    simp only [Set.mem_Icc]
    simp only [Interval.toReal, NonemptyInterval.mem_mk, Interval.maxPose, Interval.minPose] at hq
    simp only [Pose.le_iff_forall_getParam] at hq
    obtain ⟨hq₁, hq₂⟩ := hq
    push_cast
    constructor
    · change (PoseInterval.min iv).toReal.getParam p ≤ q.getParam p
      specialize hq₁ p
      exact hq₁
    · change q.getParam p ≤ (PoseInterval.max iv).toReal.getParam p
      specialize hq₂ p
      exact hq₂
  obtain ⟨n, hx⟩ :=
    mem_icc_mem_some_part_ab (q.getParam p) (iv.min.getParam p) (iv.max.getParam p) h₁ N h₂
  use n
  exact mem_nth_part _ _ _ _ _ hq hx

lemma non_rupert_parts_imp_non_rupert (p : Param) {iv : Interval} (N : ℕ) [hN : NeZero N]
    (qq : ∀ n : Fin N, ¬∃ q ∈ (Interval.nth_part p iv N n).toReal, RupertPose q exactPolyhedron.hull) :
    ¬∃ q ∈ iv.toReal, RupertPose q exactPolyhedron.hull := by
  rintro ⟨q, hq1, hq2⟩
  obtain ⟨n, hq1⟩ := mem_interval_imp_mem_some_part q iv p N hq1
  exact qq n ⟨q, hq1, hq2⟩

-- these two are used in the cube-fold part of the proof below
lemma mem_interval_imp_mem_union_halves (q : Pose ℝ) (iv : Interval) (p : Param)
     (hq : q ∈ iv.toReal) :
     q ∈ (iv.lower_half p).toReal ∨ q ∈ (iv.upper_half p).toReal := by
  let midr : ℝ := (((iv.min.getParam p + iv.max.getParam p) / 2 : ℚ) : ℝ)
  if h : q.getParam p ≤ midr then
    left; exact mem_lower_half q iv p hq h
  else
    right; exact mem_upper_half q iv p hq (Std.le_of_not_ge h)

lemma non_rupert_halves_imp_non_rupert {p : Param} {iv : Interval}
    (q1 : ¬∃ q ∈ (Interval.lower_half p iv).toReal, RupertPose q exactPolyhedron.hull)
    (q2 : ¬∃ q ∈ (Interval.upper_half p iv).toReal, RupertPose q exactPolyhedron.hull) :
    ¬∃ q ∈ iv.toReal, RupertPose q exactPolyhedron.hull := by
  rintro ⟨q, hq1, hq2⟩
  replace hq1 := mem_interval_imp_mem_union_halves q iv p hq1
  rcases hq1 with h | h
  · exact q1 ⟨q, h, hq2⟩
  · exact q2 ⟨q, h, hq2⟩

/-
This is a decently big mutual induction over several predicates establishing the validity of our interval checking.
-/
mutual

theorem has_intervals_imp_no_rupert (tab : Table) (htab : tab.RowsValid) (n : ℕ)
    (interval : Interval) (params : List Param)
    (hi : tab.HasIntervals n
      (cubeFold [Interval.lower_half, Interval.upper_half] interval params)) :
    ¬ ∃ q ∈ interval.toReal, RupertPose q exactPolyhedron.hull := by
  match params with
  | [] =>
    simp only [cubeFold, Table.HasIntervals] at hi
    specialize hi ⟨0, by simp⟩
    simp only [add_zero, List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta,
      Fin.isValue, Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero] at hi
    obtain ⟨hn, he⟩ := hi
    change ¬∃ q ∈ interval.toReal, RupertPose q exactPolyhedron.hull
    rw [← he]
    exact tab[n].valid_imp_not_rupert_ix tab n htab (htab.valid_at hn)
  | h::tl =>
    rw [cube_fold_halves, has_intervals_concat] at hi
    obtain ⟨h1, h2⟩ := hi
    obtain q1 := has_intervals_imp_no_rupert tab htab _ _ tl h1
    obtain q2 := has_intervals_imp_no_rupert tab htab _ _ tl h2
    exact non_rupert_halves_imp_non_rupert q1 q2
termination_by (tab.size - n, 4, params.length)
decreasing_by
  · right; left; norm_num
  · right; right; simp only [List.length_cons, lt_add_iff_pos_right, zero_lt_one]
  · left;
    gcongr;
    · refine has_intervals_start_in_table tab n _ ?_ h1
      apply cube_fold_nonempty (hfs := by simp)
    · grw [← cube_fold_nonempty (hfs := by simp)];
      exact lt_add_one n

theorem Row.valid_imp_not_rupert_ix
   (tab : Solution.Table) (i : ℕ) (tab_valid : tab.RowsValid)
   (row : Solution.Row) (row_valid : row.ValidIx tab i) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull :=
  let ⟨_rv1, rv2, rv3⟩ := row_valid
  match rv2 with
  | .asSplit y => valid_split_imp_no_rupert tab row tab_valid y rv3
  | .asGlobal y => valid_global_imp_no_rupert tab row y
  | .asLocal y => valid_local_imp_no_rupert tab row y
termination_by (tab.size - i, 3, 0)
decreasing_by rw [_rv1]; grind

theorem valid_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.RowsValid)
    (hr : row.ValidSplit tab) (hlt : row.ID < tab.size) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨_, hr⟩ := hr
  rcases hr with hr' | ⟨_, _, hgt, hr'⟩
  · exact valid_single_param_split_imp_no_rupert tab row htab hr'
  · exact valid_full_split_imp_no_rupert tab row htab hgt hlt hr'
termination_by (tab.size - row.ID, 2, 0)

theorem valid_single_param_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.RowsValid)
    (hr : Row.ValidSingleParamSplit tab row) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  rcases hr with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
  · exact valid_param_split_imp_no_rupert tab row htab _ h
termination_by (tab.size - row.ID, 1, 0)

theorem valid_full_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.RowsValid)
    (_hgt : row.ID < row.IDfirstChild)
    (_hlt : row.ID < tab.size)
    (hi : tab.HasIntervals row.IDfirstChild
      (cubeFold [Interval.lower_half, Interval.upper_half]
       row.interval [Param.θ₁, Param.φ₁, Param.θ₂, Param.φ₂, Param.α])) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  exact has_intervals_imp_no_rupert tab htab row.IDfirstChild row.interval _ hi
termination_by (tab.size - row.ID, 1, 0)
decreasing_by left; exact Nat.sub_lt_sub_left _hlt _hgt

theorem valid_param_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.RowsValid)
    (p : Param) (h : Row.ValidSplitParam tab row p) :
    ¬∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨hid, hkids, hnzk, hkiv⟩ := h
  refine non_rupert_parts_imp_non_rupert p row.nrChildren (hN := ⟨hnzk⟩) ?_
  intro n
  rw [← hkiv n]
  clear hkiv hnzk
  refine tab[row.IDfirstChild + n].valid_imp_not_rupert_ix tab (row.IDfirstChild+n) htab (htab.valid_at ?_)
  grind

termination_by (tab.size - row.ID, 0, 0)
decreasing_by all_goals grind

end

theorem Row.valid_imp_not_rupert
   (tab : Solution.Table) (tab_valid : tab.RowsValid)
   (hz : 0 < tab.size) :
    ¬ ∃ q ∈ tab[0].interval.toReal, RupertPose q exactPolyhedron.hull :=
  Row.valid_imp_not_rupert_ix tab 0 tab_valid tab[0] (tab_valid.valid_at hz)
