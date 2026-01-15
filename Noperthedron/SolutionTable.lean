import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Local
import Noperthedron.SolutionTable.Global
import Noperthedron.Nopert

namespace Solution

lemma mem_pose_interval_iff (q : Pose) (iv : Interval) :
    q ∈ iv.toPoseInterval ↔
      q.θ₁ ∈ Set.Icc (iv.min .θ₁ / DENOM) (iv.max .θ₁ / DENOM) ∧
      q.φ₁ ∈ Set.Icc (iv.min .φ₁ / DENOM) (iv.max .φ₁ / DENOM) ∧
      q.θ₂ ∈ Set.Icc (iv.min .θ₂ / DENOM) (iv.max .θ₂ / DENOM) ∧
      q.φ₂ ∈ Set.Icc (iv.min .φ₂ / DENOM) (iv.max .φ₂ / DENOM) ∧
      q.α ∈ Set.Icc (iv.min .α / DENOM) (iv.max .α / DENOM)
      := by
  constructor <;>
  · simp_all [Interval.toPoseInterval, Membership.mem, PoseInterval.contains]

lemma mem_lower_half (q : Pose) (iv : Interval) (p : Param)
    (hq : q ∈ iv.toPoseInterval)
    (lower : q.getParam p ≤ ((iv.min p + iv.max p) / 2 : ℕ) / DENOM) :
    q ∈ (iv.lower_half p).toPoseInterval := by
  rw [mem_pose_interval_iff] at hq ⊢
  have ⟨_, _, _, _, _⟩ := hq
  fin_cases p <;>
  · simp_all [Interval.lower_half]; exact lower

lemma mem_upper_half (q : Pose) (iv : Interval) (p : Param)
    (hq : q ∈ iv.toPoseInterval)
    (upper : ((iv.min p + iv.max p) / 2 : ℕ) / DENOM ≤ q.getParam p ) :
    q ∈ (iv.upper_half p).toPoseInterval := by
  rw [mem_pose_interval_iff] at hq ⊢
  have ⟨_, _, _, _, _⟩ := hq
  fin_cases p <;>
  · simp_all [Interval.upper_half]; exact upper

lemma mem_interval_imp_mem_union_halves (q : Pose) (iv : Interval) (p : Param)
     (hq : q ∈ iv.toPoseInterval) :
     q ∈ (iv.lower_half p).toPoseInterval ∨ q ∈ (iv.upper_half p).toPoseInterval := by
  let midn : ℕ := (iv.min p + iv.max p) / 2
  let midr : ℝ := midn / DENOM
  if h : q.getParam p ≤ midr then
    left; exact mem_lower_half q iv p hq h
  else
    right; exact mem_upper_half q iv p hq (Std.le_of_not_ge h)

lemma interval_sub_union_halves (iv : Interval) (p : Param) :
    (iv : Set Pose) ⊆ (iv.lower_half p : Set Pose) ∪ iv.upper_half p := by
  intro q
  simp only [Set.mem_setOf_eq, Set.mem_union]
  exact mem_interval_imp_mem_union_halves q iv p

lemma non_rupert_halves_imp_non_rupert {p : Param} {iv : Interval}
    (q1 : ¬∃ q ∈ (Interval.lower_half p iv).toPoseInterval, RupertPose q nopert.hull)
    (q2 : ¬∃ q ∈ (Interval.upper_half p iv).toPoseInterval, RupertPose q nopert.hull) :
    ¬∃ q ∈ iv.toPoseInterval, RupertPose q nopert.hull := by
  rintro ⟨q, hq1, hq2⟩
  replace hq1 := mem_interval_imp_mem_union_halves q iv p hq1
  rcases hq1 with h | h
  · exact q1 ⟨q, h, hq2⟩
  · exact q2 ⟨q, h, hq2⟩

/-
This is a decently big mutual induction over several predicates establishing the validity of our interval checking.
-/
mutual

theorem has_intervals_imp_no_rupert (tab : Table) (htab : tab.Valid) (n : ℕ)
    (interval : Interval) (params : List Param)
    (hi : tab.HasIntervals n
      (cubeFold [Interval.lower_half, Interval.upper_half] interval params)) :
    ¬ ∃ q ∈ interval.toPoseInterval, RupertPose q nopert.hull := by
  match params with
  | [] =>
    simp only [cubeFold, Table.HasIntervals] at hi
    specialize hi ⟨0, by simp⟩
    simp only [add_zero, List.length_cons, List.length_nil, Nat.reduceAdd, Fin.zero_eta,
      Fin.isValue, Fin.getElem_fin, Fin.val_eq_zero, List.getElem_cons_zero] at hi
    obtain ⟨hn, he⟩ := hi
    change ¬∃ q ∈ interval.toPoseInterval, RupertPose q nopert.hull
    rw [← he]
    exact tab[n].valid_imp_not_rupert_ix tab n htab (Table.Valid.valid_at htab hn)
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
   (tab : Solution.Table) (i : ℕ) (tab_valid : tab.Valid)
   (row : Solution.Row) (row_valid : row.ValidIx tab i) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull :=
  let ⟨_rv1, rv2, rv3⟩ := row_valid
  match rv2 with
  | .asSplit y => valid_split_imp_no_rupert tab row tab_valid y rv3
  | .asGlobal y => valid_global_imp_no_rupert tab row y
  | .asLocal y=> valid_local_imp_no_rupert tab row y
termination_by (tab.size - i, 3, 0)
decreasing_by rw [_rv1]; grind

theorem valid_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.Valid)
    (hr : row.ValidSplit tab) (hlt : row.ID < tab.size) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  obtain ⟨_, hr⟩ := hr
  rcases hr with hr' | ⟨_, _, hgt, hr'⟩
  · exact valid_binary_split_imp_no_rupert tab row htab hr'
  · exact valid_full_split_imp_no_rupert tab row htab hgt hlt hr'
termination_by (tab.size - row.ID, 2, 0)

theorem valid_binary_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.Valid)
    (hr : Row.ValidBinarySplit tab row) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  obtain ⟨_, hr⟩ := hr
  rcases hr with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
  · exact valid_param_split_imp_no_rupert tab row htab _ h
termination_by (tab.size - row.ID, 1, 0)

theorem valid_full_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.Valid)
    (_hgt : row.ID < row.IDfirstChild)
    (_hlt : row.ID < tab.size)
    (hi : tab.HasIntervals row.IDfirstChild
      (cubeFold [Interval.lower_half, Interval.upper_half]
       row.interval [Param.θ₁, Param.φ₁, Param.θ₂, Param.φ₂, Param.α])) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  exact has_intervals_imp_no_rupert tab htab row.IDfirstChild row.interval _ hi
termination_by (tab.size - row.ID, 1, 0)
decreasing_by left; exact Nat.sub_lt_sub_left _hlt _hgt

theorem valid_param_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.Valid)
    (p : Param) (h : Row.ValidSplitParam tab row p) :
    ¬∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  obtain ⟨_, h0, h1, h2, iv1, iv2⟩ := h
  let r1 := tab[row.IDfirstChild]
  let r2 := tab[row.IDfirstChild + 1]
  have m1 := r1.valid_imp_not_rupert_ix tab (row.IDfirstChild) htab (htab.valid_at h1)
  have m2 := r2.valid_imp_not_rupert_ix tab (row.IDfirstChild+1) htab (htab.valid_at h2)
  unfold r1 at m1
  unfold r2 at m2
  change  ¬∃ q ∈ tab[row.IDfirstChild].interval.toPoseInterval, RupertPose q nopert.hull at m1
  change  ¬∃ q ∈ tab[row.IDfirstChild + 1].interval.toPoseInterval, RupertPose q nopert.hull at m2
  rw [iv1] at m1
  rw [iv2] at m2
  exact non_rupert_halves_imp_non_rupert m1 m2

termination_by (tab.size - row.ID, 0, 0)
decreasing_by all_goals grind

end

theorem Row.valid_imp_not_rupert
   (tab : Solution.Table) (tab_valid : tab.Valid)
   (hz : 0 < tab.size) :
    ¬ ∃ q ∈ tab[0].toPoseInterval, RupertPose q nopert.hull :=
  Row.valid_imp_not_rupert_ix tab 0 tab_valid tab[0] (tab_valid.valid_at hz)
