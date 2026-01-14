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

mutual

theorem Row.valid_imp_not_rupert_ix
   (tab : Solution.Table) (i : ℕ) (tab_valid : tab.Valid)
   (row : Solution.Row) (row_valid : row.ValidIx tab i) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull :=
  let ⟨rv1, rv2⟩ := row_valid
  match rv2 with
  | .asSplit y => valid_split_imp_no_rupert tab row tab_valid y
  | .asGlobal y => valid_global_imp_no_rupert tab row y
  | .asLocal y=> valid_local_imp_no_rupert tab row y
termination_by (tab.size - i, 3)
decreasing_by rw [rv1]; grind

theorem valid_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.Valid)
    (hr : row.ValidSplit tab) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  obtain ⟨_, hr⟩ := hr
  rcases hr with hr' | ⟨_, _, hr'⟩
  · exact valid_binary_split_imp_no_rupert tab row htab hr'
  · exact valid_full_split_imp_no_rupert tab row htab hr'
termination_by (tab.size - row.ID, 2)

theorem valid_binary_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.Valid)
    (hr : Row.ValidBinarySplit tab row) : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  obtain ⟨_, hr⟩ := hr
  rcases hr with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;>
  · exact valid_param_split_imp_no_rupert tab row htab _ h
termination_by (tab.size - row.ID, 1)

theorem valid_full_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.Valid)
    (hr' : tab.HasIntervals row.IDfirstChild
      (cubeFold [Interval.lower_half, Interval.upper_half]
       row.interval [Param.θ₁, Param.φ₁, Param.θ₂, Param.φ₂, Param.α])) :
    ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  sorry
termination_by (tab.size - row.ID, 1)

theorem valid_param_split_imp_no_rupert (tab : Table) (row : Row) (htab : tab.Valid)
    (p : Param) (h : Row.ValidSplitParam tab row p) :
    ¬∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull := by
  obtain ⟨_, h0, h1, h2, iv1, iv2⟩ := h
  let r1 := tab[row.IDfirstChild]
  let r2 := tab[row.IDfirstChild + 1]
  have m1 := r1.valid_imp_not_rupert_ix tab (row.IDfirstChild) htab (htab.valid_at h1)
  have m2 := r2.valid_imp_not_rupert_ix tab (row.IDfirstChild+1) htab (htab.valid_at h2)
  rintro ⟨q, hq1, hq2⟩
  change q ∈ row.interval.toPoseInterval at hq1
  replace hq1 := mem_interval_imp_mem_union_halves q row.interval p hq1
  rcases hq1 with h | h
  · refine m1 ⟨q, ?_, hq2⟩
    change q ∈ tab[row.IDfirstChild].interval.toPoseInterval; rw [iv1]; exact h
  · refine m2 ⟨q, ?_, hq2⟩
    change q ∈ tab[row.IDfirstChild+1].interval.toPoseInterval; rw [iv2]; exact h

termination_by (tab.size - row.ID, 0)
decreasing_by all_goals grind

end

theorem Row.valid_imp_not_rupert
   (tab : Solution.Table) (tab_valid : tab.Valid)
   (hz : 0 < tab.size) :
    ¬ ∃ q ∈ tab[0].toPoseInterval, RupertPose q nopert.hull :=
  Row.valid_imp_not_rupert_ix tab 0 tab_valid tab[0] (tab_valid.valid_at hz)
