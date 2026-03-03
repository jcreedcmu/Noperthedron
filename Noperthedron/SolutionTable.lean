import Noperthedron.SolutionTable.Basic
import Noperthedron.SolutionTable.Local
import Noperthedron.SolutionTable.Global
import Noperthedron.SolutionTable.RationalLocalCheck
import Noperthedron.Nopert

namespace Solution

lemma mem_lower_half (q : Pose) (iv : Interval) (p : Param)
    (hq : q ∈ iv.toPoseInterval)
    (lower : q.getParam p ≤ (↑((iv.min p + iv.max p) / 2) : ℝ) / DENOM) :
    q ∈ (iv.lower_half p).toPoseInterval := by
  rw [mem_pose_interval_iff] at hq ⊢
  have ⟨_, _, _, _, _⟩ := hq
  fin_cases p <;>
  · simp_all [Interval.lower_half]; exact lower

lemma mem_upper_half (q : Pose) (iv : Interval) (p : Param)
    (hq : q ∈ iv.toPoseInterval)
    (upper : (↑((iv.min p + iv.max p) / 2) : ℝ) / DENOM ≤ q.getParam p ) :
    q ∈ (iv.upper_half p).toPoseInterval := by
  rw [mem_pose_interval_iff] at hq ⊢
  have ⟨_, _, _, _, _⟩ := hq
  fin_cases p <;>
  · simp_all [Interval.upper_half]; exact upper

lemma mem_interval_imp_mem_union_halves (q : Pose) (iv : Interval) (p : Param)
     (hq : q ∈ iv.toPoseInterval) :
     q ∈ (iv.lower_half p).toPoseInterval ∨ q ∈ (iv.upper_half p).toPoseInterval := by
  let midn : ℤ := (iv.min p + iv.max p) / 2
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

lemma mem_Icc_imp_mem_splitParts (x : ℝ) (lo step : ℤ) :
    ∀ parts : ℕ,
      0 < parts →
      x ∈ Set.Icc (lo / DENOM) ((lo + (parts : ℤ) * step) / DENOM) →
      ∃ i : Fin parts,
        x ∈ Set.Icc ((lo + (i.1 : ℤ) * step) / DENOM)
          ((lo + ((i.1 + 1 : ℕ) : ℤ) * step) / DENOM)
  | 0, hparts, _ => (Nat.lt_asymm hparts hparts).elim
  | 1, _hparts, hx =>
      by
        refine ⟨⟨0, by simp⟩, ?_⟩
        simpa using hx
  | Nat.succ (Nat.succ n), _hparts, hx =>
      by
        let boundary : ℝ := ((lo + step : ℤ) : ℝ) / DENOM
        by_cases h : x ≤ boundary
        · refine ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
          refine And.intro ?_ ?_
          · simpa using hx.1
          · simpa [boundary] using h
        · have hge : boundary ≤ x := Std.le_of_not_ge h
          have hx2 : x ∈ Set.Icc boundary ((lo + (Nat.succ (Nat.succ n) : ℤ) * step) / DENOM) :=
            And.intro hge hx.2
          have hx3 :
              x ∈ Set.Icc ((lo + step) / DENOM)
                ((lo + step + (Nat.succ n : ℤ) * step) / DENOM) := by
            refine And.intro (by simpa [boundary] using hge) ?_
            -- Rewrite the RHS into the same normal form as the goal.
            have hx2r_norm : x ≤ (↑lo + (↑n + 1 + 1) * ↑step) / DENOM := by
              simpa using hx2.2
            have hEq :
                (↑lo + (↑n + 1 + 1) * ↑step) / DENOM =
                  (↑lo + ↑step + (↑n + 1) * ↑step) / DENOM := by
              ring
            have hx2r_norm2 : x ≤ (↑lo + ↑step + (↑n + 1) * ↑step) / DENOM := by
              simpa [hEq] using hx2r_norm
            simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm, add_mul] using hx2r_norm2
          have hx3' :
              x ∈ Set.Icc (↑(lo + step) / DENOM)
                ((↑(lo + step) + ↑↑(Nat.succ n) * ↑step) / DENOM) := by
            simpa [Int.cast_add] using hx3
          obtain ⟨i, hi⟩ :=
            mem_Icc_imp_mem_splitParts x (lo + step) step (Nat.succ n) (Nat.succ_pos _) hx3'
          refine ⟨i.succ, ?_⟩
          -- `simp` produces a slightly different normal form for the upper bound; fix it with `ring`.
          refine And.intro (by
            simpa [Fin.succ, boundary, add_assoc, add_left_comm, add_comm, add_mul, Nat.cast_add,
              Nat.succ_eq_add_one, mul_add] using hi.1) ?_
          have hEq :
              (↑lo + (↑step + (↑step + ↑↑i * ↑step))) / DENOM =
                (↑lo + (↑↑i + 1 + 1) * ↑step) / DENOM := by
            ring
          have hi2 :
              x ≤ (↑lo + (↑step + (↑step + ↑↑i * ↑step))) / DENOM := by
            simpa [Fin.succ, boundary, add_assoc, add_left_comm, add_comm, add_mul, Nat.cast_add,
              Nat.succ_eq_add_one, mul_add] using hi.2
          simpa [hEq] using hi2

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
  rcases hr with hθ₁ | hr
  · rcases hθ₁ with ⟨_, h⟩
    exact valid_param_split_imp_no_rupert tab row htab .θ₁ h
  rcases hr with hφ₁ | hr
  · rcases hφ₁ with ⟨_, h⟩
    exact valid_param_split_imp_no_rupert tab row htab .φ₁ h
  rcases hr with hθ₂ | hr
  · rcases hθ₂ with ⟨_, h⟩
    exact valid_param_split_imp_no_rupert tab row htab .θ₂ h
  rcases hr with hφ₂ | hα
  · rcases hφ₂ with ⟨_, h⟩
    exact valid_param_split_imp_no_rupert tab row htab .φ₂ h
  · rcases hα with ⟨_, h⟩
    exact valid_param_split_imp_no_rupert tab row htab .α h
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
  classical
  let parts : ℕ := Row.partsForSplitCode row.split
  let intervals : List Interval := row.interval.splitIntoParts p parts
  have hlen : intervals.length = parts := by
    simp [intervals, Interval.splitIntoParts]

  have child_no_rupert : ∀ i : Fin parts,
      ¬ ∃ q ∈ (intervals[i]).toPoseInterval, RupertPose q nopert.hull := by
    intro i
    have intervals_good := h.intervals_good
    unfold Table.HasIntervals at intervals_good
    obtain ⟨hbound, heq⟩ := intervals_good (Fin.cast hlen.symm i)
    have hbound' : row.IDfirstChild + i.1 < tab.size := by
      simpa using hbound
    have m :=
      (tab[row.IDfirstChild + i.1]).valid_imp_not_rupert_ix tab (row.IDfirstChild + i.1) htab
        (htab.valid_at hbound')
    change ¬ ∃ q ∈ tab[row.IDfirstChild + i.1].interval.toPoseInterval, RupertPose q nopert.hull at m
    have heq' : tab[row.IDfirstChild + i.1].interval = intervals[i] := by
      simpa using heq
    simpa [heq'] using m

  rintro ⟨q, hq, hrupert⟩
  have hq' := (mem_pose_interval_iff q row.interval).1 hq

  have q_in_some_part :
      ∃ i : Fin parts, q ∈ (intervals[i]).toPoseInterval := by
    -- Extract the 1D constraint for the split parameter and choose a part.
    rcases hq' with ⟨hθ₁, hφ₁, hθ₂, hφ₂, hα⟩
    have xp : q.getParam p ∈ Set.Icc (row.interval.min p / DENOM) (row.interval.max p / DENOM) := by
      cases p <;> simpa [Pose.getParam] using
        (by
          first
          | exact hθ₁
          | exact hφ₁
          | exact hθ₂
          | exact hφ₂
          | exact hα)
    -- Rewrite the upper bound using `step_ok`.
    have xp' : q.getParam p ∈
        Set.Icc (row.interval.min p / DENOM)
          ((row.interval.min p + (parts : ℤ) * row.interval.splitStep p parts) / DENOM) := by
      refine And.intro xp.1 ?_
      have hxMax : q.getParam p ≤ (row.interval.max p / DENOM) := xp.2
      have hstep : row.interval.min p + (parts : ℤ) * row.interval.splitStep p parts = row.interval.max p := by
        simpa [parts] using h.step_ok
      -- Rewrite the upper endpoint using the `step_ok` equality (in the same cast-normal form as the goal).
      have hxMaxR : q.getParam p ≤ (↑(row.interval.max p) : ℝ) / DENOM := by
        simpa using hxMax
      have hCast : (↑(row.interval.min p + (parts : ℤ) * row.interval.splitStep p parts) : ℝ) =
          (↑(row.interval.max p) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) hstep
      have hCast' :
          (↑(row.interval.max p) : ℝ) =
            (↑(row.interval.min p) : ℝ) +
              (parts : ℝ) * (↑(row.interval.splitStep p parts) : ℝ) := by
        -- Normalize casts: `↑(min + parts*step)` becomes `↑min + ↑parts * ↑step`.
        simpa [Int.cast_add, Int.cast_mul, Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using hCast.symm
      have hEq :
          (↑(row.interval.max p) : ℝ) / DENOM =
            ((↑(row.interval.min p) : ℝ) +
                (parts : ℝ) * (↑(row.interval.splitStep p parts) : ℝ)) / DENOM := by
        simp [hCast']
      -- Apply the rewrite.
      have hxMaxR' : q.getParam p ≤
          ((↑(row.interval.min p) : ℝ) +
              (parts : ℝ) * (↑(row.interval.splitStep p parts) : ℝ)) / DENOM := by
        simpa [hEq] using hxMaxR
      simpa using hxMaxR'
    have parts_pos : 0 < parts := by
      fin_cases p <;> simp [parts, h.split, Row.splitCodeForParam, Row.partsForSplitCode]
    obtain ⟨i, hi⟩ :=
      mem_Icc_imp_mem_splitParts (q.getParam p) (row.interval.min p)
        (row.interval.splitStep p parts) parts parts_pos xp'
    refine ⟨i, ?_⟩
    -- show `q` lies in the corresponding child interval
    -- unfold the chosen interval and prove bounds coordinatewise
    have hchild :
        intervals[i] =
          { min := fun x =>
              if x == p then
                row.interval.min p + (i.1 : ℤ) * row.interval.splitStep p parts
              else
                row.interval.min x
            max := fun x =>
              if x == p then
                row.interval.min p + ((i.1 + 1 : ℕ) : ℤ) * row.interval.splitStep p parts
              else
                row.interval.max x } := by
      simp [intervals, Interval.splitIntoParts, Interval.splitStep]
    -- reduce membership in the child interval to five 1D bounds
    rw [mem_pose_interval_iff]
    cases p
    -- in each case, exactly one coordinate bound changes (provided by `hi`)
    · -- θ₁ split
      refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
      · -- θ₁ bound uses `hi`
        simpa [hchild, Pose.getParam, parts] using hi
      · simpa [hchild] using hφ₁
      · simpa [hchild] using hθ₂
      · simpa [hchild] using hφ₂
      · simpa [hchild] using hα
    · -- φ₁ split
      refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
      · simpa [hchild] using hθ₁
      · simpa [hchild, Pose.getParam, parts] using hi
      · simpa [hchild] using hθ₂
      · simpa [hchild] using hφ₂
      · simpa [hchild] using hα
    · -- θ₂ split
      refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
      · simpa [hchild] using hθ₁
      · simpa [hchild] using hφ₁
      · simpa [hchild, Pose.getParam, parts] using hi
      · simpa [hchild] using hφ₂
      · simpa [hchild] using hα
    · -- φ₂ split
      refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
      · simpa [hchild] using hθ₁
      · simpa [hchild] using hφ₁
      · simpa [hchild] using hθ₂
      · simpa [hchild, Pose.getParam, parts] using hi
      · simpa [hchild] using hα
    · -- α split
      refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
      · simpa [hchild] using hθ₁
      · simpa [hchild] using hφ₁
      · simpa [hchild] using hθ₂
      · simpa [hchild] using hφ₂
      · simpa [hchild, Pose.getParam, parts] using hi

  -- Contradict the child certificate.
  rcases q_in_some_part with ⟨i, hqi⟩
  exact child_no_rupert i ⟨q, hqi, hrupert⟩

termination_by (tab.size - row.ID, 0, 0)
decreasing_by
  all_goals
    -- Help the termination checker: children are strictly after the parent in the table.
    have parts_pos : 0 < Row.partsForSplitCode row.split := by
      -- `row.split` identifies the parameter, and each supported split uses a positive arity.
      fin_cases p <;> simp [h.split, Row.splitCodeForParam, Row.partsForSplitCode]
    have hivs :
        1 ≤ (row.interval.splitIntoParts p (Row.partsForSplitCode row.split)).length := by
      simpa [Interval.splitIntoParts] using Nat.succ_le_of_lt parts_pos
    have hfirst : row.IDfirstChild < tab.size :=
      has_intervals_start_in_table tab row.IDfirstChild _ hivs h.intervals_good
    have hlt : row.ID < tab.size := Nat.lt_trans h.bound0 hfirst
    have hgt : row.ID < row.IDfirstChild + i.1 :=
      Nat.lt_of_lt_of_le h.bound0 (Nat.le_add_right _ _)
    grind

end

theorem Row.valid_imp_not_rupert
   (tab : Solution.Table) (tab_valid : tab.Valid)
   (hz : 0 < tab.size) :
    ¬ ∃ q ∈ tab[0].toPoseInterval, RupertPose q nopert.hull :=
  Row.valid_imp_not_rupert_ix tab 0 tab_valid tab[0] (tab_valid.valid_at hz)
