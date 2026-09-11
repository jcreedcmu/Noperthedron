module

public import Noperthedron.SolutionTable.Basic
public import Noperthedron.SolutionTable.Local
public import Noperthedron.SolutionTable.Global
public import Noperthedron.Vertices.Exact

public section


namespace Noperthedron.Solution

/-- Membership in the realification of a rational `Interval`, read off one parameter
at a time. This is the single entry point for interval-membership reasoning below. -/
lemma mem_toReal_iff {q : Pose ℝ} {iv : Interval} :
    q ∈ iv.toReal ↔
      ∀ p : Param, q.getParam p ∈ Set.Icc (iv.min.getParam p : ℝ) (iv.max.getParam p : ℝ) := by
  show q ∈ Set.Icc iv.minPose iv.maxPose ↔ _
  simp only [Set.mem_Icc, Pose.le_iff_forall_getParam, Interval.minPose, Interval.maxPose,
    Pose.toReal_getParam, ← forall_and]

lemma mem_nth_part (q : Pose ℝ) (iv : Interval) (p : Param) (N : ℕ) [hN : NeZero N] (n : Fin N)
    (hq : q ∈ iv.toReal)
    (bound : q.getParam p ∈ Set.Icc (iv.interpolate p N n : ℝ) (iv.interpolate p N (n + 1) : ℝ)) :
    q ∈ (iv.nth_part p N n).toReal := by
  rw [mem_toReal_iff] at hq ⊢
  intro p'
  rcases eq_or_ne p' p with rfl | hne
  · simpa [Interval.nth_part, PoseInterval.min, PoseInterval.max] using bound
  · simpa [Interval.nth_part, PoseInterval.min, PoseInterval.max, hne] using hq p'

/-- Discrete intermediate value: a point lying between the first and last terms of a
finite sequence lies between some pair of consecutive terms. (No monotonicity needed.) -/
lemma exists_mem_Icc_consecutive (c : ℕ → ℝ) (M : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (c 0) (c (M + 1))) :
    ∃ n : Fin (M + 1), x ∈ Set.Icc (c n) (c (n + 1)) := by
  induction M with
  | zero => exact ⟨0, hx⟩
  | succ M ih =>
    rcases le_total x (c (M + 1)) with h | h
    · obtain ⟨n, hn⟩ := ih ⟨hx.1, h⟩
      exact ⟨n.castSucc, hn⟩
    · exact ⟨Fin.last (M + 1), h, hx.2⟩

lemma mem_interval_imp_mem_some_part (q : Pose ℝ) (iv : Interval) (p : Param)
     (N : ℕ) [NeZero N] (hq : q ∈ iv.toReal) :
     ∃ n : Fin N, q ∈ (iv.nth_part p N n).toReal := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  have h0 : iv.interpolate p (M + 1) 0 = iv.min.getParam p := by
    simp [Interval.interpolate]
  have h1 : iv.interpolate p (M + 1) (M + 1) = iv.max.getParam p := by
    simp [Interval.interpolate, div_self (by positivity : ((M : ℚ) + 1) ≠ 0)]
  obtain ⟨n, hn⟩ := exists_mem_Icc_consecutive
    (fun k => (iv.interpolate p (M + 1) k : ℝ)) M
    (by simpa only [h0, h1] using mem_toReal_iff.mp hq p)
  exact ⟨n, mem_nth_part q iv p (M + 1) n hq hn⟩

lemma non_rupert_parts_imp_non_rupert (p : Param) {iv : Interval} (N : ℕ) [hN : NeZero N]
    (qq : ∀ n : Fin N, ¬∃ q ∈ (Interval.nth_part p iv N n).toReal, RupertPose q exactPolyhedron.hull) :
    ¬∃ q ∈ iv.toReal, RupertPose q exactPolyhedron.hull := by
  rintro ⟨q, hq1, hq2⟩
  obtain ⟨n, hq1⟩ := mem_interval_imp_mem_some_part q iv p N hq1
  exact qq n ⟨q, hq1, hq2⟩

/-- Since the two halves are `nth_part 2 0` and `nth_part 2 1`, this is
`non_rupert_parts_imp_non_rupert` at `N = 2`. Used in the cube-fold part of the proof below. -/
lemma non_rupert_halves_imp_non_rupert {p : Param} {iv : Interval}
    (q1 : ¬∃ q ∈ (Interval.lower_half p iv).toReal, RupertPose q exactPolyhedron.hull)
    (q2 : ¬∃ q ∈ (Interval.upper_half p iv).toReal, RupertPose q exactPolyhedron.hull) :
    ¬∃ q ∈ iv.toReal, RupertPose q exactPolyhedron.hull := by
  refine non_rupert_parts_imp_non_rupert p 2 fun n => ?_
  fin_cases n
  · exact q1
  · exact q2

/-!
## From row validity to "no Rupert pose in the row's box"

Validity constrains each row to refer only to rows with larger IDs (its
children), so the argument is a strong induction on the number of rows after
the row in question.  Each helper theorem below takes the induction hypothesis
`ih` — "no Rupert pose in any row strictly after this one" — as an explicit
argument; `Row.valid_imp_not_rupert_ix` ties the knot.
-/

/-- If the `2^|params|` leaves of the cube of halvings of `interval` sit in the
table at consecutive rows starting at `n`, and none of those rows admits a
Rupert pose, then neither does `interval`.  Structural induction on `params`. -/
theorem has_intervals_imp_no_rupert (get : ℕ → Row) (size n : ℕ) (interval : Interval)
    (params : List Param)
    (hi : HasIntervalsAt get size n
      (cubeFold [Interval.lower_half, Interval.upper_half] interval params))
    (ih : ∀ j, n ≤ j → j < size →
      ¬ ∃ q ∈ (get j).interval.toReal, RupertPose q exactPolyhedron.hull) :
    ¬ ∃ q ∈ interval.toReal, RupertPose q exactPolyhedron.hull := by
  induction params generalizing n interval with
  | nil =>
    obtain ⟨hn, he⟩ := hi ⟨0, by simp [cubeFold]⟩
    simp only [add_zero, cubeFold, Fin.getElem_fin, List.getElem_cons_zero] at hn he
    rw [← he]
    exact ih n le_rfl hn
  | cons h tl ihp =>
    rw [cube_fold_halves, has_intervals_concat] at hi
    obtain ⟨h1, h2⟩ := hi
    exact non_rupert_halves_imp_non_rupert (ihp _ _ h1 ih)
      (ihp _ _ h2 fun j hj => ih j (by omega))

theorem valid_param_split_imp_no_rupert (get : ℕ → Row) (size : ℕ) (row : Row)
    (p : Param) (h : Row.ValidSplitParamAt get size row p)
    (ih : ∀ j, row.ID < j → j < size →
      ¬ ∃ q ∈ (get j).interval.toReal, RupertPose q exactPolyhedron.hull) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨hid, hkids, hnzk, hkiv⟩ := h
  refine non_rupert_parts_imp_non_rupert p row.nrChildren (hN := ⟨hnzk⟩) fun n => ?_
  rw [← hkiv n]
  exact ih _ (by omega) (by omega)

theorem valid_single_param_split_imp_no_rupert (get : ℕ → Row) (size : ℕ) (row : Row)
    (hr : Row.ValidSingleParamSplitAt get size row)
    (ih : ∀ j, row.ID < j → j < size →
      ¬ ∃ q ∈ (get j).interval.toReal, RupertPose q exactPolyhedron.hull) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨p, -, h⟩ := hr
  exact valid_param_split_imp_no_rupert get size row p h ih

theorem valid_full_split_imp_no_rupert (get : ℕ → Row) (size : ℕ) (row : Row)
    (hr : Row.ValidFullSplitAt get size row)
    (ih : ∀ j, row.ID < j → j < size →
      ¬ ∃ q ∈ (get j).interval.toReal, RupertPose q exactPolyhedron.hull) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨-, -, hgt, hi⟩ := hr
  exact has_intervals_imp_no_rupert get size row.IDfirstChild row.interval _ hi
    fun j hj => ih j (by omega)

theorem valid_split_imp_no_rupert (get : ℕ → Row) (size : ℕ) (row : Row)
    (hr : row.ValidSplitAt get size)
    (ih : ∀ j, row.ID < j → j < size →
      ¬ ∃ q ∈ (get j).interval.toReal, RupertPose q exactPolyhedron.hull) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  obtain ⟨-, hr | hr⟩ := hr
  · exact valid_single_param_split_imp_no_rupert get size row hr ih
  · exact valid_full_split_imp_no_rupert get size row hr ih

/-- No row of a valid table admits a Rupert pose.  Strong induction on
`size - i`: a split row only refers to rows with larger IDs, and leaves are
handled by the global/local theorems. -/
theorem Row.valid_imp_not_rupert_ix
    (get : ℕ → Row) (size : ℕ) (rowsValid : RowsValidAt get size)
    (i : ℕ) (hi : i < size) :
    ¬ ∃ q ∈ (get i).interval.toReal, RupertPose q exactPolyhedron.hull := by
  induction hk : size - i using Nat.strongRecOn generalizing i with
  | ind k ih =>
  obtain ⟨rowID, rowValid, -⟩ := rowsValid ⟨i, hi⟩
  have rowID' : (get i).ID = i := rowID
  have ih' : ∀ j, (get i).ID < j → j < size →
      ¬ ∃ q ∈ (get j).interval.toReal, RupertPose q exactPolyhedron.hull :=
    fun j hj hjs => ih (size - j) (by omega) j hjs rfl
  rcases rowValid with split | global | localRow | localRow₂
  · exact valid_split_imp_no_rupert get size (get i) split ih'
  · exact valid_global_imp_no_rupert (get i) global
  · exact valid_local_imp_no_rupert (get i) localRow
  · exact valid_local₂_imp_no_rupert (get i) localRow₂

theorem Row.valid_imp_not_rupert
    (get : ℕ → Row) (size : ℕ) (rowsValid : RowsValidAt get size)
    (hz : 0 < size) :
    ¬ ∃ q ∈ (get 0).interval.toReal, RupertPose q exactPolyhedron.hull :=
  Row.valid_imp_not_rupert_ix get size rowsValid 0 hz

end Noperthedron.Solution

end
