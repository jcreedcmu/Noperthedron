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

/-- Repeated bisection covers the original interval, independently of the
row table or the property that its leaves will certify. -/
lemma mem_cubeFold_halves {q : Pose ℝ} {iv : Interval} (params : List Param)
    (hq : q ∈ iv.toReal) :
    ∃ part ∈ cubeFold [Interval.lower_half, Interval.upper_half] iv params,
      q ∈ part.toReal := by
  induction params generalizing iv with
  | nil => exact ⟨iv, by simp [cubeFold], hq⟩
  | cons p params ih =>
    obtain ⟨n, hn⟩ := mem_interval_imp_mem_some_part q iv p 2 hq
    obtain ⟨part, hpart, hq⟩ := ih hn
    refine ⟨part, ?_, hq⟩
    simp only [cubeFold, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append]
    fin_cases n
    · exact Or.inl hpart
    · exact Or.inr hpart

/-- A point in one of the listed intervals occurs in its corresponding row. -/
lemma HasIntervalsAt.exists_row {get : ℕ → Row} {size start : ℕ} {ivs : List Interval}
    (h : HasIntervalsAt get size start ivs) {part : Interval} (hpart : part ∈ ivs)
    {q : Pose ℝ} (hq : q ∈ part.toReal) :
    ∃ j, start ≤ j ∧ j < size ∧ q ∈ (get j).interval.toReal := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hpart
  obtain ⟨hj, heq⟩ := h ⟨i, hi⟩
  exact ⟨start + i, Nat.le_add_right _ _, hj, by rwa [heq]⟩

/-- Every point of a valid split lies in a child with a strictly larger row
index. This is the only fact about splits needed by the table's soundness proof. -/
lemma Row.ValidSplitAt.exists_child {get : ℕ → Row} {size : ℕ} {row : Row}
    (h : row.ValidSplitAt get size) {q : Pose ℝ} (hq : q ∈ row.interval.toReal) :
    ∃ j, row.ID < j ∧ j < size ∧ q ∈ (get j).interval.toReal := by
  obtain ⟨-, hs | hf⟩ := h
  · obtain ⟨p, -, h⟩ := hs
    let : NeZero row.nrChildren := ⟨h.nonzero_children⟩
    obtain ⟨n, hn⟩ := mem_interval_imp_mem_some_part q row.interval p row.nrChildren hq
    refine ⟨row.IDfirstChild + n, ?_, ?_, ?_⟩
    · have := h.id_in_table; omega
    · have := h.children_in_table; have := n.isLt; omega
    · rwa [h.children_intervals_good n]
  · obtain ⟨-, -, hgt, hivs⟩ := hf
    obtain ⟨part, hpart, hq⟩ := mem_cubeFold_halves Param.splitOrder hq
    obtain ⟨j, hj, hjs, hq⟩ := hivs.exists_row hpart hq
    exact ⟨j, lt_of_lt_of_le hgt hj, hjs, hq⟩

theorem valid_split_imp_no_rupert (get : ℕ → Row) (size : ℕ) (row : Row)
    (hr : row.ValidSplitAt get size)
    (ih : ∀ j, row.ID < j → j < size →
      ¬ ∃ q ∈ (get j).interval.toReal, RupertPose q exactPolyhedron.hull) :
    ¬ ∃ q ∈ row.interval.toReal, RupertPose q exactPolyhedron.hull := by
  rintro ⟨q, hq, hrupert⟩
  obtain ⟨j, hj, hjs, hq⟩ := hr.exists_child hq
  exact ih j hj hjs ⟨q, hq, hrupert⟩

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
