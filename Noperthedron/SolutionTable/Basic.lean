import Noperthedron.SolutionTable.Defs
import Noperthedron.PoseInterval
import Noperthedron.Nopert

namespace Solution

def _root_.Pose.getParam (q : Pose) : Param → ℝ
| .θ₁ => q.θ₁
| .φ₁ => q.φ₁
| .θ₂ => q.θ₂
| .φ₂ => q.φ₂
| .α => q.α

structure Interval where
  min : Param → ℤ
  max : Param → ℤ
deriving DecidableEq

instance : Repr Interval where
  reprPrec i _ :=
    let params := [Param.θ₁, Param.φ₁, Param.θ₂, Param.φ₂, Param.α]
    let entries := params.map fun p =>
      s!"{repr p}: [{i.min p}, {i.max p}]"
    "{" ++ String.intercalate ",\n" entries ++ "}"

/--
A `Solution.Row` aims to closely model of exactly the data in Steininger and Yurkevich's big CSV file.
IDs start from zero. See [SY25] §7.1 for the meaning of all these fields.
-/
structure Row : Type where
   ID : ℕ
   nodeType : ℕ
   nrChildren : ℕ
   IDfirstChild : ℕ
   split : ℕ
   interval : Interval
   S_index : Fin 90
   wx_numerator : ℤ
   wy_numerator : ℤ
   w_denominator : ℕ
   P1_index : ℕ
   P2_index : ℕ
   P3_index : ℕ
   Q1_index : ℕ
   Q2_index : ℕ
   Q3_index : ℕ
   r : ℤ
   sigma_Q : Finset.Icc 0 1

abbrev Table : Type := Array Row

def decodeI (idx : ℕ) : ℕ := (idx % 45) / 15

def decodeK (idx : ℕ) : ℕ := idx % 15

def decodeL (idx : ℕ) : ℕ := idx / 45

def Row.decodeI (_row : Row) (idx : ℕ) : ℕ := Solution.decodeI idx

def Row.decodeK (_row : Row) (idx : ℕ) : ℕ := Solution.decodeK idx

def Row.decodeL (_row : Row) (idx : ℕ) : ℕ := Solution.decodeL idx

def Row.dl (row : Row) : ℕ := (row.decodeL row.P1_index + row.decodeL row.Q1_index) % 2

def Row.dkRot (row : Row) : ℕ := (row.decodeK row.P1_index + 15 - row.decodeK row.Q1_index) % 15

def Row.dkRef (row : Row) : ℕ := (row.decodeK row.P1_index + row.decodeK row.Q1_index) % 15

/--
The common denominator of θ₁, θ₂, φ₁, φ₂, α rational
representation in the table. See [SY25 §7.2]
-/
def DENOM : ℝ := 15360000

noncomputable
def Interval.toPoseInterval (iv : Interval) : PoseInterval where
  min := { θ₁ := iv.min .θ₁ / DENOM
           θ₂ := iv.min .θ₂ / DENOM
           φ₁ := iv.min .φ₁ / DENOM
           φ₂ := iv.min .φ₂ / DENOM
           α := iv.min .α / DENOM}
  max := { θ₁ := iv.max .θ₁ / DENOM
           θ₂ := iv.max .θ₂ / DENOM
           φ₁ := iv.max .φ₁ / DENOM
           φ₂ := iv.max .φ₂ / DENOM
           α := iv.max .α / DENOM}

noncomputable
def Row.toPoseInterval (row : Row) : PoseInterval :=
  row.interval.toPoseInterval

noncomputable
def Row.w (row : Row) : ℝ² :=
  !₂[(row.wx_numerator : ℝ) / row.w_denominator, (row.wy_numerator : ℝ) / row.w_denominator]

def Row.wUnitCheck (row : Row) : Prop :=
  row.w_denominator ≠ 0 ∧
    row.wx_numerator * row.wx_numerator + row.wy_numerator * row.wy_numerator =
      (row.w_denominator : ℤ) * (row.w_denominator : ℤ)
deriving Decidable

lemma Row.w_unit_of_wUnitCheck (row : Row) (h : row.wUnitCheck) : ‖row.w‖ = 1 := by
  rcases h with ⟨hden0, hpyth⟩
  have hdenR : (row.w_denominator : ℝ) ≠ 0 := by
    exact_mod_cast hden0
  have hpythR :
      (row.wx_numerator : ℝ) * (row.wx_numerator : ℝ) +
          (row.wy_numerator : ℝ) * (row.wy_numerator : ℝ) =
        (row.w_denominator : ℝ) * (row.w_denominator : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hpyth
    simpa [Int.cast_add, Int.cast_mul] using this
  have hnormsq : ‖row.w‖ ^ 2 = 1 := by
    -- Expand the Euclidean norm on `ℝ²` and use the Pythagorean identity stored in the row.
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Row.w, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
    simp only [pow_two]
    -- Reduce to the real equality `(wx^2 + wy^2) / denom^2 = 1`.
    have hdenR2 : (row.w_denominator : ℝ) * (row.w_denominator : ℝ) ≠ 0 :=
      mul_ne_zero hdenR hdenR
    calc
      (row.wx_numerator : ℝ) / (row.w_denominator : ℝ) *
            ((row.wx_numerator : ℝ) / (row.w_denominator : ℝ)) +
      (row.wy_numerator : ℝ) / (row.w_denominator : ℝ) *
            ((row.wy_numerator : ℝ) / (row.w_denominator : ℝ)) =
          ((row.wx_numerator : ℝ) * (row.wx_numerator : ℝ) +
                (row.wy_numerator : ℝ) * (row.wy_numerator : ℝ)) /
              ((row.w_denominator : ℝ) * (row.w_denominator : ℝ)) := by
        field_simp [hdenR]
      _ =
          ((row.w_denominator : ℝ) * (row.w_denominator : ℝ)) /
            ((row.w_denominator : ℝ) * (row.w_denominator : ℝ)) := by
        simp [hpythR]
      _ = 1 := by
        simp [div_self, hdenR2]
  have hsq : ‖row.w‖ ^ 2 = (1 : ℝ) ^ 2 := by
    simpa using hnormsq
  rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hsq with hpos | hneg
  · exact hpos
  · have hnonneg : (0 : ℝ) ≤ ‖row.w‖ := norm_nonneg _
    have hlt : ‖row.w‖ < 0 := by
      simp [hneg]
    exact (not_lt_of_ge hnonneg hlt).elim

/--
Best-effort, decidable check that a local-theorem row’s `(P,Q)` triangle indices are related by a
simple dihedral-style symmetry on the 15-fold rotation index, plus an optional global sign flip.

Empirically (on the published `solution_tree.parquet`), every `nodeType=2` row satisfies this with
the vertex encoding `idx = k + 15*i + 45*l` (`k ∈ {0..14}`, `i ∈ {0,1,2}`, `l ∈ {0,1}`).

This is intended as a bridge toward a fully decidable Lean-side local-row checker: once we have a
formalization of how such symmetries induce `Triangle.Congruent`, this predicate can supply the
congruence witness needed by the (rational) local theorem.
-/
def Row.localCongruenceIndexCheck (row : Row) : Prop :=
  let p := (row.P1_index, row.P2_index, row.P3_index)
  let q := (row.Q1_index, row.Q2_index, row.Q3_index)

  -- Bound the indices into the 90-vertex encoding.
  (p.1 < 90 ∧ p.2.1 < 90 ∧ p.2.2 < 90 ∧ q.1 < 90 ∧ q.2.1 < 90 ∧ q.2.2 < 90) ∧
  -- Orbit indices must match position-wise.
  (row.decodeI p.1 = row.decodeI q.1 ∧
   row.decodeI p.2.1 = row.decodeI q.2.1 ∧
   row.decodeI p.2.2 = row.decodeI q.2.2) ∧
  -- l-parity differs by a single bit (global sign flip).
  ((row.decodeL q.1 + row.dl) % 2 = row.decodeL p.1 ∧
   (row.decodeL q.2.1 + row.dl) % 2 = row.decodeL p.2.1 ∧
   (row.decodeL q.2.2 + row.dl) % 2 = row.decodeL p.2.2) ∧
  -- And either a pure rotation on k (mod 15) or a reflection+rotation.
  (((row.decodeK q.1 + row.dkRot) % 15 = row.decodeK p.1 ∧
    (row.decodeK q.2.1 + row.dkRot) % 15 = row.decodeK p.2.1 ∧
    (row.decodeK q.2.2 + row.dkRot) % 15 = row.decodeK p.2.2) ∨
   ((row.dkRef + 15 - row.decodeK q.1) % 15 = row.decodeK p.1 ∧
    (row.dkRef + 15 - row.decodeK q.2.1) % 15 = row.decodeK p.2.1 ∧
    (row.dkRef + 15 - row.decodeK q.2.2) % 15 = row.decodeK p.2.2 ∧
    row.decodeI p.1 = row.decodeI p.2.1 ∧
    row.decodeI p.1 = row.decodeI p.2.2))
deriving Decidable

def Table.HasIntervals (tab : Table) (start : ℕ) (intervals : List Interval) : Prop :=
  ∀ i : Fin intervals.length,
    ∃ (h : start + i.val < tab.size), tab[start + i.val].interval = intervals[i]
deriving Decidable

/-
Do we want to write this validity checker instead as a manifestly
computational program returning Bool?
-/

structure Row.ValidGlobal (tab : Table) (row : Row) : Prop where
  nodeType : row.nodeType = 1
  no_rupert : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull

structure Row.ValidLocal (tab : Table) (row : Row) : Prop where
  nodeType : row.nodeType = 2
  congruence_check : row.localCongruenceIndexCheck
  no_rupert : ¬ ∃ q ∈ row.toPoseInterval, RupertPose q nopert.hull

def Interval.lower_half (param : Param) (interval : Interval) : Interval := {
  min := interval.min
  max := fun p => if p == param then (interval.min p + interval.max p)/2 else interval.max p
}

def Interval.upper_half (param : Param) (interval : Interval) : Interval := {
  min := fun p => if p == param then (interval.min p + interval.max p)/2 else interval.min p
  max := interval.max
}

def Interval.splitStep (param : Param) (parts : ℕ) (interval : Interval) : ℤ :=
  (interval.max param - interval.min param) / (parts : ℤ)

def Interval.splitIntoParts (param : Param) (parts : ℕ) (interval : Interval) : List Interval :=
  let lo := interval.min param
  let step := interval.splitStep param parts
  List.ofFn fun i : Fin parts =>
    { min := fun p => if p == param then lo + (i.1 : ℤ) * step else interval.min p
      max := fun p => if p == param then lo + ((i.1 + 1 : ℕ) : ℤ) * step else interval.max p }

def Row.splitCodeForParam : Param → ℕ
| .θ₁ => 1
| .φ₁ => 2
| .θ₂ => 3
| .φ₂ => 4
| .α => 5

def Row.partsForSplitCode : ℕ → ℕ
| 1 => 4
| 2 => 30
| 3 => 4
| 4 => 15
| 5 => 30
| _ => 0

structure Row.ValidSplitParam (tab : Table) (row : Row) (param : Param) : Prop where
  split : row.split = Row.splitCodeForParam param
  parts : row.nrChildren = Row.partsForSplitCode row.split
  step_ok :
    row.interval.min param +
      (Row.partsForSplitCode row.split : ℤ) *
        row.interval.splitStep param (Row.partsForSplitCode row.split) =
      row.interval.max param
  bound0 : row.ID < row.IDfirstChild
  intervals_good :
    tab.HasIntervals row.IDfirstChild
      (row.interval.splitIntoParts param (Row.partsForSplitCode row.split))

instance (tab : Table) (row : Row) (param : Param) : Decidable (Row.ValidSplitParam tab row param) :=
  decidable_of_iff
    (row.split = Row.splitCodeForParam param ∧
     row.nrChildren = Row.partsForSplitCode row.split ∧
     row.interval.min param +
        (Row.partsForSplitCode row.split : ℤ) *
          row.interval.splitStep param (Row.partsForSplitCode row.split) =
        row.interval.max param ∧
     ∃ (_bound0 : row.ID < row.IDfirstChild),
     tab.HasIntervals row.IDfirstChild
       (row.interval.splitIntoParts param (Row.partsForSplitCode row.split)))
    ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
     fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

def Row.ValidBinarySplit (tab : Table) (row : Row) : Prop :=
  ((row.split = 1 ∧ row.ValidSplitParam tab .θ₁) ∨
   (row.split = 2 ∧ row.ValidSplitParam tab .φ₁) ∨
   (row.split = 3 ∧ row.ValidSplitParam tab .θ₂) ∨
   (row.split = 4 ∧ row.ValidSplitParam tab .φ₂) ∨
   (row.split = 5 ∧ row.ValidSplitParam tab .α))
deriving Decidable

/-
Equivalently I probably could have done

def cubeFold {α β : Type} (fs : List (α → β → β)) (b : β) : List α → List β
| [] => pure b
| (h :: tl) => do  cubeFold fs ((← fs) h b) tl

but I imagine it might be less annoying to do reasoning on the expanded-out nonmonadic version.
-/
section Test

def example_interval : Interval := {
  min := fun
  | .θ₁ => 100
  | .θ₂ => 200
  | .φ₁ => 300
  | .φ₂ => 400
  | .α => 16
  max := fun
  | .θ₁ => 116
  | .θ₂ => 216
  | .φ₁ => 316
  | .φ₂ => 416
  | .α => 32
}

/--
info: [{Solution.Param.θ₁: [100, 108],
 Solution.Param.φ₁: [300, 316],
 Solution.Param.θ₂: [200, 208],
 Solution.Param.φ₂: [400, 416],
 Solution.Param.α: [16, 32]},
 {Solution.Param.θ₁: [100, 108],
 Solution.Param.φ₁: [300, 316],
 Solution.Param.θ₂: [208, 216],
 Solution.Param.φ₂: [400, 416],
 Solution.Param.α: [16, 32]},
 {Solution.Param.θ₁: [108, 116],
 Solution.Param.φ₁: [300, 316],
 Solution.Param.θ₂: [200, 208],
 Solution.Param.φ₂: [400, 416],
 Solution.Param.α: [16, 32]},
 {Solution.Param.θ₁: [108, 116],
 Solution.Param.φ₁: [300, 316],
 Solution.Param.θ₂: [208, 216],
 Solution.Param.φ₂: [400, 416],
 Solution.Param.α: [16, 32]}]
-/
#guard_msgs in
#eval cubeFold (α := Param) (β := Interval) [Interval.lower_half, Interval.upper_half] example_interval [.θ₁, .θ₂]

end Test

def Row.ValidFullSplit (tab : Table) (row : Row) : Prop :=
  row.nrChildren = 32 ∧ row.split = 6 ∧ row.IDfirstChild > row.ID ∧
  tab.HasIntervals row.IDfirstChild (cubeFold [Interval.lower_half, Interval.upper_half] row.interval [.θ₁, .φ₁, .θ₂, .φ₂, .α])
deriving Decidable

def Row.ValidSplit (tab : Table) (row : Row) : Prop :=
  (row.nodeType = (3 : ℕ)) ∧ (row.ValidBinarySplit tab ∨ row.ValidFullSplit tab)
deriving Decidable

instance : Coe Interval (Set Pose) where
  coe iv := { q : Pose | q ∈ iv.toPoseInterval }

lemma cube_fold_nonempty_aux {α β : Type} {fs : List (α → β → β)} (hfs : fs ≠ []) (b : β) (as : List α) :
   0 < (cubeFold fs b as).length := by
  match as with
  | [] => simp [cubeFold]
  | h :: tl =>
    simp only [cubeFold, List.length_flatMap]
    have (f : α → β → β) : 0 < (cubeFold fs (f h b) tl).length := by
      exact cube_fold_nonempty_aux hfs (f h b) tl
    refine List.sum_pos _ ?_ (by simpa using hfs)
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨f, hf1, hf2⟩ := hx
    rw [← hf2]
    exact this f

lemma cube_fold_nonempty {α β : Type} {fs : List (α → β → β)} (hfs : fs ≠ []) (b : β) (as : List α) :
   1 ≤ (cubeFold fs b as).length := cube_fold_nonempty_aux hfs b as

lemma cube_fold_halves (h : Param) (tl : List Param) (iv : Interval)
    (lower : Param → Interval → Interval)
    (upper : Param → Interval → Interval) :
    cubeFold [lower, upper] iv (h :: tl) =
      cubeFold [lower, upper] (lower h iv) tl ++
      cubeFold [lower, upper] (upper h iv) tl := by
  simp [cubeFold]

lemma has_intervals_start_in_table (tab : Table) (n : ℕ) (ivs : List Interval) (hivs : 1 ≤ ivs.length)
    (hi : tab.HasIntervals n ivs) : n < tab.size := by
  unfold Table.HasIntervals at hi
  simpa using (hi ⟨0, Nat.zero_lt_of_lt hivs⟩).1

lemma has_intervals_concat (tab : Table) (start : ℕ) (ivs1 ivs2 : List Interval) :
    tab.HasIntervals start (ivs1 ++ ivs2) ↔
    tab.HasIntervals start ivs1 ∧ tab.HasIntervals (start + ivs1.length) ivs2 := by
  constructor
  · intro hi
    constructor
    · unfold Table.HasIntervals at hi ⊢
      intro i; simpa using hi (Fin.castLE (by simp) i)
    · unfold Table.HasIntervals at hi ⊢
      intro i
      specialize hi ⟨ivs1.length + i, by simp⟩
      simp at hi
      obtain ⟨h, p⟩ := hi
      replace h : start + ivs1.length + (↑i : ℕ) < Array.size tab :=
        by ring_nf at h ⊢; exact h
      use h; ring_nf at p ⊢; exact p
  · rintro ⟨h1, h2⟩
    unfold Table.HasIntervals at h1 h2 ⊢
    intro i
    if h : i < ivs1.length then
      specialize h1 ⟨i, h⟩
      simp_all
    else
      replace h := Nat.le_of_not_lt h
      have : (i : ℕ) - ivs1.length < ivs2.length := by grind
      specialize h2 ⟨(i : ℕ) - ivs1.length, this⟩
      simp_all
