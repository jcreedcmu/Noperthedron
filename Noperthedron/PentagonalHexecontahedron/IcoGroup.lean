module

public import Noperthedron.Basic
public import Noperthedron.PentagonalHexecontahedron.IcoGroupData

@[expose] public section

/-!
# The icosahedral rotation group I over ℝ

`ico n` is the real matrix of the generated `icoEntry n` (IcoGroupData.lean;
its entries are in units of 1/20), and `icoMatrix g` its `Fin 60` version.
The group facts are decided over K by kernel computation in integer
coordinates and transported to ℝ through `IcoZ.val` (IcoField.lean):
- right multiplication by the three generators stays in the set (180
  products), and every element is a smaller element times a generator (BFS),
  which together give closure, `exists_icoMatrix_mul`;
- each `icoMatrix g` is a rotation (in SO(3));
- element 0 is the identity, and the 60 matrices sum to zero;
- element `icoRzIndex` is Rz(2π/5).
-/

namespace Noperthedron.PentagonalHexecontahedron

open scoped Matrix

abbrev IcoIndex := Fin 60

/-- Element `n` of the group over ℝ (any `n`; meaningful for `n < 60`). -/
noncomputable def ico (n : Nat) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 20 : ℝ) • (icoEntry n).toMatrix

/-- The rotation `g` of the icosahedral group. -/
noncomputable def icoMatrix (g : IcoIndex) : Matrix (Fin 3) (Fin 3) ℝ := ico g.val

def icoGenAt (k : Nat) : Nat := icoGen.getD k 0

def icoGenMulAt (g k : Nat) : Nat := (icoGenMul.getD g []).getD k 0

/-! ### Decided facts over K -/

/-- `8 (20 G_g) (20 G_s) = 160 (20 G_{g s})` for each generator s. -/
def icoGenCheck : Bool :=
  (List.range 60).all fun g => (List.range 3).all fun k =>
    decide (icoGenAt k < 60) && decide (icoGenMulAt g k < 60) &&
      decide (M3.mul8 (icoEntry g) (icoEntry (icoGenAt k)) =
        M3.scale 160 (icoEntry (icoGenMulAt g k)))

def icoBfsCheck : Bool :=
  (List.range 59).all fun i =>
    decide (icoBfsParent.getD (i + 1) 0 < i + 1) && decide (icoBfsGen.getD (i + 1) 0 < 3) &&
      decide (icoGenMulAt (icoBfsParent.getD (i + 1) 0) (icoBfsGen.getD (i + 1) 0) = i + 1)

/-- `8 (20 G)ᵀ (20 G) = 3200 I` and `64 det (20 G) = 64 · 8000`. -/
def icoRotationCheck : Bool :=
  (List.range 60).all fun g =>
    decide (M3.mul8 (M3.transpose (icoEntry g)) (icoEntry g) = M3.scalar 3200) &&
      decide (M3.det64 (icoEntry g) = ⟨512000, 0, 0, 0⟩)

/-- `icoEntry 0 + ... + icoEntry (n - 1)`. -/
def icoPartialSum : Nat → M3
  | 0 => M3.zero
  | n + 1 => M3.add (icoPartialSum n) (icoEntry n)

def icoSumCheck : Bool := decide (icoPartialSum 60 = M3.zero)

theorem icoGenCheck_eq : icoGenCheck = true := by decide +kernel

theorem icoBfsCheck_eq : icoBfsCheck = true := by decide +kernel

theorem icoRotationCheck_eq : icoRotationCheck = true := by decide +kernel

theorem icoSumCheck_eq : icoSumCheck = true := by decide +kernel

theorem icoEntry_zero : icoEntry 0 = M3.scalar 20 := by decide +kernel

/-! ### The group over ℝ -/

@[simp] theorem ico_zero : ico 0 = 1 := by
  rw [ico, icoEntry_zero, M3.toMatrix_scalar, smul_smul]
  norm_num

@[simp] theorem icoMatrix_zero : icoMatrix 0 = 1 := ico_zero

/-- From `8 A B = 160 C` over K: `(A/20) (B/20) = C/20` over ℝ. -/
theorem ico_mul_of_mul8 {a b c : Nat}
    (h : M3.mul8 (icoEntry a) (icoEntry b) = M3.scale 160 (icoEntry c)) :
    ico a * ico b = ico c := by
  have h' := congrArg M3.toMatrix h
  rw [M3.toMatrix_mul8, M3.toMatrix_scale] at h'
  have hab : (icoEntry a).toMatrix * (icoEntry b).toMatrix =
      (20 : ℝ) • (icoEntry c).toMatrix := by
    have := congrArg (fun M => (1 / 8 : ℝ) • M) h'
    simp only [smul_smul] at this
    norm_num at this
    exact this
  rw [ico, ico, ico, Matrix.smul_mul, Matrix.mul_smul, hab, smul_smul, smul_smul]
  norm_num

theorem ico_genMul {g k : Nat} (hg : g < 60) (hk : k < 3) :
    icoGenAt k < 60 ∧ icoGenMulAt g k < 60 ∧ ico g * ico (icoGenAt k) = ico (icoGenMulAt g k) := by
  have hc := icoGenCheck_eq
  simp only [icoGenCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc g hg k hk
  exact ⟨h1, h2, ico_mul_of_mul8 h3⟩

theorem ico_bfs {h : Nat} (h0 : 0 < h) (h60 : h < 60) :
    icoBfsParent.getD h 0 < h ∧ icoBfsGen.getD h 0 < 3 ∧
      icoGenMulAt (icoBfsParent.getD h 0) (icoBfsGen.getD h 0) = h := by
  have hc := icoBfsCheck_eq
  simp only [icoBfsCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨i, rfl⟩ : ∃ i, h = i + 1 := ⟨h - 1, by omega⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc i (by omega)
  exact ⟨h1, h2, h3⟩

/-- Closure of the 60 matrices under multiplication. -/
theorem exists_ico_mul (g h : Nat) (hg : g < 60) (hh : h < 60) :
    ∃ k < 60, ico g * ico h = ico k := by
  induction h using Nat.strong_induction_on generalizing g with
  | _ h ih =>
    rcases Nat.eq_zero_or_pos h with rfl | h0
    · exact ⟨g, hg, by rw [ico_zero, Matrix.mul_one]⟩
    · obtain ⟨hp, hs, hgm⟩ := ico_bfs h0 hh
      set p := icoBfsParent.getD h 0
      set s := icoBfsGen.getD h 0
      obtain ⟨-, -, hph⟩ := ico_genMul (g := p) (by omega) hs
      rw [hgm] at hph
      obtain ⟨k, hk, hgp⟩ := ih p hp g hg (by omega)
      obtain ⟨-, hk60, hks⟩ := ico_genMul hk hs
      refine ⟨icoGenMulAt k s, hk60, ?_⟩
      rw [← hph, ← Matrix.mul_assoc, hgp, hks]

theorem exists_icoMatrix_mul (g h : IcoIndex) :
    ∃ k : IcoIndex, icoMatrix g * icoMatrix h = icoMatrix k := by
  obtain ⟨k, hk, hmul⟩ := exists_ico_mul g.val h.val g.isLt h.isLt
  exact ⟨⟨k, hk⟩, hmul⟩

theorem icoMatrix_transpose_mul (g : IcoIndex) : (icoMatrix g)ᵀ * icoMatrix g = 1 := by
  have hc := icoRotationCheck_eq
  simp only [icoRotationCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  have h' := congrArg M3.toMatrix (hc g.val g.isLt).1
  rw [M3.toMatrix_mul8, M3.toMatrix_transpose, M3.toMatrix_scalar] at h'
  rw [icoMatrix, ico, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have := congrArg (fun M => (1 / 3200 : ℝ) • M) h'
  simp only [smul_smul] at this
  norm_num at this ⊢
  exact this

theorem icoMatrix_det (g : IcoIndex) : (icoMatrix g).det = 1 := by
  have hc := icoRotationCheck_eq
  simp only [icoRotationCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  have h' := congrArg IcoZ.val (hc g.val g.isLt).2
  rw [M3.val_det64, IcoZ.val_mk_int] at h'
  rw [icoMatrix, ico, Matrix.det_smul, Fintype.card_fin]
  push_cast at h'
  linarith

theorem icoMatrix_mem_SO3 (g : IcoIndex) :
    icoMatrix g ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  exact ⟨icoMatrix_transpose_mul g, icoMatrix_det g⟩

theorem toMatrix_icoPartialSum (n : Nat) :
    (icoPartialSum n).toMatrix = ∑ g ∈ Finset.range n, (icoEntry g).toMatrix := by
  induction n with
  | zero => simp [icoPartialSum, M3.toMatrix_zero]
  | succ n ih => rw [icoPartialSum, M3.toMatrix_add, ih, Finset.sum_range_succ]

theorem sum_icoMatrix : ∑ g : IcoIndex, icoMatrix g = 0 := by
  have hc := icoSumCheck_eq
  simp only [icoSumCheck, decide_eq_true_eq] at hc
  have h := toMatrix_icoPartialSum 60
  rw [hc, M3.toMatrix_zero, ← Fin.sum_univ_eq_sum_range] at h
  simp only [icoMatrix, ico, ← Finset.smul_sum, ← h, smul_zero]

/-! ### Rz(2π/5) is in the group -/

theorem cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (IcoZ.sqrt5 - 1) / 4 := by
  have hsq := IcoZ.sqrt5_sq
  rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  simp only [IcoZ.sqrt5] at hsq ⊢
  nlinarith [hsq]

theorem sin_two_pi_div_five : Real.sin (2 * Real.pi / 5) = IcoZ.s72 := by
  have hpos : 0 ≤ Real.sin (2 * Real.pi / 5) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hsq : Real.sin (2 * Real.pi / 5) ^ 2 = (5 + IcoZ.sqrt5) / 8 := by
    have h := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
    rw [cos_two_pi_div_five] at h
    have hr := IcoZ.sqrt5_sq
    nlinarith
  rw [IcoZ.s72, ← hsq, Real.sqrt_sq hpos]

theorem ico_rz : ico icoRzIndex = Rz_mat (2 * Real.pi / 5) := by
  have hc := cos_two_pi_div_five
  have hs := sin_two_pi_div_five
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ico, icoRzIndex, icoEntry, M3.toMatrix, M3.entry, IcoZ.val, hc, hs] <;> ring

end Noperthedron.PentagonalHexecontahedron
