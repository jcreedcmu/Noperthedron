import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[132042, 133770). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_132042 : RangeOk getRow 2051521 132042 132106 := by
  decide +kernel

private theorem r_132106 : RangeOk getRow 2051521 132106 132170 := by
  decide +kernel

private theorem r_132170 : RangeOk getRow 2051521 132170 132234 := by
  decide +kernel

private theorem r_132234 : RangeOk getRow 2051521 132234 132298 := by
  decide +kernel

private theorem r_132298 : RangeOk getRow 2051521 132298 132362 := by
  decide +kernel

private theorem r_132362 : RangeOk getRow 2051521 132362 132426 := by
  decide +kernel

private theorem r_132426 : RangeOk getRow 2051521 132426 132490 := by
  decide +kernel

private theorem r_132490 : RangeOk getRow 2051521 132490 132554 := by
  decide +kernel

private theorem r_132554 : RangeOk getRow 2051521 132554 132618 := by
  decide +kernel

private theorem r_132618 : RangeOk getRow 2051521 132618 132682 := by
  decide +kernel

private theorem r_132682 : RangeOk getRow 2051521 132682 132746 := by
  decide +kernel

private theorem r_132746 : RangeOk getRow 2051521 132746 132810 := by
  decide +kernel

private theorem r_132810 : RangeOk getRow 2051521 132810 132874 := by
  decide +kernel

private theorem r_132874 : RangeOk getRow 2051521 132874 132938 := by
  decide +kernel

private theorem r_132938 : RangeOk getRow 2051521 132938 133002 := by
  decide +kernel

private theorem r_133002 : RangeOk getRow 2051521 133002 133066 := by
  decide +kernel

private theorem r_133066 : RangeOk getRow 2051521 133066 133130 := by
  decide +kernel

private theorem r_133130 : RangeOk getRow 2051521 133130 133194 := by
  decide +kernel

private theorem r_133194 : RangeOk getRow 2051521 133194 133258 := by
  decide +kernel

private theorem r_133258 : RangeOk getRow 2051521 133258 133322 := by
  decide +kernel

private theorem r_133322 : RangeOk getRow 2051521 133322 133386 := by
  decide +kernel

private theorem r_133386 : RangeOk getRow 2051521 133386 133450 := by
  decide +kernel

private theorem r_133450 : RangeOk getRow 2051521 133450 133514 := by
  decide +kernel

private theorem r_133514 : RangeOk getRow 2051521 133514 133578 := by
  decide +kernel

private theorem r_133578 : RangeOk getRow 2051521 133578 133642 := by
  decide +kernel

private theorem r_133642 : RangeOk getRow 2051521 133642 133706 := by
  decide +kernel

private theorem r_133706 : RangeOk getRow 2051521 133706 133770 := by
  decide +kernel

private theorem s_132106 : RangeOk getRow 2051521 132042 132106 := r_132042
private theorem s_132170 : RangeOk getRow 2051521 132042 132170 :=
  s_132106.append (by norm_num) r_132106
private theorem s_132234 : RangeOk getRow 2051521 132042 132234 :=
  s_132170.append (by norm_num) r_132170
private theorem s_132298 : RangeOk getRow 2051521 132042 132298 :=
  s_132234.append (by norm_num) r_132234
private theorem s_132362 : RangeOk getRow 2051521 132042 132362 :=
  s_132298.append (by norm_num) r_132298
private theorem s_132426 : RangeOk getRow 2051521 132042 132426 :=
  s_132362.append (by norm_num) r_132362
private theorem s_132490 : RangeOk getRow 2051521 132042 132490 :=
  s_132426.append (by norm_num) r_132426
private theorem s_132554 : RangeOk getRow 2051521 132042 132554 :=
  s_132490.append (by norm_num) r_132490
private theorem s_132618 : RangeOk getRow 2051521 132042 132618 :=
  s_132554.append (by norm_num) r_132554
private theorem s_132682 : RangeOk getRow 2051521 132042 132682 :=
  s_132618.append (by norm_num) r_132618
private theorem s_132746 : RangeOk getRow 2051521 132042 132746 :=
  s_132682.append (by norm_num) r_132682
private theorem s_132810 : RangeOk getRow 2051521 132042 132810 :=
  s_132746.append (by norm_num) r_132746
private theorem s_132874 : RangeOk getRow 2051521 132042 132874 :=
  s_132810.append (by norm_num) r_132810
private theorem s_132938 : RangeOk getRow 2051521 132042 132938 :=
  s_132874.append (by norm_num) r_132874
private theorem s_133002 : RangeOk getRow 2051521 132042 133002 :=
  s_132938.append (by norm_num) r_132938
private theorem s_133066 : RangeOk getRow 2051521 132042 133066 :=
  s_133002.append (by norm_num) r_133002
private theorem s_133130 : RangeOk getRow 2051521 132042 133130 :=
  s_133066.append (by norm_num) r_133066
private theorem s_133194 : RangeOk getRow 2051521 132042 133194 :=
  s_133130.append (by norm_num) r_133130
private theorem s_133258 : RangeOk getRow 2051521 132042 133258 :=
  s_133194.append (by norm_num) r_133194
private theorem s_133322 : RangeOk getRow 2051521 132042 133322 :=
  s_133258.append (by norm_num) r_133258
private theorem s_133386 : RangeOk getRow 2051521 132042 133386 :=
  s_133322.append (by norm_num) r_133322
private theorem s_133450 : RangeOk getRow 2051521 132042 133450 :=
  s_133386.append (by norm_num) r_133386
private theorem s_133514 : RangeOk getRow 2051521 132042 133514 :=
  s_133450.append (by norm_num) r_133450
private theorem s_133578 : RangeOk getRow 2051521 132042 133578 :=
  s_133514.append (by norm_num) r_133514
private theorem s_133642 : RangeOk getRow 2051521 132042 133642 :=
  s_133578.append (by norm_num) r_133578
private theorem s_133706 : RangeOk getRow 2051521 132042 133706 :=
  s_133642.append (by norm_num) r_133642
private theorem s_133770 : RangeOk getRow 2051521 132042 133770 :=
  s_133706.append (by norm_num) r_133706

/-- Rows `[132042, 133770)` are valid. -/
theorem rangeOk_132042_133770 : RangeOk getRow 2051521 132042 133770 := s_133770

end Noperthedron.Solution
