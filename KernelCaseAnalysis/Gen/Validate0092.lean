import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[202106, 203834). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_202106 : RangeOk getRow 2051521 202106 202170 := by
  decide +kernel

private theorem r_202170 : RangeOk getRow 2051521 202170 202234 := by
  decide +kernel

private theorem r_202234 : RangeOk getRow 2051521 202234 202298 := by
  decide +kernel

private theorem r_202298 : RangeOk getRow 2051521 202298 202362 := by
  decide +kernel

private theorem r_202362 : RangeOk getRow 2051521 202362 202426 := by
  decide +kernel

private theorem r_202426 : RangeOk getRow 2051521 202426 202490 := by
  decide +kernel

private theorem r_202490 : RangeOk getRow 2051521 202490 202554 := by
  decide +kernel

private theorem r_202554 : RangeOk getRow 2051521 202554 202618 := by
  decide +kernel

private theorem r_202618 : RangeOk getRow 2051521 202618 202682 := by
  decide +kernel

private theorem r_202682 : RangeOk getRow 2051521 202682 202746 := by
  decide +kernel

private theorem r_202746 : RangeOk getRow 2051521 202746 202810 := by
  decide +kernel

private theorem r_202810 : RangeOk getRow 2051521 202810 202874 := by
  decide +kernel

private theorem r_202874 : RangeOk getRow 2051521 202874 202938 := by
  decide +kernel

private theorem r_202938 : RangeOk getRow 2051521 202938 203002 := by
  decide +kernel

private theorem r_203002 : RangeOk getRow 2051521 203002 203066 := by
  decide +kernel

private theorem r_203066 : RangeOk getRow 2051521 203066 203130 := by
  decide +kernel

private theorem r_203130 : RangeOk getRow 2051521 203130 203194 := by
  decide +kernel

private theorem r_203194 : RangeOk getRow 2051521 203194 203258 := by
  decide +kernel

private theorem r_203258 : RangeOk getRow 2051521 203258 203322 := by
  decide +kernel

private theorem r_203322 : RangeOk getRow 2051521 203322 203386 := by
  decide +kernel

private theorem r_203386 : RangeOk getRow 2051521 203386 203450 := by
  decide +kernel

private theorem r_203450 : RangeOk getRow 2051521 203450 203514 := by
  decide +kernel

private theorem r_203514 : RangeOk getRow 2051521 203514 203578 := by
  decide +kernel

private theorem r_203578 : RangeOk getRow 2051521 203578 203642 := by
  decide +kernel

private theorem r_203642 : RangeOk getRow 2051521 203642 203706 := by
  decide +kernel

private theorem r_203706 : RangeOk getRow 2051521 203706 203770 := by
  decide +kernel

private theorem r_203770 : RangeOk getRow 2051521 203770 203834 := by
  decide +kernel

private theorem s_202170 : RangeOk getRow 2051521 202106 202170 := r_202106
private theorem s_202234 : RangeOk getRow 2051521 202106 202234 :=
  s_202170.append (by norm_num) r_202170
private theorem s_202298 : RangeOk getRow 2051521 202106 202298 :=
  s_202234.append (by norm_num) r_202234
private theorem s_202362 : RangeOk getRow 2051521 202106 202362 :=
  s_202298.append (by norm_num) r_202298
private theorem s_202426 : RangeOk getRow 2051521 202106 202426 :=
  s_202362.append (by norm_num) r_202362
private theorem s_202490 : RangeOk getRow 2051521 202106 202490 :=
  s_202426.append (by norm_num) r_202426
private theorem s_202554 : RangeOk getRow 2051521 202106 202554 :=
  s_202490.append (by norm_num) r_202490
private theorem s_202618 : RangeOk getRow 2051521 202106 202618 :=
  s_202554.append (by norm_num) r_202554
private theorem s_202682 : RangeOk getRow 2051521 202106 202682 :=
  s_202618.append (by norm_num) r_202618
private theorem s_202746 : RangeOk getRow 2051521 202106 202746 :=
  s_202682.append (by norm_num) r_202682
private theorem s_202810 : RangeOk getRow 2051521 202106 202810 :=
  s_202746.append (by norm_num) r_202746
private theorem s_202874 : RangeOk getRow 2051521 202106 202874 :=
  s_202810.append (by norm_num) r_202810
private theorem s_202938 : RangeOk getRow 2051521 202106 202938 :=
  s_202874.append (by norm_num) r_202874
private theorem s_203002 : RangeOk getRow 2051521 202106 203002 :=
  s_202938.append (by norm_num) r_202938
private theorem s_203066 : RangeOk getRow 2051521 202106 203066 :=
  s_203002.append (by norm_num) r_203002
private theorem s_203130 : RangeOk getRow 2051521 202106 203130 :=
  s_203066.append (by norm_num) r_203066
private theorem s_203194 : RangeOk getRow 2051521 202106 203194 :=
  s_203130.append (by norm_num) r_203130
private theorem s_203258 : RangeOk getRow 2051521 202106 203258 :=
  s_203194.append (by norm_num) r_203194
private theorem s_203322 : RangeOk getRow 2051521 202106 203322 :=
  s_203258.append (by norm_num) r_203258
private theorem s_203386 : RangeOk getRow 2051521 202106 203386 :=
  s_203322.append (by norm_num) r_203322
private theorem s_203450 : RangeOk getRow 2051521 202106 203450 :=
  s_203386.append (by norm_num) r_203386
private theorem s_203514 : RangeOk getRow 2051521 202106 203514 :=
  s_203450.append (by norm_num) r_203450
private theorem s_203578 : RangeOk getRow 2051521 202106 203578 :=
  s_203514.append (by norm_num) r_203514
private theorem s_203642 : RangeOk getRow 2051521 202106 203642 :=
  s_203578.append (by norm_num) r_203578
private theorem s_203706 : RangeOk getRow 2051521 202106 203706 :=
  s_203642.append (by norm_num) r_203642
private theorem s_203770 : RangeOk getRow 2051521 202106 203770 :=
  s_203706.append (by norm_num) r_203706
private theorem s_203834 : RangeOk getRow 2051521 202106 203834 :=
  s_203770.append (by norm_num) r_203770

/-- Rows `[202106, 203834)` are valid. -/
theorem rangeOk_202106_203834 : RangeOk getRow 2051521 202106 203834 := s_203834

end Noperthedron.Solution
