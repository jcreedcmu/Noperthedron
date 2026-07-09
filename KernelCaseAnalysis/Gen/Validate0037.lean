import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[81262, 82985). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_81262 : RangeOk getRow 2051521 81262 81326 := by
  decide +kernel

private theorem r_81326 : RangeOk getRow 2051521 81326 81390 := by
  decide +kernel

private theorem r_81390 : RangeOk getRow 2051521 81390 81454 := by
  decide +kernel

private theorem r_81454 : RangeOk getRow 2051521 81454 81518 := by
  decide +kernel

private theorem r_81518 : RangeOk getRow 2051521 81518 81582 := by
  decide +kernel

private theorem r_81582 : RangeOk getRow 2051521 81582 81646 := by
  decide +kernel

private theorem r_81646 : RangeOk getRow 2051521 81646 81710 := by
  decide +kernel

private theorem r_81710 : RangeOk getRow 2051521 81710 81774 := by
  decide +kernel

private theorem r_81774 : RangeOk getRow 2051521 81774 81838 := by
  decide +kernel

private theorem r_81838 : RangeOk getRow 2051521 81838 81902 := by
  decide +kernel

private theorem r_81902 : RangeOk getRow 2051521 81902 81966 := by
  decide +kernel

private theorem r_81966 : RangeOk getRow 2051521 81966 82025 := by
  decide +kernel

private theorem r_82025 : RangeOk getRow 2051521 82025 82089 := by
  decide +kernel

private theorem r_82089 : RangeOk getRow 2051521 82089 82153 := by
  decide +kernel

private theorem r_82153 : RangeOk getRow 2051521 82153 82217 := by
  decide +kernel

private theorem r_82217 : RangeOk getRow 2051521 82217 82281 := by
  decide +kernel

private theorem r_82281 : RangeOk getRow 2051521 82281 82345 := by
  decide +kernel

private theorem r_82345 : RangeOk getRow 2051521 82345 82409 := by
  decide +kernel

private theorem r_82409 : RangeOk getRow 2051521 82409 82473 := by
  decide +kernel

private theorem r_82473 : RangeOk getRow 2051521 82473 82537 := by
  decide +kernel

private theorem r_82537 : RangeOk getRow 2051521 82537 82601 := by
  decide +kernel

private theorem r_82601 : RangeOk getRow 2051521 82601 82665 := by
  decide +kernel

private theorem r_82665 : RangeOk getRow 2051521 82665 82729 := by
  decide +kernel

private theorem r_82729 : RangeOk getRow 2051521 82729 82793 := by
  decide +kernel

private theorem r_82793 : RangeOk getRow 2051521 82793 82857 := by
  decide +kernel

private theorem r_82857 : RangeOk getRow 2051521 82857 82921 := by
  decide +kernel

private theorem r_82921 : RangeOk getRow 2051521 82921 82985 := by
  decide +kernel

private theorem s_81326 : RangeOk getRow 2051521 81262 81326 := r_81262
private theorem s_81390 : RangeOk getRow 2051521 81262 81390 :=
  s_81326.append (by norm_num) r_81326
private theorem s_81454 : RangeOk getRow 2051521 81262 81454 :=
  s_81390.append (by norm_num) r_81390
private theorem s_81518 : RangeOk getRow 2051521 81262 81518 :=
  s_81454.append (by norm_num) r_81454
private theorem s_81582 : RangeOk getRow 2051521 81262 81582 :=
  s_81518.append (by norm_num) r_81518
private theorem s_81646 : RangeOk getRow 2051521 81262 81646 :=
  s_81582.append (by norm_num) r_81582
private theorem s_81710 : RangeOk getRow 2051521 81262 81710 :=
  s_81646.append (by norm_num) r_81646
private theorem s_81774 : RangeOk getRow 2051521 81262 81774 :=
  s_81710.append (by norm_num) r_81710
private theorem s_81838 : RangeOk getRow 2051521 81262 81838 :=
  s_81774.append (by norm_num) r_81774
private theorem s_81902 : RangeOk getRow 2051521 81262 81902 :=
  s_81838.append (by norm_num) r_81838
private theorem s_81966 : RangeOk getRow 2051521 81262 81966 :=
  s_81902.append (by norm_num) r_81902
private theorem s_82025 : RangeOk getRow 2051521 81262 82025 :=
  s_81966.append (by norm_num) r_81966
private theorem s_82089 : RangeOk getRow 2051521 81262 82089 :=
  s_82025.append (by norm_num) r_82025
private theorem s_82153 : RangeOk getRow 2051521 81262 82153 :=
  s_82089.append (by norm_num) r_82089
private theorem s_82217 : RangeOk getRow 2051521 81262 82217 :=
  s_82153.append (by norm_num) r_82153
private theorem s_82281 : RangeOk getRow 2051521 81262 82281 :=
  s_82217.append (by norm_num) r_82217
private theorem s_82345 : RangeOk getRow 2051521 81262 82345 :=
  s_82281.append (by norm_num) r_82281
private theorem s_82409 : RangeOk getRow 2051521 81262 82409 :=
  s_82345.append (by norm_num) r_82345
private theorem s_82473 : RangeOk getRow 2051521 81262 82473 :=
  s_82409.append (by norm_num) r_82409
private theorem s_82537 : RangeOk getRow 2051521 81262 82537 :=
  s_82473.append (by norm_num) r_82473
private theorem s_82601 : RangeOk getRow 2051521 81262 82601 :=
  s_82537.append (by norm_num) r_82537
private theorem s_82665 : RangeOk getRow 2051521 81262 82665 :=
  s_82601.append (by norm_num) r_82601
private theorem s_82729 : RangeOk getRow 2051521 81262 82729 :=
  s_82665.append (by norm_num) r_82665
private theorem s_82793 : RangeOk getRow 2051521 81262 82793 :=
  s_82729.append (by norm_num) r_82729
private theorem s_82857 : RangeOk getRow 2051521 81262 82857 :=
  s_82793.append (by norm_num) r_82793
private theorem s_82921 : RangeOk getRow 2051521 81262 82921 :=
  s_82857.append (by norm_num) r_82857
private theorem s_82985 : RangeOk getRow 2051521 81262 82985 :=
  s_82921.append (by norm_num) r_82921

/-- Rows `[81262, 82985)` are valid. -/
theorem rangeOk_81262_82985 : RangeOk getRow 2051521 81262 82985 := s_82985

end Noperthedron.Solution
