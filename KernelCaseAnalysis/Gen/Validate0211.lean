import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[509931, 512391). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_509931 : RangeOk getRow 2051521 509931 510000 := by
  decide +kernel

private theorem r_510000 : RangeOk getRow 2051521 510000 510068 := by
  decide +kernel

private theorem r_510068 : RangeOk getRow 2051521 510068 510137 := by
  decide +kernel

private theorem r_510137 : RangeOk getRow 2051521 510137 510208 := by
  decide +kernel

private theorem r_510208 : RangeOk getRow 2051521 510208 510284 := by
  decide +kernel

private theorem r_510284 : RangeOk getRow 2051521 510284 510358 := by
  decide +kernel

private theorem r_510358 : RangeOk getRow 2051521 510358 510432 := by
  decide +kernel

private theorem r_510432 : RangeOk getRow 2051521 510432 510505 := by
  decide +kernel

private theorem r_510505 : RangeOk getRow 2051521 510505 510577 := by
  decide +kernel

private theorem r_510577 : RangeOk getRow 2051521 510577 510648 := by
  decide +kernel

private theorem r_510648 : RangeOk getRow 2051521 510648 510719 := by
  decide +kernel

private theorem r_510719 : RangeOk getRow 2051521 510719 510790 := by
  decide +kernel

private theorem r_510790 : RangeOk getRow 2051521 510790 510859 := by
  decide +kernel

private theorem r_510859 : RangeOk getRow 2051521 510859 510925 := by
  decide +kernel

private theorem r_510925 : RangeOk getRow 2051521 510925 510993 := by
  decide +kernel

private theorem r_510993 : RangeOk getRow 2051521 510993 511061 := by
  decide +kernel

private theorem r_511061 : RangeOk getRow 2051521 511061 511127 := by
  decide +kernel

private theorem r_511127 : RangeOk getRow 2051521 511127 511193 := by
  decide +kernel

private theorem r_511193 : RangeOk getRow 2051521 511193 511260 := by
  decide +kernel

private theorem r_511260 : RangeOk getRow 2051521 511260 511328 := by
  decide +kernel

private theorem r_511328 : RangeOk getRow 2051521 511328 511394 := by
  decide +kernel

private theorem r_511394 : RangeOk getRow 2051521 511394 511460 := by
  decide +kernel

private theorem r_511460 : RangeOk getRow 2051521 511460 511526 := by
  decide +kernel

private theorem r_511526 : RangeOk getRow 2051521 511526 511593 := by
  decide +kernel

private theorem r_511593 : RangeOk getRow 2051521 511593 511659 := by
  decide +kernel

private theorem r_511659 : RangeOk getRow 2051521 511659 511724 := by
  decide +kernel

private theorem r_511724 : RangeOk getRow 2051521 511724 511791 := by
  decide +kernel

private theorem r_511791 : RangeOk getRow 2051521 511791 511860 := by
  decide +kernel

private theorem r_511860 : RangeOk getRow 2051521 511860 511926 := by
  decide +kernel

private theorem r_511926 : RangeOk getRow 2051521 511926 511992 := by
  decide +kernel

private theorem r_511992 : RangeOk getRow 2051521 511992 512057 := by
  decide +kernel

private theorem r_512057 : RangeOk getRow 2051521 512057 512124 := by
  decide +kernel

private theorem r_512124 : RangeOk getRow 2051521 512124 512190 := by
  decide +kernel

private theorem r_512190 : RangeOk getRow 2051521 512190 512257 := by
  decide +kernel

private theorem r_512257 : RangeOk getRow 2051521 512257 512324 := by
  decide +kernel

private theorem r_512324 : RangeOk getRow 2051521 512324 512391 := by
  decide +kernel

private theorem s_510000 : RangeOk getRow 2051521 509931 510000 := r_509931
private theorem s_510068 : RangeOk getRow 2051521 509931 510068 :=
  s_510000.append (by norm_num) r_510000
private theorem s_510137 : RangeOk getRow 2051521 509931 510137 :=
  s_510068.append (by norm_num) r_510068
private theorem s_510208 : RangeOk getRow 2051521 509931 510208 :=
  s_510137.append (by norm_num) r_510137
private theorem s_510284 : RangeOk getRow 2051521 509931 510284 :=
  s_510208.append (by norm_num) r_510208
private theorem s_510358 : RangeOk getRow 2051521 509931 510358 :=
  s_510284.append (by norm_num) r_510284
private theorem s_510432 : RangeOk getRow 2051521 509931 510432 :=
  s_510358.append (by norm_num) r_510358
private theorem s_510505 : RangeOk getRow 2051521 509931 510505 :=
  s_510432.append (by norm_num) r_510432
private theorem s_510577 : RangeOk getRow 2051521 509931 510577 :=
  s_510505.append (by norm_num) r_510505
private theorem s_510648 : RangeOk getRow 2051521 509931 510648 :=
  s_510577.append (by norm_num) r_510577
private theorem s_510719 : RangeOk getRow 2051521 509931 510719 :=
  s_510648.append (by norm_num) r_510648
private theorem s_510790 : RangeOk getRow 2051521 509931 510790 :=
  s_510719.append (by norm_num) r_510719
private theorem s_510859 : RangeOk getRow 2051521 509931 510859 :=
  s_510790.append (by norm_num) r_510790
private theorem s_510925 : RangeOk getRow 2051521 509931 510925 :=
  s_510859.append (by norm_num) r_510859
private theorem s_510993 : RangeOk getRow 2051521 509931 510993 :=
  s_510925.append (by norm_num) r_510925
private theorem s_511061 : RangeOk getRow 2051521 509931 511061 :=
  s_510993.append (by norm_num) r_510993
private theorem s_511127 : RangeOk getRow 2051521 509931 511127 :=
  s_511061.append (by norm_num) r_511061
private theorem s_511193 : RangeOk getRow 2051521 509931 511193 :=
  s_511127.append (by norm_num) r_511127
private theorem s_511260 : RangeOk getRow 2051521 509931 511260 :=
  s_511193.append (by norm_num) r_511193
private theorem s_511328 : RangeOk getRow 2051521 509931 511328 :=
  s_511260.append (by norm_num) r_511260
private theorem s_511394 : RangeOk getRow 2051521 509931 511394 :=
  s_511328.append (by norm_num) r_511328
private theorem s_511460 : RangeOk getRow 2051521 509931 511460 :=
  s_511394.append (by norm_num) r_511394
private theorem s_511526 : RangeOk getRow 2051521 509931 511526 :=
  s_511460.append (by norm_num) r_511460
private theorem s_511593 : RangeOk getRow 2051521 509931 511593 :=
  s_511526.append (by norm_num) r_511526
private theorem s_511659 : RangeOk getRow 2051521 509931 511659 :=
  s_511593.append (by norm_num) r_511593
private theorem s_511724 : RangeOk getRow 2051521 509931 511724 :=
  s_511659.append (by norm_num) r_511659
private theorem s_511791 : RangeOk getRow 2051521 509931 511791 :=
  s_511724.append (by norm_num) r_511724
private theorem s_511860 : RangeOk getRow 2051521 509931 511860 :=
  s_511791.append (by norm_num) r_511791
private theorem s_511926 : RangeOk getRow 2051521 509931 511926 :=
  s_511860.append (by norm_num) r_511860
private theorem s_511992 : RangeOk getRow 2051521 509931 511992 :=
  s_511926.append (by norm_num) r_511926
private theorem s_512057 : RangeOk getRow 2051521 509931 512057 :=
  s_511992.append (by norm_num) r_511992
private theorem s_512124 : RangeOk getRow 2051521 509931 512124 :=
  s_512057.append (by norm_num) r_512057
private theorem s_512190 : RangeOk getRow 2051521 509931 512190 :=
  s_512124.append (by norm_num) r_512124
private theorem s_512257 : RangeOk getRow 2051521 509931 512257 :=
  s_512190.append (by norm_num) r_512190
private theorem s_512324 : RangeOk getRow 2051521 509931 512324 :=
  s_512257.append (by norm_num) r_512257
private theorem s_512391 : RangeOk getRow 2051521 509931 512391 :=
  s_512324.append (by norm_num) r_512324

/-- Rows `[509931, 512391)` are valid. -/
theorem rangeOk_509931_512391 : RangeOk getRow 2051521 509931 512391 := s_512391

end Noperthedron.Solution
