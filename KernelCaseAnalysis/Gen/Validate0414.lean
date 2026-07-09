import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1002378, 1005158). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1002378 : RangeOk getRow 2051521 1002378 1002444 := by
  decide +kernel

private theorem r_1002444 : RangeOk getRow 2051521 1002444 1002512 := by
  decide +kernel

private theorem r_1002512 : RangeOk getRow 2051521 1002512 1002580 := by
  decide +kernel

private theorem r_1002580 : RangeOk getRow 2051521 1002580 1002649 := by
  decide +kernel

private theorem r_1002649 : RangeOk getRow 2051521 1002649 1002718 := by
  decide +kernel

private theorem r_1002718 : RangeOk getRow 2051521 1002718 1002789 := by
  decide +kernel

private theorem r_1002789 : RangeOk getRow 2051521 1002789 1002860 := by
  decide +kernel

private theorem r_1002860 : RangeOk getRow 2051521 1002860 1002933 := by
  decide +kernel

private theorem r_1002933 : RangeOk getRow 2051521 1002933 1003004 := by
  decide +kernel

private theorem r_1003004 : RangeOk getRow 2051521 1003004 1003076 := by
  decide +kernel

private theorem r_1003076 : RangeOk getRow 2051521 1003076 1003145 := by
  decide +kernel

private theorem r_1003145 : RangeOk getRow 2051521 1003145 1003214 := by
  decide +kernel

private theorem r_1003214 : RangeOk getRow 2051521 1003214 1003283 := by
  decide +kernel

private theorem r_1003283 : RangeOk getRow 2051521 1003283 1003350 := by
  decide +kernel

private theorem r_1003350 : RangeOk getRow 2051521 1003350 1003415 := by
  decide +kernel

private theorem r_1003415 : RangeOk getRow 2051521 1003415 1003481 := by
  decide +kernel

private theorem r_1003481 : RangeOk getRow 2051521 1003481 1003550 := by
  decide +kernel

private theorem r_1003550 : RangeOk getRow 2051521 1003550 1003619 := by
  decide +kernel

private theorem r_1003619 : RangeOk getRow 2051521 1003619 1003688 := by
  decide +kernel

private theorem r_1003688 : RangeOk getRow 2051521 1003688 1003760 := by
  decide +kernel

private theorem r_1003760 : RangeOk getRow 2051521 1003760 1003831 := by
  decide +kernel

private theorem r_1003831 : RangeOk getRow 2051521 1003831 1003903 := by
  decide +kernel

private theorem r_1003903 : RangeOk getRow 2051521 1003903 1003975 := by
  decide +kernel

private theorem r_1003975 : RangeOk getRow 2051521 1003975 1004046 := by
  decide +kernel

private theorem r_1004046 : RangeOk getRow 2051521 1004046 1004117 := by
  decide +kernel

private theorem r_1004117 : RangeOk getRow 2051521 1004117 1004186 := by
  decide +kernel

private theorem r_1004186 : RangeOk getRow 2051521 1004186 1004255 := by
  decide +kernel

private theorem r_1004255 : RangeOk getRow 2051521 1004255 1004323 := by
  decide +kernel

private theorem r_1004323 : RangeOk getRow 2051521 1004323 1004391 := by
  decide +kernel

private theorem r_1004391 : RangeOk getRow 2051521 1004391 1004455 := by
  decide +kernel

private theorem r_1004455 : RangeOk getRow 2051521 1004455 1004524 := by
  decide +kernel

private theorem r_1004524 : RangeOk getRow 2051521 1004524 1004593 := by
  decide +kernel

private theorem r_1004593 : RangeOk getRow 2051521 1004593 1004662 := by
  decide +kernel

private theorem r_1004662 : RangeOk getRow 2051521 1004662 1004734 := by
  decide +kernel

private theorem r_1004734 : RangeOk getRow 2051521 1004734 1004805 := by
  decide +kernel

private theorem r_1004805 : RangeOk getRow 2051521 1004805 1004877 := by
  decide +kernel

private theorem r_1004877 : RangeOk getRow 2051521 1004877 1004949 := by
  decide +kernel

private theorem r_1004949 : RangeOk getRow 2051521 1004949 1005019 := by
  decide +kernel

private theorem r_1005019 : RangeOk getRow 2051521 1005019 1005090 := by
  decide +kernel

private theorem r_1005090 : RangeOk getRow 2051521 1005090 1005158 := by
  decide +kernel

private theorem s_1002444 : RangeOk getRow 2051521 1002378 1002444 := r_1002378
private theorem s_1002512 : RangeOk getRow 2051521 1002378 1002512 :=
  s_1002444.append (by norm_num) r_1002444
private theorem s_1002580 : RangeOk getRow 2051521 1002378 1002580 :=
  s_1002512.append (by norm_num) r_1002512
private theorem s_1002649 : RangeOk getRow 2051521 1002378 1002649 :=
  s_1002580.append (by norm_num) r_1002580
private theorem s_1002718 : RangeOk getRow 2051521 1002378 1002718 :=
  s_1002649.append (by norm_num) r_1002649
private theorem s_1002789 : RangeOk getRow 2051521 1002378 1002789 :=
  s_1002718.append (by norm_num) r_1002718
private theorem s_1002860 : RangeOk getRow 2051521 1002378 1002860 :=
  s_1002789.append (by norm_num) r_1002789
private theorem s_1002933 : RangeOk getRow 2051521 1002378 1002933 :=
  s_1002860.append (by norm_num) r_1002860
private theorem s_1003004 : RangeOk getRow 2051521 1002378 1003004 :=
  s_1002933.append (by norm_num) r_1002933
private theorem s_1003076 : RangeOk getRow 2051521 1002378 1003076 :=
  s_1003004.append (by norm_num) r_1003004
private theorem s_1003145 : RangeOk getRow 2051521 1002378 1003145 :=
  s_1003076.append (by norm_num) r_1003076
private theorem s_1003214 : RangeOk getRow 2051521 1002378 1003214 :=
  s_1003145.append (by norm_num) r_1003145
private theorem s_1003283 : RangeOk getRow 2051521 1002378 1003283 :=
  s_1003214.append (by norm_num) r_1003214
private theorem s_1003350 : RangeOk getRow 2051521 1002378 1003350 :=
  s_1003283.append (by norm_num) r_1003283
private theorem s_1003415 : RangeOk getRow 2051521 1002378 1003415 :=
  s_1003350.append (by norm_num) r_1003350
private theorem s_1003481 : RangeOk getRow 2051521 1002378 1003481 :=
  s_1003415.append (by norm_num) r_1003415
private theorem s_1003550 : RangeOk getRow 2051521 1002378 1003550 :=
  s_1003481.append (by norm_num) r_1003481
private theorem s_1003619 : RangeOk getRow 2051521 1002378 1003619 :=
  s_1003550.append (by norm_num) r_1003550
private theorem s_1003688 : RangeOk getRow 2051521 1002378 1003688 :=
  s_1003619.append (by norm_num) r_1003619
private theorem s_1003760 : RangeOk getRow 2051521 1002378 1003760 :=
  s_1003688.append (by norm_num) r_1003688
private theorem s_1003831 : RangeOk getRow 2051521 1002378 1003831 :=
  s_1003760.append (by norm_num) r_1003760
private theorem s_1003903 : RangeOk getRow 2051521 1002378 1003903 :=
  s_1003831.append (by norm_num) r_1003831
private theorem s_1003975 : RangeOk getRow 2051521 1002378 1003975 :=
  s_1003903.append (by norm_num) r_1003903
private theorem s_1004046 : RangeOk getRow 2051521 1002378 1004046 :=
  s_1003975.append (by norm_num) r_1003975
private theorem s_1004117 : RangeOk getRow 2051521 1002378 1004117 :=
  s_1004046.append (by norm_num) r_1004046
private theorem s_1004186 : RangeOk getRow 2051521 1002378 1004186 :=
  s_1004117.append (by norm_num) r_1004117
private theorem s_1004255 : RangeOk getRow 2051521 1002378 1004255 :=
  s_1004186.append (by norm_num) r_1004186
private theorem s_1004323 : RangeOk getRow 2051521 1002378 1004323 :=
  s_1004255.append (by norm_num) r_1004255
private theorem s_1004391 : RangeOk getRow 2051521 1002378 1004391 :=
  s_1004323.append (by norm_num) r_1004323
private theorem s_1004455 : RangeOk getRow 2051521 1002378 1004455 :=
  s_1004391.append (by norm_num) r_1004391
private theorem s_1004524 : RangeOk getRow 2051521 1002378 1004524 :=
  s_1004455.append (by norm_num) r_1004455
private theorem s_1004593 : RangeOk getRow 2051521 1002378 1004593 :=
  s_1004524.append (by norm_num) r_1004524
private theorem s_1004662 : RangeOk getRow 2051521 1002378 1004662 :=
  s_1004593.append (by norm_num) r_1004593
private theorem s_1004734 : RangeOk getRow 2051521 1002378 1004734 :=
  s_1004662.append (by norm_num) r_1004662
private theorem s_1004805 : RangeOk getRow 2051521 1002378 1004805 :=
  s_1004734.append (by norm_num) r_1004734
private theorem s_1004877 : RangeOk getRow 2051521 1002378 1004877 :=
  s_1004805.append (by norm_num) r_1004805
private theorem s_1004949 : RangeOk getRow 2051521 1002378 1004949 :=
  s_1004877.append (by norm_num) r_1004877
private theorem s_1005019 : RangeOk getRow 2051521 1002378 1005019 :=
  s_1004949.append (by norm_num) r_1004949
private theorem s_1005090 : RangeOk getRow 2051521 1002378 1005090 :=
  s_1005019.append (by norm_num) r_1005019
private theorem s_1005158 : RangeOk getRow 2051521 1002378 1005158 :=
  s_1005090.append (by norm_num) r_1005090

/-- Rows `[1002378, 1005158)` are valid. -/
theorem rangeOk_1002378_1005158 : RangeOk getRow 2051521 1002378 1005158 := s_1005158

end Noperthedron.Solution
