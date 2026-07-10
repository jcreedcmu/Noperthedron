import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[951099, 953628). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_951099 : RangeOk getRow 2051521 951099 951165 := by
  decide +kernel

private theorem r_951165 : RangeOk getRow 2051521 951165 951233 := by
  decide +kernel

private theorem r_951233 : RangeOk getRow 2051521 951233 951305 := by
  decide +kernel

private theorem r_951305 : RangeOk getRow 2051521 951305 951373 := by
  decide +kernel

private theorem r_951373 : RangeOk getRow 2051521 951373 951444 := by
  decide +kernel

private theorem r_951444 : RangeOk getRow 2051521 951444 951517 := by
  decide +kernel

private theorem r_951517 : RangeOk getRow 2051521 951517 951587 := by
  decide +kernel

private theorem r_951587 : RangeOk getRow 2051521 951587 951657 := by
  decide +kernel

private theorem r_951657 : RangeOk getRow 2051521 951657 951724 := by
  decide +kernel

private theorem r_951724 : RangeOk getRow 2051521 951724 951792 := by
  decide +kernel

private theorem r_951792 : RangeOk getRow 2051521 951792 951860 := by
  decide +kernel

private theorem r_951860 : RangeOk getRow 2051521 951860 951929 := by
  decide +kernel

private theorem r_951929 : RangeOk getRow 2051521 951929 951997 := by
  decide +kernel

private theorem r_951997 : RangeOk getRow 2051521 951997 952065 := by
  decide +kernel

private theorem r_952065 : RangeOk getRow 2051521 952065 952131 := by
  decide +kernel

private theorem r_952131 : RangeOk getRow 2051521 952131 952199 := by
  decide +kernel

private theorem r_952199 : RangeOk getRow 2051521 952199 952269 := by
  decide +kernel

private theorem r_952269 : RangeOk getRow 2051521 952269 952341 := by
  decide +kernel

private theorem r_952341 : RangeOk getRow 2051521 952341 952411 := by
  decide +kernel

private theorem r_952411 : RangeOk getRow 2051521 952411 952478 := by
  decide +kernel

private theorem r_952478 : RangeOk getRow 2051521 952478 952543 := by
  decide +kernel

private theorem r_952543 : RangeOk getRow 2051521 952543 952611 := by
  decide +kernel

private theorem r_952611 : RangeOk getRow 2051521 952611 952678 := by
  decide +kernel

private theorem r_952678 : RangeOk getRow 2051521 952678 952744 := by
  decide +kernel

private theorem r_952744 : RangeOk getRow 2051521 952744 952812 := by
  decide +kernel

private theorem r_952812 : RangeOk getRow 2051521 952812 952880 := by
  decide +kernel

private theorem r_952880 : RangeOk getRow 2051521 952880 952949 := by
  decide +kernel

private theorem r_952949 : RangeOk getRow 2051521 952949 953015 := by
  decide +kernel

private theorem r_953015 : RangeOk getRow 2051521 953015 953083 := by
  decide +kernel

private theorem r_953083 : RangeOk getRow 2051521 953083 953151 := by
  decide +kernel

private theorem r_953151 : RangeOk getRow 2051521 953151 953223 := by
  decide +kernel

private theorem r_953223 : RangeOk getRow 2051521 953223 953291 := by
  decide +kernel

private theorem r_953291 : RangeOk getRow 2051521 953291 953357 := by
  decide +kernel

private theorem r_953357 : RangeOk getRow 2051521 953357 953424 := by
  decide +kernel

private theorem r_953424 : RangeOk getRow 2051521 953424 953490 := by
  decide +kernel

private theorem r_953490 : RangeOk getRow 2051521 953490 953559 := by
  decide +kernel

private theorem r_953559 : RangeOk getRow 2051521 953559 953628 := by
  decide +kernel

private theorem s_951165 : RangeOk getRow 2051521 951099 951165 := r_951099
private theorem s_951233 : RangeOk getRow 2051521 951099 951233 :=
  s_951165.append (by norm_num) r_951165
private theorem s_951305 : RangeOk getRow 2051521 951099 951305 :=
  s_951233.append (by norm_num) r_951233
private theorem s_951373 : RangeOk getRow 2051521 951099 951373 :=
  s_951305.append (by norm_num) r_951305
private theorem s_951444 : RangeOk getRow 2051521 951099 951444 :=
  s_951373.append (by norm_num) r_951373
private theorem s_951517 : RangeOk getRow 2051521 951099 951517 :=
  s_951444.append (by norm_num) r_951444
private theorem s_951587 : RangeOk getRow 2051521 951099 951587 :=
  s_951517.append (by norm_num) r_951517
private theorem s_951657 : RangeOk getRow 2051521 951099 951657 :=
  s_951587.append (by norm_num) r_951587
private theorem s_951724 : RangeOk getRow 2051521 951099 951724 :=
  s_951657.append (by norm_num) r_951657
private theorem s_951792 : RangeOk getRow 2051521 951099 951792 :=
  s_951724.append (by norm_num) r_951724
private theorem s_951860 : RangeOk getRow 2051521 951099 951860 :=
  s_951792.append (by norm_num) r_951792
private theorem s_951929 : RangeOk getRow 2051521 951099 951929 :=
  s_951860.append (by norm_num) r_951860
private theorem s_951997 : RangeOk getRow 2051521 951099 951997 :=
  s_951929.append (by norm_num) r_951929
private theorem s_952065 : RangeOk getRow 2051521 951099 952065 :=
  s_951997.append (by norm_num) r_951997
private theorem s_952131 : RangeOk getRow 2051521 951099 952131 :=
  s_952065.append (by norm_num) r_952065
private theorem s_952199 : RangeOk getRow 2051521 951099 952199 :=
  s_952131.append (by norm_num) r_952131
private theorem s_952269 : RangeOk getRow 2051521 951099 952269 :=
  s_952199.append (by norm_num) r_952199
private theorem s_952341 : RangeOk getRow 2051521 951099 952341 :=
  s_952269.append (by norm_num) r_952269
private theorem s_952411 : RangeOk getRow 2051521 951099 952411 :=
  s_952341.append (by norm_num) r_952341
private theorem s_952478 : RangeOk getRow 2051521 951099 952478 :=
  s_952411.append (by norm_num) r_952411
private theorem s_952543 : RangeOk getRow 2051521 951099 952543 :=
  s_952478.append (by norm_num) r_952478
private theorem s_952611 : RangeOk getRow 2051521 951099 952611 :=
  s_952543.append (by norm_num) r_952543
private theorem s_952678 : RangeOk getRow 2051521 951099 952678 :=
  s_952611.append (by norm_num) r_952611
private theorem s_952744 : RangeOk getRow 2051521 951099 952744 :=
  s_952678.append (by norm_num) r_952678
private theorem s_952812 : RangeOk getRow 2051521 951099 952812 :=
  s_952744.append (by norm_num) r_952744
private theorem s_952880 : RangeOk getRow 2051521 951099 952880 :=
  s_952812.append (by norm_num) r_952812
private theorem s_952949 : RangeOk getRow 2051521 951099 952949 :=
  s_952880.append (by norm_num) r_952880
private theorem s_953015 : RangeOk getRow 2051521 951099 953015 :=
  s_952949.append (by norm_num) r_952949
private theorem s_953083 : RangeOk getRow 2051521 951099 953083 :=
  s_953015.append (by norm_num) r_953015
private theorem s_953151 : RangeOk getRow 2051521 951099 953151 :=
  s_953083.append (by norm_num) r_953083
private theorem s_953223 : RangeOk getRow 2051521 951099 953223 :=
  s_953151.append (by norm_num) r_953151
private theorem s_953291 : RangeOk getRow 2051521 951099 953291 :=
  s_953223.append (by norm_num) r_953223
private theorem s_953357 : RangeOk getRow 2051521 951099 953357 :=
  s_953291.append (by norm_num) r_953291
private theorem s_953424 : RangeOk getRow 2051521 951099 953424 :=
  s_953357.append (by norm_num) r_953357
private theorem s_953490 : RangeOk getRow 2051521 951099 953490 :=
  s_953424.append (by norm_num) r_953424
private theorem s_953559 : RangeOk getRow 2051521 951099 953559 :=
  s_953490.append (by norm_num) r_953490
private theorem s_953628 : RangeOk getRow 2051521 951099 953628 :=
  s_953559.append (by norm_num) r_953559

/-- Rows `[951099, 953628)` are valid. -/
theorem rangeOk_951099_953628 : RangeOk getRow 2051521 951099 953628 := s_953628

end Noperthedron.Solution
