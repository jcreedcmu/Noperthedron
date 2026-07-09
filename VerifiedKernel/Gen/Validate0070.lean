import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[151084, 152808). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_151084 : RangeOk getRow 2051521 151084 151148 := by
  decide +kernel

private theorem r_151148 : RangeOk getRow 2051521 151148 151212 := by
  decide +kernel

private theorem r_151212 : RangeOk getRow 2051521 151212 151272 := by
  decide +kernel

private theorem r_151272 : RangeOk getRow 2051521 151272 151336 := by
  decide +kernel

private theorem r_151336 : RangeOk getRow 2051521 151336 151400 := by
  decide +kernel

private theorem r_151400 : RangeOk getRow 2051521 151400 151464 := by
  decide +kernel

private theorem r_151464 : RangeOk getRow 2051521 151464 151528 := by
  decide +kernel

private theorem r_151528 : RangeOk getRow 2051521 151528 151592 := by
  decide +kernel

private theorem r_151592 : RangeOk getRow 2051521 151592 151656 := by
  decide +kernel

private theorem r_151656 : RangeOk getRow 2051521 151656 151720 := by
  decide +kernel

private theorem r_151720 : RangeOk getRow 2051521 151720 151784 := by
  decide +kernel

private theorem r_151784 : RangeOk getRow 2051521 151784 151848 := by
  decide +kernel

private theorem r_151848 : RangeOk getRow 2051521 151848 151912 := by
  decide +kernel

private theorem r_151912 : RangeOk getRow 2051521 151912 151976 := by
  decide +kernel

private theorem r_151976 : RangeOk getRow 2051521 151976 152040 := by
  decide +kernel

private theorem r_152040 : RangeOk getRow 2051521 152040 152104 := by
  decide +kernel

private theorem r_152104 : RangeOk getRow 2051521 152104 152168 := by
  decide +kernel

private theorem r_152168 : RangeOk getRow 2051521 152168 152232 := by
  decide +kernel

private theorem r_152232 : RangeOk getRow 2051521 152232 152296 := by
  decide +kernel

private theorem r_152296 : RangeOk getRow 2051521 152296 152360 := by
  decide +kernel

private theorem r_152360 : RangeOk getRow 2051521 152360 152424 := by
  decide +kernel

private theorem r_152424 : RangeOk getRow 2051521 152424 152488 := by
  decide +kernel

private theorem r_152488 : RangeOk getRow 2051521 152488 152552 := by
  decide +kernel

private theorem r_152552 : RangeOk getRow 2051521 152552 152616 := by
  decide +kernel

private theorem r_152616 : RangeOk getRow 2051521 152616 152680 := by
  decide +kernel

private theorem r_152680 : RangeOk getRow 2051521 152680 152744 := by
  decide +kernel

private theorem r_152744 : RangeOk getRow 2051521 152744 152808 := by
  decide +kernel

private theorem s_151148 : RangeOk getRow 2051521 151084 151148 := r_151084
private theorem s_151212 : RangeOk getRow 2051521 151084 151212 :=
  s_151148.append (by norm_num) r_151148
private theorem s_151272 : RangeOk getRow 2051521 151084 151272 :=
  s_151212.append (by norm_num) r_151212
private theorem s_151336 : RangeOk getRow 2051521 151084 151336 :=
  s_151272.append (by norm_num) r_151272
private theorem s_151400 : RangeOk getRow 2051521 151084 151400 :=
  s_151336.append (by norm_num) r_151336
private theorem s_151464 : RangeOk getRow 2051521 151084 151464 :=
  s_151400.append (by norm_num) r_151400
private theorem s_151528 : RangeOk getRow 2051521 151084 151528 :=
  s_151464.append (by norm_num) r_151464
private theorem s_151592 : RangeOk getRow 2051521 151084 151592 :=
  s_151528.append (by norm_num) r_151528
private theorem s_151656 : RangeOk getRow 2051521 151084 151656 :=
  s_151592.append (by norm_num) r_151592
private theorem s_151720 : RangeOk getRow 2051521 151084 151720 :=
  s_151656.append (by norm_num) r_151656
private theorem s_151784 : RangeOk getRow 2051521 151084 151784 :=
  s_151720.append (by norm_num) r_151720
private theorem s_151848 : RangeOk getRow 2051521 151084 151848 :=
  s_151784.append (by norm_num) r_151784
private theorem s_151912 : RangeOk getRow 2051521 151084 151912 :=
  s_151848.append (by norm_num) r_151848
private theorem s_151976 : RangeOk getRow 2051521 151084 151976 :=
  s_151912.append (by norm_num) r_151912
private theorem s_152040 : RangeOk getRow 2051521 151084 152040 :=
  s_151976.append (by norm_num) r_151976
private theorem s_152104 : RangeOk getRow 2051521 151084 152104 :=
  s_152040.append (by norm_num) r_152040
private theorem s_152168 : RangeOk getRow 2051521 151084 152168 :=
  s_152104.append (by norm_num) r_152104
private theorem s_152232 : RangeOk getRow 2051521 151084 152232 :=
  s_152168.append (by norm_num) r_152168
private theorem s_152296 : RangeOk getRow 2051521 151084 152296 :=
  s_152232.append (by norm_num) r_152232
private theorem s_152360 : RangeOk getRow 2051521 151084 152360 :=
  s_152296.append (by norm_num) r_152296
private theorem s_152424 : RangeOk getRow 2051521 151084 152424 :=
  s_152360.append (by norm_num) r_152360
private theorem s_152488 : RangeOk getRow 2051521 151084 152488 :=
  s_152424.append (by norm_num) r_152424
private theorem s_152552 : RangeOk getRow 2051521 151084 152552 :=
  s_152488.append (by norm_num) r_152488
private theorem s_152616 : RangeOk getRow 2051521 151084 152616 :=
  s_152552.append (by norm_num) r_152552
private theorem s_152680 : RangeOk getRow 2051521 151084 152680 :=
  s_152616.append (by norm_num) r_152616
private theorem s_152744 : RangeOk getRow 2051521 151084 152744 :=
  s_152680.append (by norm_num) r_152680
private theorem s_152808 : RangeOk getRow 2051521 151084 152808 :=
  s_152744.append (by norm_num) r_152744

/-- Rows `[151084, 152808)` are valid. -/
theorem rangeOk_151084_152808 : RangeOk getRow 2051521 151084 152808 := s_152808

end Noperthedron.Solution
