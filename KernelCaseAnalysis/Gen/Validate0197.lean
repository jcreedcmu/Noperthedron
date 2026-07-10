import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[475453, 477748). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_475453 : RangeOk getRow 2051521 475453 475520 := by
  decide +kernel

private theorem r_475520 : RangeOk getRow 2051521 475520 475585 := by
  decide +kernel

private theorem r_475585 : RangeOk getRow 2051521 475585 475652 := by
  decide +kernel

private theorem r_475652 : RangeOk getRow 2051521 475652 475721 := by
  decide +kernel

private theorem r_475721 : RangeOk getRow 2051521 475721 475791 := by
  decide +kernel

private theorem r_475791 : RangeOk getRow 2051521 475791 475858 := by
  decide +kernel

private theorem r_475858 : RangeOk getRow 2051521 475858 475925 := by
  decide +kernel

private theorem r_475925 : RangeOk getRow 2051521 475925 475991 := by
  decide +kernel

private theorem r_475991 : RangeOk getRow 2051521 475991 476059 := by
  decide +kernel

private theorem r_476059 : RangeOk getRow 2051521 476059 476128 := by
  decide +kernel

private theorem r_476128 : RangeOk getRow 2051521 476128 476197 := by
  decide +kernel

private theorem r_476197 : RangeOk getRow 2051521 476197 476264 := by
  decide +kernel

private theorem r_476264 : RangeOk getRow 2051521 476264 476332 := by
  decide +kernel

private theorem r_476332 : RangeOk getRow 2051521 476332 476398 := by
  decide +kernel

private theorem r_476398 : RangeOk getRow 2051521 476398 476465 := by
  decide +kernel

private theorem r_476465 : RangeOk getRow 2051521 476465 476534 := by
  decide +kernel

private theorem r_476534 : RangeOk getRow 2051521 476534 476603 := by
  decide +kernel

private theorem r_476603 : RangeOk getRow 2051521 476603 476671 := by
  decide +kernel

private theorem r_476671 : RangeOk getRow 2051521 476671 476739 := by
  decide +kernel

private theorem r_476739 : RangeOk getRow 2051521 476739 476804 := by
  decide +kernel

private theorem r_476804 : RangeOk getRow 2051521 476804 476870 := by
  decide +kernel

private theorem r_476870 : RangeOk getRow 2051521 476870 476940 := by
  decide +kernel

private theorem r_476940 : RangeOk getRow 2051521 476940 477006 := by
  decide +kernel

private theorem r_477006 : RangeOk getRow 2051521 477006 477073 := by
  decide +kernel

private theorem r_477073 : RangeOk getRow 2051521 477073 477140 := by
  decide +kernel

private theorem r_477140 : RangeOk getRow 2051521 477140 477208 := by
  decide +kernel

private theorem r_477208 : RangeOk getRow 2051521 477208 477277 := by
  decide +kernel

private theorem r_477277 : RangeOk getRow 2051521 477277 477346 := by
  decide +kernel

private theorem r_477346 : RangeOk getRow 2051521 477346 477415 := by
  decide +kernel

private theorem r_477415 : RangeOk getRow 2051521 477415 477482 := by
  decide +kernel

private theorem r_477482 : RangeOk getRow 2051521 477482 477546 := by
  decide +kernel

private theorem r_477546 : RangeOk getRow 2051521 477546 477612 := by
  decide +kernel

private theorem r_477612 : RangeOk getRow 2051521 477612 477681 := by
  decide +kernel

private theorem r_477681 : RangeOk getRow 2051521 477681 477748 := by
  decide +kernel

private theorem s_475520 : RangeOk getRow 2051521 475453 475520 := r_475453
private theorem s_475585 : RangeOk getRow 2051521 475453 475585 :=
  s_475520.append (by norm_num) r_475520
private theorem s_475652 : RangeOk getRow 2051521 475453 475652 :=
  s_475585.append (by norm_num) r_475585
private theorem s_475721 : RangeOk getRow 2051521 475453 475721 :=
  s_475652.append (by norm_num) r_475652
private theorem s_475791 : RangeOk getRow 2051521 475453 475791 :=
  s_475721.append (by norm_num) r_475721
private theorem s_475858 : RangeOk getRow 2051521 475453 475858 :=
  s_475791.append (by norm_num) r_475791
private theorem s_475925 : RangeOk getRow 2051521 475453 475925 :=
  s_475858.append (by norm_num) r_475858
private theorem s_475991 : RangeOk getRow 2051521 475453 475991 :=
  s_475925.append (by norm_num) r_475925
private theorem s_476059 : RangeOk getRow 2051521 475453 476059 :=
  s_475991.append (by norm_num) r_475991
private theorem s_476128 : RangeOk getRow 2051521 475453 476128 :=
  s_476059.append (by norm_num) r_476059
private theorem s_476197 : RangeOk getRow 2051521 475453 476197 :=
  s_476128.append (by norm_num) r_476128
private theorem s_476264 : RangeOk getRow 2051521 475453 476264 :=
  s_476197.append (by norm_num) r_476197
private theorem s_476332 : RangeOk getRow 2051521 475453 476332 :=
  s_476264.append (by norm_num) r_476264
private theorem s_476398 : RangeOk getRow 2051521 475453 476398 :=
  s_476332.append (by norm_num) r_476332
private theorem s_476465 : RangeOk getRow 2051521 475453 476465 :=
  s_476398.append (by norm_num) r_476398
private theorem s_476534 : RangeOk getRow 2051521 475453 476534 :=
  s_476465.append (by norm_num) r_476465
private theorem s_476603 : RangeOk getRow 2051521 475453 476603 :=
  s_476534.append (by norm_num) r_476534
private theorem s_476671 : RangeOk getRow 2051521 475453 476671 :=
  s_476603.append (by norm_num) r_476603
private theorem s_476739 : RangeOk getRow 2051521 475453 476739 :=
  s_476671.append (by norm_num) r_476671
private theorem s_476804 : RangeOk getRow 2051521 475453 476804 :=
  s_476739.append (by norm_num) r_476739
private theorem s_476870 : RangeOk getRow 2051521 475453 476870 :=
  s_476804.append (by norm_num) r_476804
private theorem s_476940 : RangeOk getRow 2051521 475453 476940 :=
  s_476870.append (by norm_num) r_476870
private theorem s_477006 : RangeOk getRow 2051521 475453 477006 :=
  s_476940.append (by norm_num) r_476940
private theorem s_477073 : RangeOk getRow 2051521 475453 477073 :=
  s_477006.append (by norm_num) r_477006
private theorem s_477140 : RangeOk getRow 2051521 475453 477140 :=
  s_477073.append (by norm_num) r_477073
private theorem s_477208 : RangeOk getRow 2051521 475453 477208 :=
  s_477140.append (by norm_num) r_477140
private theorem s_477277 : RangeOk getRow 2051521 475453 477277 :=
  s_477208.append (by norm_num) r_477208
private theorem s_477346 : RangeOk getRow 2051521 475453 477346 :=
  s_477277.append (by norm_num) r_477277
private theorem s_477415 : RangeOk getRow 2051521 475453 477415 :=
  s_477346.append (by norm_num) r_477346
private theorem s_477482 : RangeOk getRow 2051521 475453 477482 :=
  s_477415.append (by norm_num) r_477415
private theorem s_477546 : RangeOk getRow 2051521 475453 477546 :=
  s_477482.append (by norm_num) r_477482
private theorem s_477612 : RangeOk getRow 2051521 475453 477612 :=
  s_477546.append (by norm_num) r_477546
private theorem s_477681 : RangeOk getRow 2051521 475453 477681 :=
  s_477612.append (by norm_num) r_477612
private theorem s_477748 : RangeOk getRow 2051521 475453 477748 :=
  s_477681.append (by norm_num) r_477681

/-- Rows `[475453, 477748)` are valid. -/
theorem rangeOk_475453_477748 : RangeOk getRow 2051521 475453 477748 := s_477748

end Noperthedron.Solution
