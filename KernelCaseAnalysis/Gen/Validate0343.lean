import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[825442, 827742). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_825442 : RangeOk getRow 2051521 825442 825511 := by
  decide +kernel

private theorem r_825511 : RangeOk getRow 2051521 825511 825579 := by
  decide +kernel

private theorem r_825579 : RangeOk getRow 2051521 825579 825649 := by
  decide +kernel

private theorem r_825649 : RangeOk getRow 2051521 825649 825717 := by
  decide +kernel

private theorem r_825717 : RangeOk getRow 2051521 825717 825787 := by
  decide +kernel

private theorem r_825787 : RangeOk getRow 2051521 825787 825854 := by
  decide +kernel

private theorem r_825854 : RangeOk getRow 2051521 825854 825920 := by
  decide +kernel

private theorem r_825920 : RangeOk getRow 2051521 825920 825988 := by
  decide +kernel

private theorem r_825988 : RangeOk getRow 2051521 825988 826057 := by
  decide +kernel

private theorem r_826057 : RangeOk getRow 2051521 826057 826123 := by
  decide +kernel

private theorem r_826123 : RangeOk getRow 2051521 826123 826190 := by
  decide +kernel

private theorem r_826190 : RangeOk getRow 2051521 826190 826256 := by
  decide +kernel

private theorem r_826256 : RangeOk getRow 2051521 826256 826323 := by
  decide +kernel

private theorem r_826323 : RangeOk getRow 2051521 826323 826391 := by
  decide +kernel

private theorem r_826391 : RangeOk getRow 2051521 826391 826458 := by
  decide +kernel

private theorem r_826458 : RangeOk getRow 2051521 826458 826524 := by
  decide +kernel

private theorem r_826524 : RangeOk getRow 2051521 826524 826591 := by
  decide +kernel

private theorem r_826591 : RangeOk getRow 2051521 826591 826660 := by
  decide +kernel

private theorem r_826660 : RangeOk getRow 2051521 826660 826731 := by
  decide +kernel

private theorem r_826731 : RangeOk getRow 2051521 826731 826799 := by
  decide +kernel

private theorem r_826799 : RangeOk getRow 2051521 826799 826865 := by
  decide +kernel

private theorem r_826865 : RangeOk getRow 2051521 826865 826932 := by
  decide +kernel

private theorem r_826932 : RangeOk getRow 2051521 826932 827001 := by
  decide +kernel

private theorem r_827001 : RangeOk getRow 2051521 827001 827069 := by
  decide +kernel

private theorem r_827069 : RangeOk getRow 2051521 827069 827137 := by
  decide +kernel

private theorem r_827137 : RangeOk getRow 2051521 827137 827205 := by
  decide +kernel

private theorem r_827205 : RangeOk getRow 2051521 827205 827272 := by
  decide +kernel

private theorem r_827272 : RangeOk getRow 2051521 827272 827341 := by
  decide +kernel

private theorem r_827341 : RangeOk getRow 2051521 827341 827408 := by
  decide +kernel

private theorem r_827408 : RangeOk getRow 2051521 827408 827475 := by
  decide +kernel

private theorem r_827475 : RangeOk getRow 2051521 827475 827541 := by
  decide +kernel

private theorem r_827541 : RangeOk getRow 2051521 827541 827607 := by
  decide +kernel

private theorem r_827607 : RangeOk getRow 2051521 827607 827674 := by
  decide +kernel

private theorem r_827674 : RangeOk getRow 2051521 827674 827742 := by
  decide +kernel

private theorem s_825511 : RangeOk getRow 2051521 825442 825511 := r_825442
private theorem s_825579 : RangeOk getRow 2051521 825442 825579 :=
  s_825511.append (by norm_num) r_825511
private theorem s_825649 : RangeOk getRow 2051521 825442 825649 :=
  s_825579.append (by norm_num) r_825579
private theorem s_825717 : RangeOk getRow 2051521 825442 825717 :=
  s_825649.append (by norm_num) r_825649
private theorem s_825787 : RangeOk getRow 2051521 825442 825787 :=
  s_825717.append (by norm_num) r_825717
private theorem s_825854 : RangeOk getRow 2051521 825442 825854 :=
  s_825787.append (by norm_num) r_825787
private theorem s_825920 : RangeOk getRow 2051521 825442 825920 :=
  s_825854.append (by norm_num) r_825854
private theorem s_825988 : RangeOk getRow 2051521 825442 825988 :=
  s_825920.append (by norm_num) r_825920
private theorem s_826057 : RangeOk getRow 2051521 825442 826057 :=
  s_825988.append (by norm_num) r_825988
private theorem s_826123 : RangeOk getRow 2051521 825442 826123 :=
  s_826057.append (by norm_num) r_826057
private theorem s_826190 : RangeOk getRow 2051521 825442 826190 :=
  s_826123.append (by norm_num) r_826123
private theorem s_826256 : RangeOk getRow 2051521 825442 826256 :=
  s_826190.append (by norm_num) r_826190
private theorem s_826323 : RangeOk getRow 2051521 825442 826323 :=
  s_826256.append (by norm_num) r_826256
private theorem s_826391 : RangeOk getRow 2051521 825442 826391 :=
  s_826323.append (by norm_num) r_826323
private theorem s_826458 : RangeOk getRow 2051521 825442 826458 :=
  s_826391.append (by norm_num) r_826391
private theorem s_826524 : RangeOk getRow 2051521 825442 826524 :=
  s_826458.append (by norm_num) r_826458
private theorem s_826591 : RangeOk getRow 2051521 825442 826591 :=
  s_826524.append (by norm_num) r_826524
private theorem s_826660 : RangeOk getRow 2051521 825442 826660 :=
  s_826591.append (by norm_num) r_826591
private theorem s_826731 : RangeOk getRow 2051521 825442 826731 :=
  s_826660.append (by norm_num) r_826660
private theorem s_826799 : RangeOk getRow 2051521 825442 826799 :=
  s_826731.append (by norm_num) r_826731
private theorem s_826865 : RangeOk getRow 2051521 825442 826865 :=
  s_826799.append (by norm_num) r_826799
private theorem s_826932 : RangeOk getRow 2051521 825442 826932 :=
  s_826865.append (by norm_num) r_826865
private theorem s_827001 : RangeOk getRow 2051521 825442 827001 :=
  s_826932.append (by norm_num) r_826932
private theorem s_827069 : RangeOk getRow 2051521 825442 827069 :=
  s_827001.append (by norm_num) r_827001
private theorem s_827137 : RangeOk getRow 2051521 825442 827137 :=
  s_827069.append (by norm_num) r_827069
private theorem s_827205 : RangeOk getRow 2051521 825442 827205 :=
  s_827137.append (by norm_num) r_827137
private theorem s_827272 : RangeOk getRow 2051521 825442 827272 :=
  s_827205.append (by norm_num) r_827205
private theorem s_827341 : RangeOk getRow 2051521 825442 827341 :=
  s_827272.append (by norm_num) r_827272
private theorem s_827408 : RangeOk getRow 2051521 825442 827408 :=
  s_827341.append (by norm_num) r_827341
private theorem s_827475 : RangeOk getRow 2051521 825442 827475 :=
  s_827408.append (by norm_num) r_827408
private theorem s_827541 : RangeOk getRow 2051521 825442 827541 :=
  s_827475.append (by norm_num) r_827475
private theorem s_827607 : RangeOk getRow 2051521 825442 827607 :=
  s_827541.append (by norm_num) r_827541
private theorem s_827674 : RangeOk getRow 2051521 825442 827674 :=
  s_827607.append (by norm_num) r_827607
private theorem s_827742 : RangeOk getRow 2051521 825442 827742 :=
  s_827674.append (by norm_num) r_827674

/-- Rows `[825442, 827742)` are valid. -/
theorem rangeOk_825442_827742 : RangeOk getRow 2051521 825442 827742 := s_827742

end Noperthedron.Solution
