import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[847127, 849423). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_847127 : RangeOk getRow 2051521 847127 847198 := by
  decide +kernel

private theorem r_847198 : RangeOk getRow 2051521 847198 847265 := by
  decide +kernel

private theorem r_847265 : RangeOk getRow 2051521 847265 847332 := by
  decide +kernel

private theorem r_847332 : RangeOk getRow 2051521 847332 847399 := by
  decide +kernel

private theorem r_847399 : RangeOk getRow 2051521 847399 847465 := by
  decide +kernel

private theorem r_847465 : RangeOk getRow 2051521 847465 847533 := by
  decide +kernel

private theorem r_847533 : RangeOk getRow 2051521 847533 847605 := by
  decide +kernel

private theorem r_847605 : RangeOk getRow 2051521 847605 847672 := by
  decide +kernel

private theorem r_847672 : RangeOk getRow 2051521 847672 847739 := by
  decide +kernel

private theorem r_847739 : RangeOk getRow 2051521 847739 847806 := by
  decide +kernel

private theorem r_847806 : RangeOk getRow 2051521 847806 847873 := by
  decide +kernel

private theorem r_847873 : RangeOk getRow 2051521 847873 847939 := by
  decide +kernel

private theorem r_847939 : RangeOk getRow 2051521 847939 848007 := by
  decide +kernel

private theorem r_848007 : RangeOk getRow 2051521 848007 848076 := by
  decide +kernel

private theorem r_848076 : RangeOk getRow 2051521 848076 848144 := by
  decide +kernel

private theorem r_848144 : RangeOk getRow 2051521 848144 848210 := by
  decide +kernel

private theorem r_848210 : RangeOk getRow 2051521 848210 848277 := by
  decide +kernel

private theorem r_848277 : RangeOk getRow 2051521 848277 848345 := by
  decide +kernel

private theorem r_848345 : RangeOk getRow 2051521 848345 848415 := by
  decide +kernel

private theorem r_848415 : RangeOk getRow 2051521 848415 848485 := by
  decide +kernel

private theorem r_848485 : RangeOk getRow 2051521 848485 848553 := by
  decide +kernel

private theorem r_848553 : RangeOk getRow 2051521 848553 848619 := by
  decide +kernel

private theorem r_848619 : RangeOk getRow 2051521 848619 848687 := by
  decide +kernel

private theorem r_848687 : RangeOk getRow 2051521 848687 848755 := by
  decide +kernel

private theorem r_848755 : RangeOk getRow 2051521 848755 848821 := by
  decide +kernel

private theorem r_848821 : RangeOk getRow 2051521 848821 848888 := by
  decide +kernel

private theorem r_848888 : RangeOk getRow 2051521 848888 848953 := by
  decide +kernel

private theorem r_848953 : RangeOk getRow 2051521 848953 849020 := by
  decide +kernel

private theorem r_849020 : RangeOk getRow 2051521 849020 849088 := by
  decide +kernel

private theorem r_849088 : RangeOk getRow 2051521 849088 849154 := by
  decide +kernel

private theorem r_849154 : RangeOk getRow 2051521 849154 849219 := by
  decide +kernel

private theorem r_849219 : RangeOk getRow 2051521 849219 849286 := by
  decide +kernel

private theorem r_849286 : RangeOk getRow 2051521 849286 849358 := by
  decide +kernel

private theorem r_849358 : RangeOk getRow 2051521 849358 849423 := by
  decide +kernel

private theorem s_847198 : RangeOk getRow 2051521 847127 847198 := r_847127
private theorem s_847265 : RangeOk getRow 2051521 847127 847265 :=
  s_847198.append (by norm_num) r_847198
private theorem s_847332 : RangeOk getRow 2051521 847127 847332 :=
  s_847265.append (by norm_num) r_847265
private theorem s_847399 : RangeOk getRow 2051521 847127 847399 :=
  s_847332.append (by norm_num) r_847332
private theorem s_847465 : RangeOk getRow 2051521 847127 847465 :=
  s_847399.append (by norm_num) r_847399
private theorem s_847533 : RangeOk getRow 2051521 847127 847533 :=
  s_847465.append (by norm_num) r_847465
private theorem s_847605 : RangeOk getRow 2051521 847127 847605 :=
  s_847533.append (by norm_num) r_847533
private theorem s_847672 : RangeOk getRow 2051521 847127 847672 :=
  s_847605.append (by norm_num) r_847605
private theorem s_847739 : RangeOk getRow 2051521 847127 847739 :=
  s_847672.append (by norm_num) r_847672
private theorem s_847806 : RangeOk getRow 2051521 847127 847806 :=
  s_847739.append (by norm_num) r_847739
private theorem s_847873 : RangeOk getRow 2051521 847127 847873 :=
  s_847806.append (by norm_num) r_847806
private theorem s_847939 : RangeOk getRow 2051521 847127 847939 :=
  s_847873.append (by norm_num) r_847873
private theorem s_848007 : RangeOk getRow 2051521 847127 848007 :=
  s_847939.append (by norm_num) r_847939
private theorem s_848076 : RangeOk getRow 2051521 847127 848076 :=
  s_848007.append (by norm_num) r_848007
private theorem s_848144 : RangeOk getRow 2051521 847127 848144 :=
  s_848076.append (by norm_num) r_848076
private theorem s_848210 : RangeOk getRow 2051521 847127 848210 :=
  s_848144.append (by norm_num) r_848144
private theorem s_848277 : RangeOk getRow 2051521 847127 848277 :=
  s_848210.append (by norm_num) r_848210
private theorem s_848345 : RangeOk getRow 2051521 847127 848345 :=
  s_848277.append (by norm_num) r_848277
private theorem s_848415 : RangeOk getRow 2051521 847127 848415 :=
  s_848345.append (by norm_num) r_848345
private theorem s_848485 : RangeOk getRow 2051521 847127 848485 :=
  s_848415.append (by norm_num) r_848415
private theorem s_848553 : RangeOk getRow 2051521 847127 848553 :=
  s_848485.append (by norm_num) r_848485
private theorem s_848619 : RangeOk getRow 2051521 847127 848619 :=
  s_848553.append (by norm_num) r_848553
private theorem s_848687 : RangeOk getRow 2051521 847127 848687 :=
  s_848619.append (by norm_num) r_848619
private theorem s_848755 : RangeOk getRow 2051521 847127 848755 :=
  s_848687.append (by norm_num) r_848687
private theorem s_848821 : RangeOk getRow 2051521 847127 848821 :=
  s_848755.append (by norm_num) r_848755
private theorem s_848888 : RangeOk getRow 2051521 847127 848888 :=
  s_848821.append (by norm_num) r_848821
private theorem s_848953 : RangeOk getRow 2051521 847127 848953 :=
  s_848888.append (by norm_num) r_848888
private theorem s_849020 : RangeOk getRow 2051521 847127 849020 :=
  s_848953.append (by norm_num) r_848953
private theorem s_849088 : RangeOk getRow 2051521 847127 849088 :=
  s_849020.append (by norm_num) r_849020
private theorem s_849154 : RangeOk getRow 2051521 847127 849154 :=
  s_849088.append (by norm_num) r_849088
private theorem s_849219 : RangeOk getRow 2051521 847127 849219 :=
  s_849154.append (by norm_num) r_849154
private theorem s_849286 : RangeOk getRow 2051521 847127 849286 :=
  s_849219.append (by norm_num) r_849219
private theorem s_849358 : RangeOk getRow 2051521 847127 849358 :=
  s_849286.append (by norm_num) r_849286
private theorem s_849423 : RangeOk getRow 2051521 847127 849423 :=
  s_849358.append (by norm_num) r_849358

/-- Rows `[847127, 849423)` are valid. -/
theorem rangeOk_847127_849423 : RangeOk getRow 2051521 847127 849423 := s_849423

end Noperthedron.Solution
