import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[27341, 29069). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_27341 : RangeOk getRow 2051521 27341 27405 := by
  decide +kernel

private theorem r_27405 : RangeOk getRow 2051521 27405 27469 := by
  decide +kernel

private theorem r_27469 : RangeOk getRow 2051521 27469 27533 := by
  decide +kernel

private theorem r_27533 : RangeOk getRow 2051521 27533 27597 := by
  decide +kernel

private theorem r_27597 : RangeOk getRow 2051521 27597 27661 := by
  decide +kernel

private theorem r_27661 : RangeOk getRow 2051521 27661 27725 := by
  decide +kernel

private theorem r_27725 : RangeOk getRow 2051521 27725 27789 := by
  decide +kernel

private theorem r_27789 : RangeOk getRow 2051521 27789 27853 := by
  decide +kernel

private theorem r_27853 : RangeOk getRow 2051521 27853 27917 := by
  decide +kernel

private theorem r_27917 : RangeOk getRow 2051521 27917 27981 := by
  decide +kernel

private theorem r_27981 : RangeOk getRow 2051521 27981 28045 := by
  decide +kernel

private theorem r_28045 : RangeOk getRow 2051521 28045 28109 := by
  decide +kernel

private theorem r_28109 : RangeOk getRow 2051521 28109 28173 := by
  decide +kernel

private theorem r_28173 : RangeOk getRow 2051521 28173 28237 := by
  decide +kernel

private theorem r_28237 : RangeOk getRow 2051521 28237 28301 := by
  decide +kernel

private theorem r_28301 : RangeOk getRow 2051521 28301 28365 := by
  decide +kernel

private theorem r_28365 : RangeOk getRow 2051521 28365 28429 := by
  decide +kernel

private theorem r_28429 : RangeOk getRow 2051521 28429 28493 := by
  decide +kernel

private theorem r_28493 : RangeOk getRow 2051521 28493 28557 := by
  decide +kernel

private theorem r_28557 : RangeOk getRow 2051521 28557 28621 := by
  decide +kernel

private theorem r_28621 : RangeOk getRow 2051521 28621 28685 := by
  decide +kernel

private theorem r_28685 : RangeOk getRow 2051521 28685 28749 := by
  decide +kernel

private theorem r_28749 : RangeOk getRow 2051521 28749 28813 := by
  decide +kernel

private theorem r_28813 : RangeOk getRow 2051521 28813 28877 := by
  decide +kernel

private theorem r_28877 : RangeOk getRow 2051521 28877 28941 := by
  decide +kernel

private theorem r_28941 : RangeOk getRow 2051521 28941 29005 := by
  decide +kernel

private theorem r_29005 : RangeOk getRow 2051521 29005 29069 := by
  decide +kernel

private theorem s_27405 : RangeOk getRow 2051521 27341 27405 := r_27341
private theorem s_27469 : RangeOk getRow 2051521 27341 27469 :=
  s_27405.append (by norm_num) r_27405
private theorem s_27533 : RangeOk getRow 2051521 27341 27533 :=
  s_27469.append (by norm_num) r_27469
private theorem s_27597 : RangeOk getRow 2051521 27341 27597 :=
  s_27533.append (by norm_num) r_27533
private theorem s_27661 : RangeOk getRow 2051521 27341 27661 :=
  s_27597.append (by norm_num) r_27597
private theorem s_27725 : RangeOk getRow 2051521 27341 27725 :=
  s_27661.append (by norm_num) r_27661
private theorem s_27789 : RangeOk getRow 2051521 27341 27789 :=
  s_27725.append (by norm_num) r_27725
private theorem s_27853 : RangeOk getRow 2051521 27341 27853 :=
  s_27789.append (by norm_num) r_27789
private theorem s_27917 : RangeOk getRow 2051521 27341 27917 :=
  s_27853.append (by norm_num) r_27853
private theorem s_27981 : RangeOk getRow 2051521 27341 27981 :=
  s_27917.append (by norm_num) r_27917
private theorem s_28045 : RangeOk getRow 2051521 27341 28045 :=
  s_27981.append (by norm_num) r_27981
private theorem s_28109 : RangeOk getRow 2051521 27341 28109 :=
  s_28045.append (by norm_num) r_28045
private theorem s_28173 : RangeOk getRow 2051521 27341 28173 :=
  s_28109.append (by norm_num) r_28109
private theorem s_28237 : RangeOk getRow 2051521 27341 28237 :=
  s_28173.append (by norm_num) r_28173
private theorem s_28301 : RangeOk getRow 2051521 27341 28301 :=
  s_28237.append (by norm_num) r_28237
private theorem s_28365 : RangeOk getRow 2051521 27341 28365 :=
  s_28301.append (by norm_num) r_28301
private theorem s_28429 : RangeOk getRow 2051521 27341 28429 :=
  s_28365.append (by norm_num) r_28365
private theorem s_28493 : RangeOk getRow 2051521 27341 28493 :=
  s_28429.append (by norm_num) r_28429
private theorem s_28557 : RangeOk getRow 2051521 27341 28557 :=
  s_28493.append (by norm_num) r_28493
private theorem s_28621 : RangeOk getRow 2051521 27341 28621 :=
  s_28557.append (by norm_num) r_28557
private theorem s_28685 : RangeOk getRow 2051521 27341 28685 :=
  s_28621.append (by norm_num) r_28621
private theorem s_28749 : RangeOk getRow 2051521 27341 28749 :=
  s_28685.append (by norm_num) r_28685
private theorem s_28813 : RangeOk getRow 2051521 27341 28813 :=
  s_28749.append (by norm_num) r_28749
private theorem s_28877 : RangeOk getRow 2051521 27341 28877 :=
  s_28813.append (by norm_num) r_28813
private theorem s_28941 : RangeOk getRow 2051521 27341 28941 :=
  s_28877.append (by norm_num) r_28877
private theorem s_29005 : RangeOk getRow 2051521 27341 29005 :=
  s_28941.append (by norm_num) r_28941
private theorem s_29069 : RangeOk getRow 2051521 27341 29069 :=
  s_29005.append (by norm_num) r_29005

/-- Rows `[27341, 29069)` are valid. -/
theorem rangeOk_27341_29069 : RangeOk getRow 2051521 27341 29069 := s_29069

end Noperthedron.Solution
