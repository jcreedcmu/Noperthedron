import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1043013, 1045472). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1043013 : RangeOk getRow 2051521 1043013 1043085 := by
  decide +kernel

private theorem r_1043085 : RangeOk getRow 2051521 1043085 1043151 := by
  decide +kernel

private theorem r_1043151 : RangeOk getRow 2051521 1043151 1043219 := by
  decide +kernel

private theorem r_1043219 : RangeOk getRow 2051521 1043219 1043290 := by
  decide +kernel

private theorem r_1043290 : RangeOk getRow 2051521 1043290 1043360 := by
  decide +kernel

private theorem r_1043360 : RangeOk getRow 2051521 1043360 1043430 := by
  decide +kernel

private theorem r_1043430 : RangeOk getRow 2051521 1043430 1043501 := by
  decide +kernel

private theorem r_1043501 : RangeOk getRow 2051521 1043501 1043573 := by
  decide +kernel

private theorem r_1043573 : RangeOk getRow 2051521 1043573 1043640 := by
  decide +kernel

private theorem r_1043640 : RangeOk getRow 2051521 1043640 1043708 := by
  decide +kernel

private theorem r_1043708 : RangeOk getRow 2051521 1043708 1043774 := by
  decide +kernel

private theorem r_1043774 : RangeOk getRow 2051521 1043774 1043842 := by
  decide +kernel

private theorem r_1043842 : RangeOk getRow 2051521 1043842 1043909 := by
  decide +kernel

private theorem r_1043909 : RangeOk getRow 2051521 1043909 1043977 := by
  decide +kernel

private theorem r_1043977 : RangeOk getRow 2051521 1043977 1044045 := by
  decide +kernel

private theorem r_1044045 : RangeOk getRow 2051521 1044045 1044115 := by
  decide +kernel

private theorem r_1044115 : RangeOk getRow 2051521 1044115 1044187 := by
  decide +kernel

private theorem r_1044187 : RangeOk getRow 2051521 1044187 1044254 := by
  decide +kernel

private theorem r_1044254 : RangeOk getRow 2051521 1044254 1044321 := by
  decide +kernel

private theorem r_1044321 : RangeOk getRow 2051521 1044321 1044390 := by
  decide +kernel

private theorem r_1044390 : RangeOk getRow 2051521 1044390 1044456 := by
  decide +kernel

private theorem r_1044456 : RangeOk getRow 2051521 1044456 1044522 := by
  decide +kernel

private theorem r_1044522 : RangeOk getRow 2051521 1044522 1044587 := by
  decide +kernel

private theorem r_1044587 : RangeOk getRow 2051521 1044587 1044653 := by
  decide +kernel

private theorem r_1044653 : RangeOk getRow 2051521 1044653 1044721 := by
  decide +kernel

private theorem r_1044721 : RangeOk getRow 2051521 1044721 1044788 := by
  decide +kernel

private theorem r_1044788 : RangeOk getRow 2051521 1044788 1044859 := by
  decide +kernel

private theorem r_1044859 : RangeOk getRow 2051521 1044859 1044931 := by
  decide +kernel

private theorem r_1044931 : RangeOk getRow 2051521 1044931 1044997 := by
  decide +kernel

private theorem r_1044997 : RangeOk getRow 2051521 1044997 1045067 := by
  decide +kernel

private theorem r_1045067 : RangeOk getRow 2051521 1045067 1045133 := by
  decide +kernel

private theorem r_1045133 : RangeOk getRow 2051521 1045133 1045201 := by
  decide +kernel

private theorem r_1045201 : RangeOk getRow 2051521 1045201 1045268 := by
  decide +kernel

private theorem r_1045268 : RangeOk getRow 2051521 1045268 1045336 := by
  decide +kernel

private theorem r_1045336 : RangeOk getRow 2051521 1045336 1045405 := by
  decide +kernel

private theorem r_1045405 : RangeOk getRow 2051521 1045405 1045472 := by
  decide +kernel

private theorem s_1043085 : RangeOk getRow 2051521 1043013 1043085 := r_1043013
private theorem s_1043151 : RangeOk getRow 2051521 1043013 1043151 :=
  s_1043085.append (by norm_num) r_1043085
private theorem s_1043219 : RangeOk getRow 2051521 1043013 1043219 :=
  s_1043151.append (by norm_num) r_1043151
private theorem s_1043290 : RangeOk getRow 2051521 1043013 1043290 :=
  s_1043219.append (by norm_num) r_1043219
private theorem s_1043360 : RangeOk getRow 2051521 1043013 1043360 :=
  s_1043290.append (by norm_num) r_1043290
private theorem s_1043430 : RangeOk getRow 2051521 1043013 1043430 :=
  s_1043360.append (by norm_num) r_1043360
private theorem s_1043501 : RangeOk getRow 2051521 1043013 1043501 :=
  s_1043430.append (by norm_num) r_1043430
private theorem s_1043573 : RangeOk getRow 2051521 1043013 1043573 :=
  s_1043501.append (by norm_num) r_1043501
private theorem s_1043640 : RangeOk getRow 2051521 1043013 1043640 :=
  s_1043573.append (by norm_num) r_1043573
private theorem s_1043708 : RangeOk getRow 2051521 1043013 1043708 :=
  s_1043640.append (by norm_num) r_1043640
private theorem s_1043774 : RangeOk getRow 2051521 1043013 1043774 :=
  s_1043708.append (by norm_num) r_1043708
private theorem s_1043842 : RangeOk getRow 2051521 1043013 1043842 :=
  s_1043774.append (by norm_num) r_1043774
private theorem s_1043909 : RangeOk getRow 2051521 1043013 1043909 :=
  s_1043842.append (by norm_num) r_1043842
private theorem s_1043977 : RangeOk getRow 2051521 1043013 1043977 :=
  s_1043909.append (by norm_num) r_1043909
private theorem s_1044045 : RangeOk getRow 2051521 1043013 1044045 :=
  s_1043977.append (by norm_num) r_1043977
private theorem s_1044115 : RangeOk getRow 2051521 1043013 1044115 :=
  s_1044045.append (by norm_num) r_1044045
private theorem s_1044187 : RangeOk getRow 2051521 1043013 1044187 :=
  s_1044115.append (by norm_num) r_1044115
private theorem s_1044254 : RangeOk getRow 2051521 1043013 1044254 :=
  s_1044187.append (by norm_num) r_1044187
private theorem s_1044321 : RangeOk getRow 2051521 1043013 1044321 :=
  s_1044254.append (by norm_num) r_1044254
private theorem s_1044390 : RangeOk getRow 2051521 1043013 1044390 :=
  s_1044321.append (by norm_num) r_1044321
private theorem s_1044456 : RangeOk getRow 2051521 1043013 1044456 :=
  s_1044390.append (by norm_num) r_1044390
private theorem s_1044522 : RangeOk getRow 2051521 1043013 1044522 :=
  s_1044456.append (by norm_num) r_1044456
private theorem s_1044587 : RangeOk getRow 2051521 1043013 1044587 :=
  s_1044522.append (by norm_num) r_1044522
private theorem s_1044653 : RangeOk getRow 2051521 1043013 1044653 :=
  s_1044587.append (by norm_num) r_1044587
private theorem s_1044721 : RangeOk getRow 2051521 1043013 1044721 :=
  s_1044653.append (by norm_num) r_1044653
private theorem s_1044788 : RangeOk getRow 2051521 1043013 1044788 :=
  s_1044721.append (by norm_num) r_1044721
private theorem s_1044859 : RangeOk getRow 2051521 1043013 1044859 :=
  s_1044788.append (by norm_num) r_1044788
private theorem s_1044931 : RangeOk getRow 2051521 1043013 1044931 :=
  s_1044859.append (by norm_num) r_1044859
private theorem s_1044997 : RangeOk getRow 2051521 1043013 1044997 :=
  s_1044931.append (by norm_num) r_1044931
private theorem s_1045067 : RangeOk getRow 2051521 1043013 1045067 :=
  s_1044997.append (by norm_num) r_1044997
private theorem s_1045133 : RangeOk getRow 2051521 1043013 1045133 :=
  s_1045067.append (by norm_num) r_1045067
private theorem s_1045201 : RangeOk getRow 2051521 1043013 1045201 :=
  s_1045133.append (by norm_num) r_1045133
private theorem s_1045268 : RangeOk getRow 2051521 1043013 1045268 :=
  s_1045201.append (by norm_num) r_1045201
private theorem s_1045336 : RangeOk getRow 2051521 1043013 1045336 :=
  s_1045268.append (by norm_num) r_1045268
private theorem s_1045405 : RangeOk getRow 2051521 1043013 1045405 :=
  s_1045336.append (by norm_num) r_1045336
private theorem s_1045472 : RangeOk getRow 2051521 1043013 1045472 :=
  s_1045405.append (by norm_num) r_1045405

/-- Rows `[1043013, 1045472)` are valid. -/
theorem rangeOk_1043013_1045472 : RangeOk getRow 2051521 1043013 1045472 := s_1045472

end Noperthedron.Solution
