import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1029521, 1031974). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1029521 : RangeOk getRow 2051521 1029521 1029589 := by
  decide +kernel

private theorem r_1029589 : RangeOk getRow 2051521 1029589 1029656 := by
  decide +kernel

private theorem r_1029656 : RangeOk getRow 2051521 1029656 1029724 := by
  decide +kernel

private theorem r_1029724 : RangeOk getRow 2051521 1029724 1029790 := by
  decide +kernel

private theorem r_1029790 : RangeOk getRow 2051521 1029790 1029856 := by
  decide +kernel

private theorem r_1029856 : RangeOk getRow 2051521 1029856 1029923 := by
  decide +kernel

private theorem r_1029923 : RangeOk getRow 2051521 1029923 1029992 := by
  decide +kernel

private theorem r_1029992 : RangeOk getRow 2051521 1029992 1030060 := by
  decide +kernel

private theorem r_1030060 : RangeOk getRow 2051521 1030060 1030126 := by
  decide +kernel

private theorem r_1030126 : RangeOk getRow 2051521 1030126 1030194 := by
  decide +kernel

private theorem r_1030194 : RangeOk getRow 2051521 1030194 1030261 := by
  decide +kernel

private theorem r_1030261 : RangeOk getRow 2051521 1030261 1030327 := by
  decide +kernel

private theorem r_1030327 : RangeOk getRow 2051521 1030327 1030394 := by
  decide +kernel

private theorem r_1030394 : RangeOk getRow 2051521 1030394 1030460 := by
  decide +kernel

private theorem r_1030460 : RangeOk getRow 2051521 1030460 1030529 := by
  decide +kernel

private theorem r_1030529 : RangeOk getRow 2051521 1030529 1030598 := by
  decide +kernel

private theorem r_1030598 : RangeOk getRow 2051521 1030598 1030668 := by
  decide +kernel

private theorem r_1030668 : RangeOk getRow 2051521 1030668 1030735 := by
  decide +kernel

private theorem r_1030735 : RangeOk getRow 2051521 1030735 1030806 := by
  decide +kernel

private theorem r_1030806 : RangeOk getRow 2051521 1030806 1030875 := by
  decide +kernel

private theorem r_1030875 : RangeOk getRow 2051521 1030875 1030943 := by
  decide +kernel

private theorem r_1030943 : RangeOk getRow 2051521 1030943 1031011 := by
  decide +kernel

private theorem r_1031011 : RangeOk getRow 2051521 1031011 1031081 := by
  decide +kernel

private theorem r_1031081 : RangeOk getRow 2051521 1031081 1031149 := by
  decide +kernel

private theorem r_1031149 : RangeOk getRow 2051521 1031149 1031216 := by
  decide +kernel

private theorem r_1031216 : RangeOk getRow 2051521 1031216 1031284 := by
  decide +kernel

private theorem r_1031284 : RangeOk getRow 2051521 1031284 1031352 := by
  decide +kernel

private theorem r_1031352 : RangeOk getRow 2051521 1031352 1031423 := by
  decide +kernel

private theorem r_1031423 : RangeOk getRow 2051521 1031423 1031491 := by
  decide +kernel

private theorem r_1031491 : RangeOk getRow 2051521 1031491 1031558 := by
  decide +kernel

private theorem r_1031558 : RangeOk getRow 2051521 1031558 1031629 := by
  decide +kernel

private theorem r_1031629 : RangeOk getRow 2051521 1031629 1031700 := by
  decide +kernel

private theorem r_1031700 : RangeOk getRow 2051521 1031700 1031773 := by
  decide +kernel

private theorem r_1031773 : RangeOk getRow 2051521 1031773 1031840 := by
  decide +kernel

private theorem r_1031840 : RangeOk getRow 2051521 1031840 1031908 := by
  decide +kernel

private theorem r_1031908 : RangeOk getRow 2051521 1031908 1031974 := by
  decide +kernel

private theorem s_1029589 : RangeOk getRow 2051521 1029521 1029589 := r_1029521
private theorem s_1029656 : RangeOk getRow 2051521 1029521 1029656 :=
  s_1029589.append (by norm_num) r_1029589
private theorem s_1029724 : RangeOk getRow 2051521 1029521 1029724 :=
  s_1029656.append (by norm_num) r_1029656
private theorem s_1029790 : RangeOk getRow 2051521 1029521 1029790 :=
  s_1029724.append (by norm_num) r_1029724
private theorem s_1029856 : RangeOk getRow 2051521 1029521 1029856 :=
  s_1029790.append (by norm_num) r_1029790
private theorem s_1029923 : RangeOk getRow 2051521 1029521 1029923 :=
  s_1029856.append (by norm_num) r_1029856
private theorem s_1029992 : RangeOk getRow 2051521 1029521 1029992 :=
  s_1029923.append (by norm_num) r_1029923
private theorem s_1030060 : RangeOk getRow 2051521 1029521 1030060 :=
  s_1029992.append (by norm_num) r_1029992
private theorem s_1030126 : RangeOk getRow 2051521 1029521 1030126 :=
  s_1030060.append (by norm_num) r_1030060
private theorem s_1030194 : RangeOk getRow 2051521 1029521 1030194 :=
  s_1030126.append (by norm_num) r_1030126
private theorem s_1030261 : RangeOk getRow 2051521 1029521 1030261 :=
  s_1030194.append (by norm_num) r_1030194
private theorem s_1030327 : RangeOk getRow 2051521 1029521 1030327 :=
  s_1030261.append (by norm_num) r_1030261
private theorem s_1030394 : RangeOk getRow 2051521 1029521 1030394 :=
  s_1030327.append (by norm_num) r_1030327
private theorem s_1030460 : RangeOk getRow 2051521 1029521 1030460 :=
  s_1030394.append (by norm_num) r_1030394
private theorem s_1030529 : RangeOk getRow 2051521 1029521 1030529 :=
  s_1030460.append (by norm_num) r_1030460
private theorem s_1030598 : RangeOk getRow 2051521 1029521 1030598 :=
  s_1030529.append (by norm_num) r_1030529
private theorem s_1030668 : RangeOk getRow 2051521 1029521 1030668 :=
  s_1030598.append (by norm_num) r_1030598
private theorem s_1030735 : RangeOk getRow 2051521 1029521 1030735 :=
  s_1030668.append (by norm_num) r_1030668
private theorem s_1030806 : RangeOk getRow 2051521 1029521 1030806 :=
  s_1030735.append (by norm_num) r_1030735
private theorem s_1030875 : RangeOk getRow 2051521 1029521 1030875 :=
  s_1030806.append (by norm_num) r_1030806
private theorem s_1030943 : RangeOk getRow 2051521 1029521 1030943 :=
  s_1030875.append (by norm_num) r_1030875
private theorem s_1031011 : RangeOk getRow 2051521 1029521 1031011 :=
  s_1030943.append (by norm_num) r_1030943
private theorem s_1031081 : RangeOk getRow 2051521 1029521 1031081 :=
  s_1031011.append (by norm_num) r_1031011
private theorem s_1031149 : RangeOk getRow 2051521 1029521 1031149 :=
  s_1031081.append (by norm_num) r_1031081
private theorem s_1031216 : RangeOk getRow 2051521 1029521 1031216 :=
  s_1031149.append (by norm_num) r_1031149
private theorem s_1031284 : RangeOk getRow 2051521 1029521 1031284 :=
  s_1031216.append (by norm_num) r_1031216
private theorem s_1031352 : RangeOk getRow 2051521 1029521 1031352 :=
  s_1031284.append (by norm_num) r_1031284
private theorem s_1031423 : RangeOk getRow 2051521 1029521 1031423 :=
  s_1031352.append (by norm_num) r_1031352
private theorem s_1031491 : RangeOk getRow 2051521 1029521 1031491 :=
  s_1031423.append (by norm_num) r_1031423
private theorem s_1031558 : RangeOk getRow 2051521 1029521 1031558 :=
  s_1031491.append (by norm_num) r_1031491
private theorem s_1031629 : RangeOk getRow 2051521 1029521 1031629 :=
  s_1031558.append (by norm_num) r_1031558
private theorem s_1031700 : RangeOk getRow 2051521 1029521 1031700 :=
  s_1031629.append (by norm_num) r_1031629
private theorem s_1031773 : RangeOk getRow 2051521 1029521 1031773 :=
  s_1031700.append (by norm_num) r_1031700
private theorem s_1031840 : RangeOk getRow 2051521 1029521 1031840 :=
  s_1031773.append (by norm_num) r_1031773
private theorem s_1031908 : RangeOk getRow 2051521 1029521 1031908 :=
  s_1031840.append (by norm_num) r_1031840
private theorem s_1031974 : RangeOk getRow 2051521 1029521 1031974 :=
  s_1031908.append (by norm_num) r_1031908

/-- Rows `[1029521, 1031974)` are valid. -/
theorem rangeOk_1029521_1031974 : RangeOk getRow 2051521 1029521 1031974 := s_1031974

end Noperthedron.Solution
