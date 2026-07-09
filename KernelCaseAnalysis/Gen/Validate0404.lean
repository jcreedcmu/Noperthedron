import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[976283, 978583). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_976283 : RangeOk getRow 2051521 976283 976352 := by
  decide +kernel

private theorem r_976352 : RangeOk getRow 2051521 976352 976420 := by
  decide +kernel

private theorem r_976420 : RangeOk getRow 2051521 976420 976489 := by
  decide +kernel

private theorem r_976489 : RangeOk getRow 2051521 976489 976558 := by
  decide +kernel

private theorem r_976558 : RangeOk getRow 2051521 976558 976626 := by
  decide +kernel

private theorem r_976626 : RangeOk getRow 2051521 976626 976696 := by
  decide +kernel

private theorem r_976696 : RangeOk getRow 2051521 976696 976765 := by
  decide +kernel

private theorem r_976765 : RangeOk getRow 2051521 976765 976833 := by
  decide +kernel

private theorem r_976833 : RangeOk getRow 2051521 976833 976902 := by
  decide +kernel

private theorem r_976902 : RangeOk getRow 2051521 976902 976971 := by
  decide +kernel

private theorem r_976971 : RangeOk getRow 2051521 976971 977039 := by
  decide +kernel

private theorem r_977039 : RangeOk getRow 2051521 977039 977107 := by
  decide +kernel

private theorem r_977107 : RangeOk getRow 2051521 977107 977175 := by
  decide +kernel

private theorem r_977175 : RangeOk getRow 2051521 977175 977243 := by
  decide +kernel

private theorem r_977243 : RangeOk getRow 2051521 977243 977309 := by
  decide +kernel

private theorem r_977309 : RangeOk getRow 2051521 977309 977375 := by
  decide +kernel

private theorem r_977375 : RangeOk getRow 2051521 977375 977440 := by
  decide +kernel

private theorem r_977440 : RangeOk getRow 2051521 977440 977506 := by
  decide +kernel

private theorem r_977506 : RangeOk getRow 2051521 977506 977574 := by
  decide +kernel

private theorem r_977574 : RangeOk getRow 2051521 977574 977640 := by
  decide +kernel

private theorem r_977640 : RangeOk getRow 2051521 977640 977706 := by
  decide +kernel

private theorem r_977706 : RangeOk getRow 2051521 977706 977773 := by
  decide +kernel

private theorem r_977773 : RangeOk getRow 2051521 977773 977841 := by
  decide +kernel

private theorem r_977841 : RangeOk getRow 2051521 977841 977909 := by
  decide +kernel

private theorem r_977909 : RangeOk getRow 2051521 977909 977976 := by
  decide +kernel

private theorem r_977976 : RangeOk getRow 2051521 977976 978043 := by
  decide +kernel

private theorem r_978043 : RangeOk getRow 2051521 978043 978112 := by
  decide +kernel

private theorem r_978112 : RangeOk getRow 2051521 978112 978180 := by
  decide +kernel

private theorem r_978180 : RangeOk getRow 2051521 978180 978246 := by
  decide +kernel

private theorem r_978246 : RangeOk getRow 2051521 978246 978313 := by
  decide +kernel

private theorem r_978313 : RangeOk getRow 2051521 978313 978379 := by
  decide +kernel

private theorem r_978379 : RangeOk getRow 2051521 978379 978447 := by
  decide +kernel

private theorem r_978447 : RangeOk getRow 2051521 978447 978514 := by
  decide +kernel

private theorem r_978514 : RangeOk getRow 2051521 978514 978583 := by
  decide +kernel

private theorem s_976352 : RangeOk getRow 2051521 976283 976352 := r_976283
private theorem s_976420 : RangeOk getRow 2051521 976283 976420 :=
  s_976352.append (by norm_num) r_976352
private theorem s_976489 : RangeOk getRow 2051521 976283 976489 :=
  s_976420.append (by norm_num) r_976420
private theorem s_976558 : RangeOk getRow 2051521 976283 976558 :=
  s_976489.append (by norm_num) r_976489
private theorem s_976626 : RangeOk getRow 2051521 976283 976626 :=
  s_976558.append (by norm_num) r_976558
private theorem s_976696 : RangeOk getRow 2051521 976283 976696 :=
  s_976626.append (by norm_num) r_976626
private theorem s_976765 : RangeOk getRow 2051521 976283 976765 :=
  s_976696.append (by norm_num) r_976696
private theorem s_976833 : RangeOk getRow 2051521 976283 976833 :=
  s_976765.append (by norm_num) r_976765
private theorem s_976902 : RangeOk getRow 2051521 976283 976902 :=
  s_976833.append (by norm_num) r_976833
private theorem s_976971 : RangeOk getRow 2051521 976283 976971 :=
  s_976902.append (by norm_num) r_976902
private theorem s_977039 : RangeOk getRow 2051521 976283 977039 :=
  s_976971.append (by norm_num) r_976971
private theorem s_977107 : RangeOk getRow 2051521 976283 977107 :=
  s_977039.append (by norm_num) r_977039
private theorem s_977175 : RangeOk getRow 2051521 976283 977175 :=
  s_977107.append (by norm_num) r_977107
private theorem s_977243 : RangeOk getRow 2051521 976283 977243 :=
  s_977175.append (by norm_num) r_977175
private theorem s_977309 : RangeOk getRow 2051521 976283 977309 :=
  s_977243.append (by norm_num) r_977243
private theorem s_977375 : RangeOk getRow 2051521 976283 977375 :=
  s_977309.append (by norm_num) r_977309
private theorem s_977440 : RangeOk getRow 2051521 976283 977440 :=
  s_977375.append (by norm_num) r_977375
private theorem s_977506 : RangeOk getRow 2051521 976283 977506 :=
  s_977440.append (by norm_num) r_977440
private theorem s_977574 : RangeOk getRow 2051521 976283 977574 :=
  s_977506.append (by norm_num) r_977506
private theorem s_977640 : RangeOk getRow 2051521 976283 977640 :=
  s_977574.append (by norm_num) r_977574
private theorem s_977706 : RangeOk getRow 2051521 976283 977706 :=
  s_977640.append (by norm_num) r_977640
private theorem s_977773 : RangeOk getRow 2051521 976283 977773 :=
  s_977706.append (by norm_num) r_977706
private theorem s_977841 : RangeOk getRow 2051521 976283 977841 :=
  s_977773.append (by norm_num) r_977773
private theorem s_977909 : RangeOk getRow 2051521 976283 977909 :=
  s_977841.append (by norm_num) r_977841
private theorem s_977976 : RangeOk getRow 2051521 976283 977976 :=
  s_977909.append (by norm_num) r_977909
private theorem s_978043 : RangeOk getRow 2051521 976283 978043 :=
  s_977976.append (by norm_num) r_977976
private theorem s_978112 : RangeOk getRow 2051521 976283 978112 :=
  s_978043.append (by norm_num) r_978043
private theorem s_978180 : RangeOk getRow 2051521 976283 978180 :=
  s_978112.append (by norm_num) r_978112
private theorem s_978246 : RangeOk getRow 2051521 976283 978246 :=
  s_978180.append (by norm_num) r_978180
private theorem s_978313 : RangeOk getRow 2051521 976283 978313 :=
  s_978246.append (by norm_num) r_978246
private theorem s_978379 : RangeOk getRow 2051521 976283 978379 :=
  s_978313.append (by norm_num) r_978313
private theorem s_978447 : RangeOk getRow 2051521 976283 978447 :=
  s_978379.append (by norm_num) r_978379
private theorem s_978514 : RangeOk getRow 2051521 976283 978514 :=
  s_978447.append (by norm_num) r_978447
private theorem s_978583 : RangeOk getRow 2051521 976283 978583 :=
  s_978514.append (by norm_num) r_978514

/-- Rows `[976283, 978583)` are valid. -/
theorem rangeOk_976283_978583 : RangeOk getRow 2051521 976283 978583 := s_978583

end Noperthedron.Solution
