import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[198650, 200378). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_198650 : RangeOk getRow 2051521 198650 198714 := by
  decide +kernel

private theorem r_198714 : RangeOk getRow 2051521 198714 198778 := by
  decide +kernel

private theorem r_198778 : RangeOk getRow 2051521 198778 198842 := by
  decide +kernel

private theorem r_198842 : RangeOk getRow 2051521 198842 198906 := by
  decide +kernel

private theorem r_198906 : RangeOk getRow 2051521 198906 198970 := by
  decide +kernel

private theorem r_198970 : RangeOk getRow 2051521 198970 199034 := by
  decide +kernel

private theorem r_199034 : RangeOk getRow 2051521 199034 199098 := by
  decide +kernel

private theorem r_199098 : RangeOk getRow 2051521 199098 199162 := by
  decide +kernel

private theorem r_199162 : RangeOk getRow 2051521 199162 199226 := by
  decide +kernel

private theorem r_199226 : RangeOk getRow 2051521 199226 199290 := by
  decide +kernel

private theorem r_199290 : RangeOk getRow 2051521 199290 199354 := by
  decide +kernel

private theorem r_199354 : RangeOk getRow 2051521 199354 199418 := by
  decide +kernel

private theorem r_199418 : RangeOk getRow 2051521 199418 199482 := by
  decide +kernel

private theorem r_199482 : RangeOk getRow 2051521 199482 199546 := by
  decide +kernel

private theorem r_199546 : RangeOk getRow 2051521 199546 199610 := by
  decide +kernel

private theorem r_199610 : RangeOk getRow 2051521 199610 199674 := by
  decide +kernel

private theorem r_199674 : RangeOk getRow 2051521 199674 199738 := by
  decide +kernel

private theorem r_199738 : RangeOk getRow 2051521 199738 199802 := by
  decide +kernel

private theorem r_199802 : RangeOk getRow 2051521 199802 199866 := by
  decide +kernel

private theorem r_199866 : RangeOk getRow 2051521 199866 199930 := by
  decide +kernel

private theorem r_199930 : RangeOk getRow 2051521 199930 199994 := by
  decide +kernel

private theorem r_199994 : RangeOk getRow 2051521 199994 200058 := by
  decide +kernel

private theorem r_200058 : RangeOk getRow 2051521 200058 200122 := by
  decide +kernel

private theorem r_200122 : RangeOk getRow 2051521 200122 200186 := by
  decide +kernel

private theorem r_200186 : RangeOk getRow 2051521 200186 200250 := by
  decide +kernel

private theorem r_200250 : RangeOk getRow 2051521 200250 200314 := by
  decide +kernel

private theorem r_200314 : RangeOk getRow 2051521 200314 200378 := by
  decide +kernel

private theorem s_198714 : RangeOk getRow 2051521 198650 198714 := r_198650
private theorem s_198778 : RangeOk getRow 2051521 198650 198778 :=
  s_198714.append (by norm_num) r_198714
private theorem s_198842 : RangeOk getRow 2051521 198650 198842 :=
  s_198778.append (by norm_num) r_198778
private theorem s_198906 : RangeOk getRow 2051521 198650 198906 :=
  s_198842.append (by norm_num) r_198842
private theorem s_198970 : RangeOk getRow 2051521 198650 198970 :=
  s_198906.append (by norm_num) r_198906
private theorem s_199034 : RangeOk getRow 2051521 198650 199034 :=
  s_198970.append (by norm_num) r_198970
private theorem s_199098 : RangeOk getRow 2051521 198650 199098 :=
  s_199034.append (by norm_num) r_199034
private theorem s_199162 : RangeOk getRow 2051521 198650 199162 :=
  s_199098.append (by norm_num) r_199098
private theorem s_199226 : RangeOk getRow 2051521 198650 199226 :=
  s_199162.append (by norm_num) r_199162
private theorem s_199290 : RangeOk getRow 2051521 198650 199290 :=
  s_199226.append (by norm_num) r_199226
private theorem s_199354 : RangeOk getRow 2051521 198650 199354 :=
  s_199290.append (by norm_num) r_199290
private theorem s_199418 : RangeOk getRow 2051521 198650 199418 :=
  s_199354.append (by norm_num) r_199354
private theorem s_199482 : RangeOk getRow 2051521 198650 199482 :=
  s_199418.append (by norm_num) r_199418
private theorem s_199546 : RangeOk getRow 2051521 198650 199546 :=
  s_199482.append (by norm_num) r_199482
private theorem s_199610 : RangeOk getRow 2051521 198650 199610 :=
  s_199546.append (by norm_num) r_199546
private theorem s_199674 : RangeOk getRow 2051521 198650 199674 :=
  s_199610.append (by norm_num) r_199610
private theorem s_199738 : RangeOk getRow 2051521 198650 199738 :=
  s_199674.append (by norm_num) r_199674
private theorem s_199802 : RangeOk getRow 2051521 198650 199802 :=
  s_199738.append (by norm_num) r_199738
private theorem s_199866 : RangeOk getRow 2051521 198650 199866 :=
  s_199802.append (by norm_num) r_199802
private theorem s_199930 : RangeOk getRow 2051521 198650 199930 :=
  s_199866.append (by norm_num) r_199866
private theorem s_199994 : RangeOk getRow 2051521 198650 199994 :=
  s_199930.append (by norm_num) r_199930
private theorem s_200058 : RangeOk getRow 2051521 198650 200058 :=
  s_199994.append (by norm_num) r_199994
private theorem s_200122 : RangeOk getRow 2051521 198650 200122 :=
  s_200058.append (by norm_num) r_200058
private theorem s_200186 : RangeOk getRow 2051521 198650 200186 :=
  s_200122.append (by norm_num) r_200122
private theorem s_200250 : RangeOk getRow 2051521 198650 200250 :=
  s_200186.append (by norm_num) r_200186
private theorem s_200314 : RangeOk getRow 2051521 198650 200314 :=
  s_200250.append (by norm_num) r_200250
private theorem s_200378 : RangeOk getRow 2051521 198650 200378 :=
  s_200314.append (by norm_num) r_200314

/-- Rows `[198650, 200378)` are valid. -/
theorem rangeOk_198650_200378 : RangeOk getRow 2051521 198650 200378 := s_200378

end Noperthedron.Solution
