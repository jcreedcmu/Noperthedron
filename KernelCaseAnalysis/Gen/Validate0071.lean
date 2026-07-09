import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[152808, 154537). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_152808 : RangeOk getRow 2051521 152808 152872 := by
  decide +kernel

private theorem r_152872 : RangeOk getRow 2051521 152872 152936 := by
  decide +kernel

private theorem r_152936 : RangeOk getRow 2051521 152936 152996 := by
  decide +kernel

private theorem r_152996 : RangeOk getRow 2051521 152996 153060 := by
  decide +kernel

private theorem r_153060 : RangeOk getRow 2051521 153060 153124 := by
  decide +kernel

private theorem r_153124 : RangeOk getRow 2051521 153124 153188 := by
  decide +kernel

private theorem r_153188 : RangeOk getRow 2051521 153188 153252 := by
  decide +kernel

private theorem r_153252 : RangeOk getRow 2051521 153252 153316 := by
  decide +kernel

private theorem r_153316 : RangeOk getRow 2051521 153316 153380 := by
  decide +kernel

private theorem r_153380 : RangeOk getRow 2051521 153380 153444 := by
  decide +kernel

private theorem r_153444 : RangeOk getRow 2051521 153444 153508 := by
  decide +kernel

private theorem r_153508 : RangeOk getRow 2051521 153508 153572 := by
  decide +kernel

private theorem r_153572 : RangeOk getRow 2051521 153572 153636 := by
  decide +kernel

private theorem r_153636 : RangeOk getRow 2051521 153636 153700 := by
  decide +kernel

private theorem r_153700 : RangeOk getRow 2051521 153700 153765 := by
  decide +kernel

private theorem r_153765 : RangeOk getRow 2051521 153765 153829 := by
  decide +kernel

private theorem r_153829 : RangeOk getRow 2051521 153829 153894 := by
  decide +kernel

private theorem r_153894 : RangeOk getRow 2051521 153894 153958 := by
  decide +kernel

private theorem r_153958 : RangeOk getRow 2051521 153958 154022 := by
  decide +kernel

private theorem r_154022 : RangeOk getRow 2051521 154022 154086 := by
  decide +kernel

private theorem r_154086 : RangeOk getRow 2051521 154086 154150 := by
  decide +kernel

private theorem r_154150 : RangeOk getRow 2051521 154150 154215 := by
  decide +kernel

private theorem r_154215 : RangeOk getRow 2051521 154215 154279 := by
  decide +kernel

private theorem r_154279 : RangeOk getRow 2051521 154279 154344 := by
  decide +kernel

private theorem r_154344 : RangeOk getRow 2051521 154344 154409 := by
  decide +kernel

private theorem r_154409 : RangeOk getRow 2051521 154409 154473 := by
  decide +kernel

private theorem r_154473 : RangeOk getRow 2051521 154473 154537 := by
  decide +kernel

private theorem s_152872 : RangeOk getRow 2051521 152808 152872 := r_152808
private theorem s_152936 : RangeOk getRow 2051521 152808 152936 :=
  s_152872.append (by norm_num) r_152872
private theorem s_152996 : RangeOk getRow 2051521 152808 152996 :=
  s_152936.append (by norm_num) r_152936
private theorem s_153060 : RangeOk getRow 2051521 152808 153060 :=
  s_152996.append (by norm_num) r_152996
private theorem s_153124 : RangeOk getRow 2051521 152808 153124 :=
  s_153060.append (by norm_num) r_153060
private theorem s_153188 : RangeOk getRow 2051521 152808 153188 :=
  s_153124.append (by norm_num) r_153124
private theorem s_153252 : RangeOk getRow 2051521 152808 153252 :=
  s_153188.append (by norm_num) r_153188
private theorem s_153316 : RangeOk getRow 2051521 152808 153316 :=
  s_153252.append (by norm_num) r_153252
private theorem s_153380 : RangeOk getRow 2051521 152808 153380 :=
  s_153316.append (by norm_num) r_153316
private theorem s_153444 : RangeOk getRow 2051521 152808 153444 :=
  s_153380.append (by norm_num) r_153380
private theorem s_153508 : RangeOk getRow 2051521 152808 153508 :=
  s_153444.append (by norm_num) r_153444
private theorem s_153572 : RangeOk getRow 2051521 152808 153572 :=
  s_153508.append (by norm_num) r_153508
private theorem s_153636 : RangeOk getRow 2051521 152808 153636 :=
  s_153572.append (by norm_num) r_153572
private theorem s_153700 : RangeOk getRow 2051521 152808 153700 :=
  s_153636.append (by norm_num) r_153636
private theorem s_153765 : RangeOk getRow 2051521 152808 153765 :=
  s_153700.append (by norm_num) r_153700
private theorem s_153829 : RangeOk getRow 2051521 152808 153829 :=
  s_153765.append (by norm_num) r_153765
private theorem s_153894 : RangeOk getRow 2051521 152808 153894 :=
  s_153829.append (by norm_num) r_153829
private theorem s_153958 : RangeOk getRow 2051521 152808 153958 :=
  s_153894.append (by norm_num) r_153894
private theorem s_154022 : RangeOk getRow 2051521 152808 154022 :=
  s_153958.append (by norm_num) r_153958
private theorem s_154086 : RangeOk getRow 2051521 152808 154086 :=
  s_154022.append (by norm_num) r_154022
private theorem s_154150 : RangeOk getRow 2051521 152808 154150 :=
  s_154086.append (by norm_num) r_154086
private theorem s_154215 : RangeOk getRow 2051521 152808 154215 :=
  s_154150.append (by norm_num) r_154150
private theorem s_154279 : RangeOk getRow 2051521 152808 154279 :=
  s_154215.append (by norm_num) r_154215
private theorem s_154344 : RangeOk getRow 2051521 152808 154344 :=
  s_154279.append (by norm_num) r_154279
private theorem s_154409 : RangeOk getRow 2051521 152808 154409 :=
  s_154344.append (by norm_num) r_154344
private theorem s_154473 : RangeOk getRow 2051521 152808 154473 :=
  s_154409.append (by norm_num) r_154409
private theorem s_154537 : RangeOk getRow 2051521 152808 154537 :=
  s_154473.append (by norm_num) r_154473

/-- Rows `[152808, 154537)` are valid. -/
theorem rangeOk_152808_154537 : RangeOk getRow 2051521 152808 154537 := s_154537

end Noperthedron.Solution
