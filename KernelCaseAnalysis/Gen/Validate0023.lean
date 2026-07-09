import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[44700, 46434). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_44700 : RangeOk getRow 2051521 44700 44764 := by
  decide +kernel

private theorem r_44764 : RangeOk getRow 2051521 44764 44828 := by
  decide +kernel

private theorem r_44828 : RangeOk getRow 2051521 44828 44892 := by
  decide +kernel

private theorem r_44892 : RangeOk getRow 2051521 44892 44956 := by
  decide +kernel

private theorem r_44956 : RangeOk getRow 2051521 44956 45021 := by
  decide +kernel

private theorem r_45021 : RangeOk getRow 2051521 45021 45085 := by
  decide +kernel

private theorem r_45085 : RangeOk getRow 2051521 45085 45149 := by
  decide +kernel

private theorem r_45149 : RangeOk getRow 2051521 45149 45213 := by
  decide +kernel

private theorem r_45213 : RangeOk getRow 2051521 45213 45277 := by
  decide +kernel

private theorem r_45277 : RangeOk getRow 2051521 45277 45341 := by
  decide +kernel

private theorem r_45341 : RangeOk getRow 2051521 45341 45405 := by
  decide +kernel

private theorem r_45405 : RangeOk getRow 2051521 45405 45470 := by
  decide +kernel

private theorem r_45470 : RangeOk getRow 2051521 45470 45534 := by
  decide +kernel

private theorem r_45534 : RangeOk getRow 2051521 45534 45598 := by
  decide +kernel

private theorem r_45598 : RangeOk getRow 2051521 45598 45662 := by
  decide +kernel

private theorem r_45662 : RangeOk getRow 2051521 45662 45726 := by
  decide +kernel

private theorem r_45726 : RangeOk getRow 2051521 45726 45790 := by
  decide +kernel

private theorem r_45790 : RangeOk getRow 2051521 45790 45854 := by
  decide +kernel

private theorem r_45854 : RangeOk getRow 2051521 45854 45920 := by
  decide +kernel

private theorem r_45920 : RangeOk getRow 2051521 45920 45984 := by
  decide +kernel

private theorem r_45984 : RangeOk getRow 2051521 45984 46048 := by
  decide +kernel

private theorem r_46048 : RangeOk getRow 2051521 46048 46112 := by
  decide +kernel

private theorem r_46112 : RangeOk getRow 2051521 46112 46176 := by
  decide +kernel

private theorem r_46176 : RangeOk getRow 2051521 46176 46240 := by
  decide +kernel

private theorem r_46240 : RangeOk getRow 2051521 46240 46304 := by
  decide +kernel

private theorem r_46304 : RangeOk getRow 2051521 46304 46370 := by
  decide +kernel

private theorem r_46370 : RangeOk getRow 2051521 46370 46434 := by
  decide +kernel

private theorem s_44764 : RangeOk getRow 2051521 44700 44764 := r_44700
private theorem s_44828 : RangeOk getRow 2051521 44700 44828 :=
  s_44764.append (by norm_num) r_44764
private theorem s_44892 : RangeOk getRow 2051521 44700 44892 :=
  s_44828.append (by norm_num) r_44828
private theorem s_44956 : RangeOk getRow 2051521 44700 44956 :=
  s_44892.append (by norm_num) r_44892
private theorem s_45021 : RangeOk getRow 2051521 44700 45021 :=
  s_44956.append (by norm_num) r_44956
private theorem s_45085 : RangeOk getRow 2051521 44700 45085 :=
  s_45021.append (by norm_num) r_45021
private theorem s_45149 : RangeOk getRow 2051521 44700 45149 :=
  s_45085.append (by norm_num) r_45085
private theorem s_45213 : RangeOk getRow 2051521 44700 45213 :=
  s_45149.append (by norm_num) r_45149
private theorem s_45277 : RangeOk getRow 2051521 44700 45277 :=
  s_45213.append (by norm_num) r_45213
private theorem s_45341 : RangeOk getRow 2051521 44700 45341 :=
  s_45277.append (by norm_num) r_45277
private theorem s_45405 : RangeOk getRow 2051521 44700 45405 :=
  s_45341.append (by norm_num) r_45341
private theorem s_45470 : RangeOk getRow 2051521 44700 45470 :=
  s_45405.append (by norm_num) r_45405
private theorem s_45534 : RangeOk getRow 2051521 44700 45534 :=
  s_45470.append (by norm_num) r_45470
private theorem s_45598 : RangeOk getRow 2051521 44700 45598 :=
  s_45534.append (by norm_num) r_45534
private theorem s_45662 : RangeOk getRow 2051521 44700 45662 :=
  s_45598.append (by norm_num) r_45598
private theorem s_45726 : RangeOk getRow 2051521 44700 45726 :=
  s_45662.append (by norm_num) r_45662
private theorem s_45790 : RangeOk getRow 2051521 44700 45790 :=
  s_45726.append (by norm_num) r_45726
private theorem s_45854 : RangeOk getRow 2051521 44700 45854 :=
  s_45790.append (by norm_num) r_45790
private theorem s_45920 : RangeOk getRow 2051521 44700 45920 :=
  s_45854.append (by norm_num) r_45854
private theorem s_45984 : RangeOk getRow 2051521 44700 45984 :=
  s_45920.append (by norm_num) r_45920
private theorem s_46048 : RangeOk getRow 2051521 44700 46048 :=
  s_45984.append (by norm_num) r_45984
private theorem s_46112 : RangeOk getRow 2051521 44700 46112 :=
  s_46048.append (by norm_num) r_46048
private theorem s_46176 : RangeOk getRow 2051521 44700 46176 :=
  s_46112.append (by norm_num) r_46112
private theorem s_46240 : RangeOk getRow 2051521 44700 46240 :=
  s_46176.append (by norm_num) r_46176
private theorem s_46304 : RangeOk getRow 2051521 44700 46304 :=
  s_46240.append (by norm_num) r_46240
private theorem s_46370 : RangeOk getRow 2051521 44700 46370 :=
  s_46304.append (by norm_num) r_46304
private theorem s_46434 : RangeOk getRow 2051521 44700 46434 :=
  s_46370.append (by norm_num) r_46370

/-- Rows `[44700, 46434)` are valid. -/
theorem rangeOk_44700_46434 : RangeOk getRow 2051521 44700 46434 := s_46434

end Noperthedron.Solution
