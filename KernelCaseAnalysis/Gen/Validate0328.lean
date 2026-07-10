import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[789904, 792275). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_789904 : RangeOk getRow 2051521 789904 789973 := by
  decide +kernel

private theorem r_789973 : RangeOk getRow 2051521 789973 790040 := by
  decide +kernel

private theorem r_790040 : RangeOk getRow 2051521 790040 790108 := by
  decide +kernel

private theorem r_790108 : RangeOk getRow 2051521 790108 790176 := by
  decide +kernel

private theorem r_790176 : RangeOk getRow 2051521 790176 790244 := by
  decide +kernel

private theorem r_790244 : RangeOk getRow 2051521 790244 790311 := by
  decide +kernel

private theorem r_790311 : RangeOk getRow 2051521 790311 790379 := by
  decide +kernel

private theorem r_790379 : RangeOk getRow 2051521 790379 790446 := by
  decide +kernel

private theorem r_790446 : RangeOk getRow 2051521 790446 790513 := by
  decide +kernel

private theorem r_790513 : RangeOk getRow 2051521 790513 790580 := by
  decide +kernel

private theorem r_790580 : RangeOk getRow 2051521 790580 790646 := by
  decide +kernel

private theorem r_790646 : RangeOk getRow 2051521 790646 790711 := by
  decide +kernel

private theorem r_790711 : RangeOk getRow 2051521 790711 790776 := by
  decide +kernel

private theorem r_790776 : RangeOk getRow 2051521 790776 790845 := by
  decide +kernel

private theorem r_790845 : RangeOk getRow 2051521 790845 790914 := by
  decide +kernel

private theorem r_790914 : RangeOk getRow 2051521 790914 790988 := by
  decide +kernel

private theorem r_790988 : RangeOk getRow 2051521 790988 791061 := by
  decide +kernel

private theorem r_791061 : RangeOk getRow 2051521 791061 791130 := by
  decide +kernel

private theorem r_791130 : RangeOk getRow 2051521 791130 791199 := by
  decide +kernel

private theorem r_791199 : RangeOk getRow 2051521 791199 791267 := by
  decide +kernel

private theorem r_791267 : RangeOk getRow 2051521 791267 791334 := by
  decide +kernel

private theorem r_791334 : RangeOk getRow 2051521 791334 791402 := by
  decide +kernel

private theorem r_791402 : RangeOk getRow 2051521 791402 791468 := by
  decide +kernel

private theorem r_791468 : RangeOk getRow 2051521 791468 791534 := by
  decide +kernel

private theorem r_791534 : RangeOk getRow 2051521 791534 791600 := by
  decide +kernel

private theorem r_791600 : RangeOk getRow 2051521 791600 791668 := by
  decide +kernel

private theorem r_791668 : RangeOk getRow 2051521 791668 791734 := by
  decide +kernel

private theorem r_791734 : RangeOk getRow 2051521 791734 791802 := by
  decide +kernel

private theorem r_791802 : RangeOk getRow 2051521 791802 791868 := by
  decide +kernel

private theorem r_791868 : RangeOk getRow 2051521 791868 791936 := by
  decide +kernel

private theorem r_791936 : RangeOk getRow 2051521 791936 792005 := by
  decide +kernel

private theorem r_792005 : RangeOk getRow 2051521 792005 792071 := by
  decide +kernel

private theorem r_792071 : RangeOk getRow 2051521 792071 792140 := by
  decide +kernel

private theorem r_792140 : RangeOk getRow 2051521 792140 792206 := by
  decide +kernel

private theorem r_792206 : RangeOk getRow 2051521 792206 792275 := by
  decide +kernel

private theorem s_789973 : RangeOk getRow 2051521 789904 789973 := r_789904
private theorem s_790040 : RangeOk getRow 2051521 789904 790040 :=
  s_789973.append (by norm_num) r_789973
private theorem s_790108 : RangeOk getRow 2051521 789904 790108 :=
  s_790040.append (by norm_num) r_790040
private theorem s_790176 : RangeOk getRow 2051521 789904 790176 :=
  s_790108.append (by norm_num) r_790108
private theorem s_790244 : RangeOk getRow 2051521 789904 790244 :=
  s_790176.append (by norm_num) r_790176
private theorem s_790311 : RangeOk getRow 2051521 789904 790311 :=
  s_790244.append (by norm_num) r_790244
private theorem s_790379 : RangeOk getRow 2051521 789904 790379 :=
  s_790311.append (by norm_num) r_790311
private theorem s_790446 : RangeOk getRow 2051521 789904 790446 :=
  s_790379.append (by norm_num) r_790379
private theorem s_790513 : RangeOk getRow 2051521 789904 790513 :=
  s_790446.append (by norm_num) r_790446
private theorem s_790580 : RangeOk getRow 2051521 789904 790580 :=
  s_790513.append (by norm_num) r_790513
private theorem s_790646 : RangeOk getRow 2051521 789904 790646 :=
  s_790580.append (by norm_num) r_790580
private theorem s_790711 : RangeOk getRow 2051521 789904 790711 :=
  s_790646.append (by norm_num) r_790646
private theorem s_790776 : RangeOk getRow 2051521 789904 790776 :=
  s_790711.append (by norm_num) r_790711
private theorem s_790845 : RangeOk getRow 2051521 789904 790845 :=
  s_790776.append (by norm_num) r_790776
private theorem s_790914 : RangeOk getRow 2051521 789904 790914 :=
  s_790845.append (by norm_num) r_790845
private theorem s_790988 : RangeOk getRow 2051521 789904 790988 :=
  s_790914.append (by norm_num) r_790914
private theorem s_791061 : RangeOk getRow 2051521 789904 791061 :=
  s_790988.append (by norm_num) r_790988
private theorem s_791130 : RangeOk getRow 2051521 789904 791130 :=
  s_791061.append (by norm_num) r_791061
private theorem s_791199 : RangeOk getRow 2051521 789904 791199 :=
  s_791130.append (by norm_num) r_791130
private theorem s_791267 : RangeOk getRow 2051521 789904 791267 :=
  s_791199.append (by norm_num) r_791199
private theorem s_791334 : RangeOk getRow 2051521 789904 791334 :=
  s_791267.append (by norm_num) r_791267
private theorem s_791402 : RangeOk getRow 2051521 789904 791402 :=
  s_791334.append (by norm_num) r_791334
private theorem s_791468 : RangeOk getRow 2051521 789904 791468 :=
  s_791402.append (by norm_num) r_791402
private theorem s_791534 : RangeOk getRow 2051521 789904 791534 :=
  s_791468.append (by norm_num) r_791468
private theorem s_791600 : RangeOk getRow 2051521 789904 791600 :=
  s_791534.append (by norm_num) r_791534
private theorem s_791668 : RangeOk getRow 2051521 789904 791668 :=
  s_791600.append (by norm_num) r_791600
private theorem s_791734 : RangeOk getRow 2051521 789904 791734 :=
  s_791668.append (by norm_num) r_791668
private theorem s_791802 : RangeOk getRow 2051521 789904 791802 :=
  s_791734.append (by norm_num) r_791734
private theorem s_791868 : RangeOk getRow 2051521 789904 791868 :=
  s_791802.append (by norm_num) r_791802
private theorem s_791936 : RangeOk getRow 2051521 789904 791936 :=
  s_791868.append (by norm_num) r_791868
private theorem s_792005 : RangeOk getRow 2051521 789904 792005 :=
  s_791936.append (by norm_num) r_791936
private theorem s_792071 : RangeOk getRow 2051521 789904 792071 :=
  s_792005.append (by norm_num) r_792005
private theorem s_792140 : RangeOk getRow 2051521 789904 792140 :=
  s_792071.append (by norm_num) r_792071
private theorem s_792206 : RangeOk getRow 2051521 789904 792206 :=
  s_792140.append (by norm_num) r_792140
private theorem s_792275 : RangeOk getRow 2051521 789904 792275 :=
  s_792206.append (by norm_num) r_792206

/-- Rows `[789904, 792275)` are valid. -/
theorem rangeOk_789904_792275 : RangeOk getRow 2051521 789904 792275 := s_792275

end Noperthedron.Solution
