import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[76072, 77806). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_76072 : RangeOk getRow 2051521 76072 76139 := by
  decide +kernel

private theorem r_76139 : RangeOk getRow 2051521 76139 76203 := by
  decide +kernel

private theorem r_76203 : RangeOk getRow 2051521 76203 76267 := by
  decide +kernel

private theorem r_76267 : RangeOk getRow 2051521 76267 76331 := by
  decide +kernel

private theorem r_76331 : RangeOk getRow 2051521 76331 76395 := by
  decide +kernel

private theorem r_76395 : RangeOk getRow 2051521 76395 76459 := by
  decide +kernel

private theorem r_76459 : RangeOk getRow 2051521 76459 76524 := by
  decide +kernel

private theorem r_76524 : RangeOk getRow 2051521 76524 76588 := by
  decide +kernel

private theorem r_76588 : RangeOk getRow 2051521 76588 76652 := by
  decide +kernel

private theorem r_76652 : RangeOk getRow 2051521 76652 76716 := by
  decide +kernel

private theorem r_76716 : RangeOk getRow 2051521 76716 76780 := by
  decide +kernel

private theorem r_76780 : RangeOk getRow 2051521 76780 76844 := by
  decide +kernel

private theorem r_76844 : RangeOk getRow 2051521 76844 76908 := by
  decide +kernel

private theorem r_76908 : RangeOk getRow 2051521 76908 76973 := by
  decide +kernel

private theorem r_76973 : RangeOk getRow 2051521 76973 77037 := by
  decide +kernel

private theorem r_77037 : RangeOk getRow 2051521 77037 77101 := by
  decide +kernel

private theorem r_77101 : RangeOk getRow 2051521 77101 77165 := by
  decide +kernel

private theorem r_77165 : RangeOk getRow 2051521 77165 77229 := by
  decide +kernel

private theorem r_77229 : RangeOk getRow 2051521 77229 77293 := by
  decide +kernel

private theorem r_77293 : RangeOk getRow 2051521 77293 77357 := by
  decide +kernel

private theorem r_77357 : RangeOk getRow 2051521 77357 77422 := by
  decide +kernel

private theorem r_77422 : RangeOk getRow 2051521 77422 77486 := by
  decide +kernel

private theorem r_77486 : RangeOk getRow 2051521 77486 77550 := by
  decide +kernel

private theorem r_77550 : RangeOk getRow 2051521 77550 77614 := by
  decide +kernel

private theorem r_77614 : RangeOk getRow 2051521 77614 77678 := by
  decide +kernel

private theorem r_77678 : RangeOk getRow 2051521 77678 77742 := by
  decide +kernel

private theorem r_77742 : RangeOk getRow 2051521 77742 77806 := by
  decide +kernel

private theorem s_76139 : RangeOk getRow 2051521 76072 76139 := r_76072
private theorem s_76203 : RangeOk getRow 2051521 76072 76203 :=
  s_76139.append (by norm_num) r_76139
private theorem s_76267 : RangeOk getRow 2051521 76072 76267 :=
  s_76203.append (by norm_num) r_76203
private theorem s_76331 : RangeOk getRow 2051521 76072 76331 :=
  s_76267.append (by norm_num) r_76267
private theorem s_76395 : RangeOk getRow 2051521 76072 76395 :=
  s_76331.append (by norm_num) r_76331
private theorem s_76459 : RangeOk getRow 2051521 76072 76459 :=
  s_76395.append (by norm_num) r_76395
private theorem s_76524 : RangeOk getRow 2051521 76072 76524 :=
  s_76459.append (by norm_num) r_76459
private theorem s_76588 : RangeOk getRow 2051521 76072 76588 :=
  s_76524.append (by norm_num) r_76524
private theorem s_76652 : RangeOk getRow 2051521 76072 76652 :=
  s_76588.append (by norm_num) r_76588
private theorem s_76716 : RangeOk getRow 2051521 76072 76716 :=
  s_76652.append (by norm_num) r_76652
private theorem s_76780 : RangeOk getRow 2051521 76072 76780 :=
  s_76716.append (by norm_num) r_76716
private theorem s_76844 : RangeOk getRow 2051521 76072 76844 :=
  s_76780.append (by norm_num) r_76780
private theorem s_76908 : RangeOk getRow 2051521 76072 76908 :=
  s_76844.append (by norm_num) r_76844
private theorem s_76973 : RangeOk getRow 2051521 76072 76973 :=
  s_76908.append (by norm_num) r_76908
private theorem s_77037 : RangeOk getRow 2051521 76072 77037 :=
  s_76973.append (by norm_num) r_76973
private theorem s_77101 : RangeOk getRow 2051521 76072 77101 :=
  s_77037.append (by norm_num) r_77037
private theorem s_77165 : RangeOk getRow 2051521 76072 77165 :=
  s_77101.append (by norm_num) r_77101
private theorem s_77229 : RangeOk getRow 2051521 76072 77229 :=
  s_77165.append (by norm_num) r_77165
private theorem s_77293 : RangeOk getRow 2051521 76072 77293 :=
  s_77229.append (by norm_num) r_77229
private theorem s_77357 : RangeOk getRow 2051521 76072 77357 :=
  s_77293.append (by norm_num) r_77293
private theorem s_77422 : RangeOk getRow 2051521 76072 77422 :=
  s_77357.append (by norm_num) r_77357
private theorem s_77486 : RangeOk getRow 2051521 76072 77486 :=
  s_77422.append (by norm_num) r_77422
private theorem s_77550 : RangeOk getRow 2051521 76072 77550 :=
  s_77486.append (by norm_num) r_77486
private theorem s_77614 : RangeOk getRow 2051521 76072 77614 :=
  s_77550.append (by norm_num) r_77550
private theorem s_77678 : RangeOk getRow 2051521 76072 77678 :=
  s_77614.append (by norm_num) r_77614
private theorem s_77742 : RangeOk getRow 2051521 76072 77742 :=
  s_77678.append (by norm_num) r_77678
private theorem s_77806 : RangeOk getRow 2051521 76072 77806 :=
  s_77742.append (by norm_num) r_77742

/-- Rows `[76072, 77806)` are valid. -/
theorem rangeOk_76072_77806 : RangeOk getRow 2051521 76072 77806 := s_77806

end Noperthedron.Solution
