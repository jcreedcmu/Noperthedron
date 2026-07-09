import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[84713, 86443). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_84713 : RangeOk getRow 2051521 84713 84777 := by
  decide +kernel

private theorem r_84777 : RangeOk getRow 2051521 84777 84841 := by
  decide +kernel

private theorem r_84841 : RangeOk getRow 2051521 84841 84905 := by
  decide +kernel

private theorem r_84905 : RangeOk getRow 2051521 84905 84969 := by
  decide +kernel

private theorem r_84969 : RangeOk getRow 2051521 84969 85033 := by
  decide +kernel

private theorem r_85033 : RangeOk getRow 2051521 85033 85097 := by
  decide +kernel

private theorem r_85097 : RangeOk getRow 2051521 85097 85161 := by
  decide +kernel

private theorem r_85161 : RangeOk getRow 2051521 85161 85225 := by
  decide +kernel

private theorem r_85225 : RangeOk getRow 2051521 85225 85289 := by
  decide +kernel

private theorem r_85289 : RangeOk getRow 2051521 85289 85353 := by
  decide +kernel

private theorem r_85353 : RangeOk getRow 2051521 85353 85417 := by
  decide +kernel

private theorem r_85417 : RangeOk getRow 2051521 85417 85481 := by
  decide +kernel

private theorem r_85481 : RangeOk getRow 2051521 85481 85546 := by
  decide +kernel

private theorem r_85546 : RangeOk getRow 2051521 85546 85611 := by
  decide +kernel

private theorem r_85611 : RangeOk getRow 2051521 85611 85675 := by
  decide +kernel

private theorem r_85675 : RangeOk getRow 2051521 85675 85739 := by
  decide +kernel

private theorem r_85739 : RangeOk getRow 2051521 85739 85803 := by
  decide +kernel

private theorem r_85803 : RangeOk getRow 2051521 85803 85867 := by
  decide +kernel

private theorem r_85867 : RangeOk getRow 2051521 85867 85931 := by
  decide +kernel

private theorem r_85931 : RangeOk getRow 2051521 85931 85995 := by
  decide +kernel

private theorem r_85995 : RangeOk getRow 2051521 85995 86059 := by
  decide +kernel

private theorem r_86059 : RangeOk getRow 2051521 86059 86123 := by
  decide +kernel

private theorem r_86123 : RangeOk getRow 2051521 86123 86187 := by
  decide +kernel

private theorem r_86187 : RangeOk getRow 2051521 86187 86251 := by
  decide +kernel

private theorem r_86251 : RangeOk getRow 2051521 86251 86315 := by
  decide +kernel

private theorem r_86315 : RangeOk getRow 2051521 86315 86379 := by
  decide +kernel

private theorem r_86379 : RangeOk getRow 2051521 86379 86443 := by
  decide +kernel

private theorem s_84777 : RangeOk getRow 2051521 84713 84777 := r_84713
private theorem s_84841 : RangeOk getRow 2051521 84713 84841 :=
  s_84777.append (by norm_num) r_84777
private theorem s_84905 : RangeOk getRow 2051521 84713 84905 :=
  s_84841.append (by norm_num) r_84841
private theorem s_84969 : RangeOk getRow 2051521 84713 84969 :=
  s_84905.append (by norm_num) r_84905
private theorem s_85033 : RangeOk getRow 2051521 84713 85033 :=
  s_84969.append (by norm_num) r_84969
private theorem s_85097 : RangeOk getRow 2051521 84713 85097 :=
  s_85033.append (by norm_num) r_85033
private theorem s_85161 : RangeOk getRow 2051521 84713 85161 :=
  s_85097.append (by norm_num) r_85097
private theorem s_85225 : RangeOk getRow 2051521 84713 85225 :=
  s_85161.append (by norm_num) r_85161
private theorem s_85289 : RangeOk getRow 2051521 84713 85289 :=
  s_85225.append (by norm_num) r_85225
private theorem s_85353 : RangeOk getRow 2051521 84713 85353 :=
  s_85289.append (by norm_num) r_85289
private theorem s_85417 : RangeOk getRow 2051521 84713 85417 :=
  s_85353.append (by norm_num) r_85353
private theorem s_85481 : RangeOk getRow 2051521 84713 85481 :=
  s_85417.append (by norm_num) r_85417
private theorem s_85546 : RangeOk getRow 2051521 84713 85546 :=
  s_85481.append (by norm_num) r_85481
private theorem s_85611 : RangeOk getRow 2051521 84713 85611 :=
  s_85546.append (by norm_num) r_85546
private theorem s_85675 : RangeOk getRow 2051521 84713 85675 :=
  s_85611.append (by norm_num) r_85611
private theorem s_85739 : RangeOk getRow 2051521 84713 85739 :=
  s_85675.append (by norm_num) r_85675
private theorem s_85803 : RangeOk getRow 2051521 84713 85803 :=
  s_85739.append (by norm_num) r_85739
private theorem s_85867 : RangeOk getRow 2051521 84713 85867 :=
  s_85803.append (by norm_num) r_85803
private theorem s_85931 : RangeOk getRow 2051521 84713 85931 :=
  s_85867.append (by norm_num) r_85867
private theorem s_85995 : RangeOk getRow 2051521 84713 85995 :=
  s_85931.append (by norm_num) r_85931
private theorem s_86059 : RangeOk getRow 2051521 84713 86059 :=
  s_85995.append (by norm_num) r_85995
private theorem s_86123 : RangeOk getRow 2051521 84713 86123 :=
  s_86059.append (by norm_num) r_86059
private theorem s_86187 : RangeOk getRow 2051521 84713 86187 :=
  s_86123.append (by norm_num) r_86123
private theorem s_86251 : RangeOk getRow 2051521 84713 86251 :=
  s_86187.append (by norm_num) r_86187
private theorem s_86315 : RangeOk getRow 2051521 84713 86315 :=
  s_86251.append (by norm_num) r_86251
private theorem s_86379 : RangeOk getRow 2051521 84713 86379 :=
  s_86315.append (by norm_num) r_86315
private theorem s_86443 : RangeOk getRow 2051521 84713 86443 :=
  s_86379.append (by norm_num) r_86379

/-- Rows `[84713, 86443)` are valid. -/
theorem rangeOk_84713_86443 : RangeOk getRow 2051521 84713 86443 := s_86443

end Noperthedron.Solution
