import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[82985, 84713). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_82985 : RangeOk getRow 2051521 82985 83049 := by
  decide +kernel

private theorem r_83049 : RangeOk getRow 2051521 83049 83113 := by
  decide +kernel

private theorem r_83113 : RangeOk getRow 2051521 83113 83177 := by
  decide +kernel

private theorem r_83177 : RangeOk getRow 2051521 83177 83241 := by
  decide +kernel

private theorem r_83241 : RangeOk getRow 2051521 83241 83305 := by
  decide +kernel

private theorem r_83305 : RangeOk getRow 2051521 83305 83369 := by
  decide +kernel

private theorem r_83369 : RangeOk getRow 2051521 83369 83433 := by
  decide +kernel

private theorem r_83433 : RangeOk getRow 2051521 83433 83497 := by
  decide +kernel

private theorem r_83497 : RangeOk getRow 2051521 83497 83561 := by
  decide +kernel

private theorem r_83561 : RangeOk getRow 2051521 83561 83625 := by
  decide +kernel

private theorem r_83625 : RangeOk getRow 2051521 83625 83689 := by
  decide +kernel

private theorem r_83689 : RangeOk getRow 2051521 83689 83753 := by
  decide +kernel

private theorem r_83753 : RangeOk getRow 2051521 83753 83817 := by
  decide +kernel

private theorem r_83817 : RangeOk getRow 2051521 83817 83881 := by
  decide +kernel

private theorem r_83881 : RangeOk getRow 2051521 83881 83945 := by
  decide +kernel

private theorem r_83945 : RangeOk getRow 2051521 83945 84009 := by
  decide +kernel

private theorem r_84009 : RangeOk getRow 2051521 84009 84073 := by
  decide +kernel

private theorem r_84073 : RangeOk getRow 2051521 84073 84137 := by
  decide +kernel

private theorem r_84137 : RangeOk getRow 2051521 84137 84201 := by
  decide +kernel

private theorem r_84201 : RangeOk getRow 2051521 84201 84265 := by
  decide +kernel

private theorem r_84265 : RangeOk getRow 2051521 84265 84329 := by
  decide +kernel

private theorem r_84329 : RangeOk getRow 2051521 84329 84393 := by
  decide +kernel

private theorem r_84393 : RangeOk getRow 2051521 84393 84457 := by
  decide +kernel

private theorem r_84457 : RangeOk getRow 2051521 84457 84521 := by
  decide +kernel

private theorem r_84521 : RangeOk getRow 2051521 84521 84585 := by
  decide +kernel

private theorem r_84585 : RangeOk getRow 2051521 84585 84649 := by
  decide +kernel

private theorem r_84649 : RangeOk getRow 2051521 84649 84713 := by
  decide +kernel

private theorem s_83049 : RangeOk getRow 2051521 82985 83049 := r_82985
private theorem s_83113 : RangeOk getRow 2051521 82985 83113 :=
  s_83049.append (by norm_num) r_83049
private theorem s_83177 : RangeOk getRow 2051521 82985 83177 :=
  s_83113.append (by norm_num) r_83113
private theorem s_83241 : RangeOk getRow 2051521 82985 83241 :=
  s_83177.append (by norm_num) r_83177
private theorem s_83305 : RangeOk getRow 2051521 82985 83305 :=
  s_83241.append (by norm_num) r_83241
private theorem s_83369 : RangeOk getRow 2051521 82985 83369 :=
  s_83305.append (by norm_num) r_83305
private theorem s_83433 : RangeOk getRow 2051521 82985 83433 :=
  s_83369.append (by norm_num) r_83369
private theorem s_83497 : RangeOk getRow 2051521 82985 83497 :=
  s_83433.append (by norm_num) r_83433
private theorem s_83561 : RangeOk getRow 2051521 82985 83561 :=
  s_83497.append (by norm_num) r_83497
private theorem s_83625 : RangeOk getRow 2051521 82985 83625 :=
  s_83561.append (by norm_num) r_83561
private theorem s_83689 : RangeOk getRow 2051521 82985 83689 :=
  s_83625.append (by norm_num) r_83625
private theorem s_83753 : RangeOk getRow 2051521 82985 83753 :=
  s_83689.append (by norm_num) r_83689
private theorem s_83817 : RangeOk getRow 2051521 82985 83817 :=
  s_83753.append (by norm_num) r_83753
private theorem s_83881 : RangeOk getRow 2051521 82985 83881 :=
  s_83817.append (by norm_num) r_83817
private theorem s_83945 : RangeOk getRow 2051521 82985 83945 :=
  s_83881.append (by norm_num) r_83881
private theorem s_84009 : RangeOk getRow 2051521 82985 84009 :=
  s_83945.append (by norm_num) r_83945
private theorem s_84073 : RangeOk getRow 2051521 82985 84073 :=
  s_84009.append (by norm_num) r_84009
private theorem s_84137 : RangeOk getRow 2051521 82985 84137 :=
  s_84073.append (by norm_num) r_84073
private theorem s_84201 : RangeOk getRow 2051521 82985 84201 :=
  s_84137.append (by norm_num) r_84137
private theorem s_84265 : RangeOk getRow 2051521 82985 84265 :=
  s_84201.append (by norm_num) r_84201
private theorem s_84329 : RangeOk getRow 2051521 82985 84329 :=
  s_84265.append (by norm_num) r_84265
private theorem s_84393 : RangeOk getRow 2051521 82985 84393 :=
  s_84329.append (by norm_num) r_84329
private theorem s_84457 : RangeOk getRow 2051521 82985 84457 :=
  s_84393.append (by norm_num) r_84393
private theorem s_84521 : RangeOk getRow 2051521 82985 84521 :=
  s_84457.append (by norm_num) r_84457
private theorem s_84585 : RangeOk getRow 2051521 82985 84585 :=
  s_84521.append (by norm_num) r_84521
private theorem s_84649 : RangeOk getRow 2051521 82985 84649 :=
  s_84585.append (by norm_num) r_84585
private theorem s_84713 : RangeOk getRow 2051521 82985 84713 :=
  s_84649.append (by norm_num) r_84649

/-- Rows `[82985, 84713)` are valid. -/
theorem rangeOk_82985_84713 : RangeOk getRow 2051521 82985 84713 := s_84713

end Noperthedron.Solution
