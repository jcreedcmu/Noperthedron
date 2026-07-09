import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[411765, 414220). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_411765 : RangeOk getRow 2051521 411765 411833 := by
  decide +kernel

private theorem r_411833 : RangeOk getRow 2051521 411833 411903 := by
  decide +kernel

private theorem r_411903 : RangeOk getRow 2051521 411903 411971 := by
  decide +kernel

private theorem r_411971 : RangeOk getRow 2051521 411971 412039 := by
  decide +kernel

private theorem r_412039 : RangeOk getRow 2051521 412039 412108 := by
  decide +kernel

private theorem r_412108 : RangeOk getRow 2051521 412108 412177 := by
  decide +kernel

private theorem r_412177 : RangeOk getRow 2051521 412177 412246 := by
  decide +kernel

private theorem r_412246 : RangeOk getRow 2051521 412246 412316 := by
  decide +kernel

private theorem r_412316 : RangeOk getRow 2051521 412316 412385 := by
  decide +kernel

private theorem r_412385 : RangeOk getRow 2051521 412385 412453 := by
  decide +kernel

private theorem r_412453 : RangeOk getRow 2051521 412453 412521 := by
  decide +kernel

private theorem r_412521 : RangeOk getRow 2051521 412521 412589 := by
  decide +kernel

private theorem r_412589 : RangeOk getRow 2051521 412589 412658 := by
  decide +kernel

private theorem r_412658 : RangeOk getRow 2051521 412658 412727 := by
  decide +kernel

private theorem r_412727 : RangeOk getRow 2051521 412727 412795 := by
  decide +kernel

private theorem r_412795 : RangeOk getRow 2051521 412795 412864 := by
  decide +kernel

private theorem r_412864 : RangeOk getRow 2051521 412864 412933 := by
  decide +kernel

private theorem r_412933 : RangeOk getRow 2051521 412933 413000 := by
  decide +kernel

private theorem r_413000 : RangeOk getRow 2051521 413000 413068 := by
  decide +kernel

private theorem r_413068 : RangeOk getRow 2051521 413068 413136 := by
  decide +kernel

private theorem r_413136 : RangeOk getRow 2051521 413136 413202 := by
  decide +kernel

private theorem r_413202 : RangeOk getRow 2051521 413202 413271 := by
  decide +kernel

private theorem r_413271 : RangeOk getRow 2051521 413271 413341 := by
  decide +kernel

private theorem r_413341 : RangeOk getRow 2051521 413341 413410 := by
  decide +kernel

private theorem r_413410 : RangeOk getRow 2051521 413410 413474 := by
  decide +kernel

private theorem r_413474 : RangeOk getRow 2051521 413474 413538 := by
  decide +kernel

private theorem r_413538 : RangeOk getRow 2051521 413538 413604 := by
  decide +kernel

private theorem r_413604 : RangeOk getRow 2051521 413604 413673 := by
  decide +kernel

private theorem r_413673 : RangeOk getRow 2051521 413673 413742 := by
  decide +kernel

private theorem r_413742 : RangeOk getRow 2051521 413742 413811 := by
  decide +kernel

private theorem r_413811 : RangeOk getRow 2051521 413811 413879 := by
  decide +kernel

private theorem r_413879 : RangeOk getRow 2051521 413879 413947 := by
  decide +kernel

private theorem r_413947 : RangeOk getRow 2051521 413947 414014 := by
  decide +kernel

private theorem r_414014 : RangeOk getRow 2051521 414014 414081 := by
  decide +kernel

private theorem r_414081 : RangeOk getRow 2051521 414081 414149 := by
  decide +kernel

private theorem r_414149 : RangeOk getRow 2051521 414149 414220 := by
  decide +kernel

private theorem s_411833 : RangeOk getRow 2051521 411765 411833 := r_411765
private theorem s_411903 : RangeOk getRow 2051521 411765 411903 :=
  s_411833.append (by norm_num) r_411833
private theorem s_411971 : RangeOk getRow 2051521 411765 411971 :=
  s_411903.append (by norm_num) r_411903
private theorem s_412039 : RangeOk getRow 2051521 411765 412039 :=
  s_411971.append (by norm_num) r_411971
private theorem s_412108 : RangeOk getRow 2051521 411765 412108 :=
  s_412039.append (by norm_num) r_412039
private theorem s_412177 : RangeOk getRow 2051521 411765 412177 :=
  s_412108.append (by norm_num) r_412108
private theorem s_412246 : RangeOk getRow 2051521 411765 412246 :=
  s_412177.append (by norm_num) r_412177
private theorem s_412316 : RangeOk getRow 2051521 411765 412316 :=
  s_412246.append (by norm_num) r_412246
private theorem s_412385 : RangeOk getRow 2051521 411765 412385 :=
  s_412316.append (by norm_num) r_412316
private theorem s_412453 : RangeOk getRow 2051521 411765 412453 :=
  s_412385.append (by norm_num) r_412385
private theorem s_412521 : RangeOk getRow 2051521 411765 412521 :=
  s_412453.append (by norm_num) r_412453
private theorem s_412589 : RangeOk getRow 2051521 411765 412589 :=
  s_412521.append (by norm_num) r_412521
private theorem s_412658 : RangeOk getRow 2051521 411765 412658 :=
  s_412589.append (by norm_num) r_412589
private theorem s_412727 : RangeOk getRow 2051521 411765 412727 :=
  s_412658.append (by norm_num) r_412658
private theorem s_412795 : RangeOk getRow 2051521 411765 412795 :=
  s_412727.append (by norm_num) r_412727
private theorem s_412864 : RangeOk getRow 2051521 411765 412864 :=
  s_412795.append (by norm_num) r_412795
private theorem s_412933 : RangeOk getRow 2051521 411765 412933 :=
  s_412864.append (by norm_num) r_412864
private theorem s_413000 : RangeOk getRow 2051521 411765 413000 :=
  s_412933.append (by norm_num) r_412933
private theorem s_413068 : RangeOk getRow 2051521 411765 413068 :=
  s_413000.append (by norm_num) r_413000
private theorem s_413136 : RangeOk getRow 2051521 411765 413136 :=
  s_413068.append (by norm_num) r_413068
private theorem s_413202 : RangeOk getRow 2051521 411765 413202 :=
  s_413136.append (by norm_num) r_413136
private theorem s_413271 : RangeOk getRow 2051521 411765 413271 :=
  s_413202.append (by norm_num) r_413202
private theorem s_413341 : RangeOk getRow 2051521 411765 413341 :=
  s_413271.append (by norm_num) r_413271
private theorem s_413410 : RangeOk getRow 2051521 411765 413410 :=
  s_413341.append (by norm_num) r_413341
private theorem s_413474 : RangeOk getRow 2051521 411765 413474 :=
  s_413410.append (by norm_num) r_413410
private theorem s_413538 : RangeOk getRow 2051521 411765 413538 :=
  s_413474.append (by norm_num) r_413474
private theorem s_413604 : RangeOk getRow 2051521 411765 413604 :=
  s_413538.append (by norm_num) r_413538
private theorem s_413673 : RangeOk getRow 2051521 411765 413673 :=
  s_413604.append (by norm_num) r_413604
private theorem s_413742 : RangeOk getRow 2051521 411765 413742 :=
  s_413673.append (by norm_num) r_413673
private theorem s_413811 : RangeOk getRow 2051521 411765 413811 :=
  s_413742.append (by norm_num) r_413742
private theorem s_413879 : RangeOk getRow 2051521 411765 413879 :=
  s_413811.append (by norm_num) r_413811
private theorem s_413947 : RangeOk getRow 2051521 411765 413947 :=
  s_413879.append (by norm_num) r_413879
private theorem s_414014 : RangeOk getRow 2051521 411765 414014 :=
  s_413947.append (by norm_num) r_413947
private theorem s_414081 : RangeOk getRow 2051521 411765 414081 :=
  s_414014.append (by norm_num) r_414014
private theorem s_414149 : RangeOk getRow 2051521 411765 414149 :=
  s_414081.append (by norm_num) r_414081
private theorem s_414220 : RangeOk getRow 2051521 411765 414220 :=
  s_414149.append (by norm_num) r_414149

/-- Rows `[411765, 414220)` are valid. -/
theorem rangeOk_411765_414220 : RangeOk getRow 2051521 411765 414220 := s_414220

end Noperthedron.Solution
