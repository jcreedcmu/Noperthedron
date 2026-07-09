import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[564450, 566750). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_564450 : RangeOk getRow 2051521 564450 564519 := by
  decide +kernel

private theorem r_564519 : RangeOk getRow 2051521 564519 564588 := by
  decide +kernel

private theorem r_564588 : RangeOk getRow 2051521 564588 564657 := by
  decide +kernel

private theorem r_564657 : RangeOk getRow 2051521 564657 564723 := by
  decide +kernel

private theorem r_564723 : RangeOk getRow 2051521 564723 564790 := by
  decide +kernel

private theorem r_564790 : RangeOk getRow 2051521 564790 564856 := by
  decide +kernel

private theorem r_564856 : RangeOk getRow 2051521 564856 564924 := by
  decide +kernel

private theorem r_564924 : RangeOk getRow 2051521 564924 564992 := by
  decide +kernel

private theorem r_564992 : RangeOk getRow 2051521 564992 565060 := by
  decide +kernel

private theorem r_565060 : RangeOk getRow 2051521 565060 565127 := by
  decide +kernel

private theorem r_565127 : RangeOk getRow 2051521 565127 565196 := by
  decide +kernel

private theorem r_565196 : RangeOk getRow 2051521 565196 565263 := by
  decide +kernel

private theorem r_565263 : RangeOk getRow 2051521 565263 565327 := by
  decide +kernel

private theorem r_565327 : RangeOk getRow 2051521 565327 565395 := by
  decide +kernel

private theorem r_565395 : RangeOk getRow 2051521 565395 565461 := by
  decide +kernel

private theorem r_565461 : RangeOk getRow 2051521 565461 565525 := by
  decide +kernel

private theorem r_565525 : RangeOk getRow 2051521 565525 565589 := by
  decide +kernel

private theorem r_565589 : RangeOk getRow 2051521 565589 565654 := by
  decide +kernel

private theorem r_565654 : RangeOk getRow 2051521 565654 565724 := by
  decide +kernel

private theorem r_565724 : RangeOk getRow 2051521 565724 565795 := by
  decide +kernel

private theorem r_565795 : RangeOk getRow 2051521 565795 565865 := by
  decide +kernel

private theorem r_565865 : RangeOk getRow 2051521 565865 565934 := by
  decide +kernel

private theorem r_565934 : RangeOk getRow 2051521 565934 566002 := by
  decide +kernel

private theorem r_566002 : RangeOk getRow 2051521 566002 566072 := by
  decide +kernel

private theorem r_566072 : RangeOk getRow 2051521 566072 566141 := by
  decide +kernel

private theorem r_566141 : RangeOk getRow 2051521 566141 566208 := by
  decide +kernel

private theorem r_566208 : RangeOk getRow 2051521 566208 566277 := by
  decide +kernel

private theorem r_566277 : RangeOk getRow 2051521 566277 566346 := by
  decide +kernel

private theorem r_566346 : RangeOk getRow 2051521 566346 566415 := by
  decide +kernel

private theorem r_566415 : RangeOk getRow 2051521 566415 566482 := by
  decide +kernel

private theorem r_566482 : RangeOk getRow 2051521 566482 566548 := by
  decide +kernel

private theorem r_566548 : RangeOk getRow 2051521 566548 566613 := by
  decide +kernel

private theorem r_566613 : RangeOk getRow 2051521 566613 566681 := by
  decide +kernel

private theorem r_566681 : RangeOk getRow 2051521 566681 566750 := by
  decide +kernel

private theorem s_564519 : RangeOk getRow 2051521 564450 564519 := r_564450
private theorem s_564588 : RangeOk getRow 2051521 564450 564588 :=
  s_564519.append (by norm_num) r_564519
private theorem s_564657 : RangeOk getRow 2051521 564450 564657 :=
  s_564588.append (by norm_num) r_564588
private theorem s_564723 : RangeOk getRow 2051521 564450 564723 :=
  s_564657.append (by norm_num) r_564657
private theorem s_564790 : RangeOk getRow 2051521 564450 564790 :=
  s_564723.append (by norm_num) r_564723
private theorem s_564856 : RangeOk getRow 2051521 564450 564856 :=
  s_564790.append (by norm_num) r_564790
private theorem s_564924 : RangeOk getRow 2051521 564450 564924 :=
  s_564856.append (by norm_num) r_564856
private theorem s_564992 : RangeOk getRow 2051521 564450 564992 :=
  s_564924.append (by norm_num) r_564924
private theorem s_565060 : RangeOk getRow 2051521 564450 565060 :=
  s_564992.append (by norm_num) r_564992
private theorem s_565127 : RangeOk getRow 2051521 564450 565127 :=
  s_565060.append (by norm_num) r_565060
private theorem s_565196 : RangeOk getRow 2051521 564450 565196 :=
  s_565127.append (by norm_num) r_565127
private theorem s_565263 : RangeOk getRow 2051521 564450 565263 :=
  s_565196.append (by norm_num) r_565196
private theorem s_565327 : RangeOk getRow 2051521 564450 565327 :=
  s_565263.append (by norm_num) r_565263
private theorem s_565395 : RangeOk getRow 2051521 564450 565395 :=
  s_565327.append (by norm_num) r_565327
private theorem s_565461 : RangeOk getRow 2051521 564450 565461 :=
  s_565395.append (by norm_num) r_565395
private theorem s_565525 : RangeOk getRow 2051521 564450 565525 :=
  s_565461.append (by norm_num) r_565461
private theorem s_565589 : RangeOk getRow 2051521 564450 565589 :=
  s_565525.append (by norm_num) r_565525
private theorem s_565654 : RangeOk getRow 2051521 564450 565654 :=
  s_565589.append (by norm_num) r_565589
private theorem s_565724 : RangeOk getRow 2051521 564450 565724 :=
  s_565654.append (by norm_num) r_565654
private theorem s_565795 : RangeOk getRow 2051521 564450 565795 :=
  s_565724.append (by norm_num) r_565724
private theorem s_565865 : RangeOk getRow 2051521 564450 565865 :=
  s_565795.append (by norm_num) r_565795
private theorem s_565934 : RangeOk getRow 2051521 564450 565934 :=
  s_565865.append (by norm_num) r_565865
private theorem s_566002 : RangeOk getRow 2051521 564450 566002 :=
  s_565934.append (by norm_num) r_565934
private theorem s_566072 : RangeOk getRow 2051521 564450 566072 :=
  s_566002.append (by norm_num) r_566002
private theorem s_566141 : RangeOk getRow 2051521 564450 566141 :=
  s_566072.append (by norm_num) r_566072
private theorem s_566208 : RangeOk getRow 2051521 564450 566208 :=
  s_566141.append (by norm_num) r_566141
private theorem s_566277 : RangeOk getRow 2051521 564450 566277 :=
  s_566208.append (by norm_num) r_566208
private theorem s_566346 : RangeOk getRow 2051521 564450 566346 :=
  s_566277.append (by norm_num) r_566277
private theorem s_566415 : RangeOk getRow 2051521 564450 566415 :=
  s_566346.append (by norm_num) r_566346
private theorem s_566482 : RangeOk getRow 2051521 564450 566482 :=
  s_566415.append (by norm_num) r_566415
private theorem s_566548 : RangeOk getRow 2051521 564450 566548 :=
  s_566482.append (by norm_num) r_566482
private theorem s_566613 : RangeOk getRow 2051521 564450 566613 :=
  s_566548.append (by norm_num) r_566548
private theorem s_566681 : RangeOk getRow 2051521 564450 566681 :=
  s_566613.append (by norm_num) r_566613
private theorem s_566750 : RangeOk getRow 2051521 564450 566750 :=
  s_566681.append (by norm_num) r_566681

/-- Rows `[564450, 566750)` are valid. -/
theorem rangeOk_564450_566750 : RangeOk getRow 2051521 564450 566750 := s_566750

end Noperthedron.Solution
