import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[480205, 482503). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_480205 : RangeOk getRow 2051521 480205 480274 := by
  decide +kernel

private theorem r_480274 : RangeOk getRow 2051521 480274 480343 := by
  decide +kernel

private theorem r_480343 : RangeOk getRow 2051521 480343 480407 := by
  decide +kernel

private theorem r_480407 : RangeOk getRow 2051521 480407 480472 := by
  decide +kernel

private theorem r_480472 : RangeOk getRow 2051521 480472 480536 := by
  decide +kernel

private theorem r_480536 : RangeOk getRow 2051521 480536 480600 := by
  decide +kernel

private theorem r_480600 : RangeOk getRow 2051521 480600 480664 := by
  decide +kernel

private theorem r_480664 : RangeOk getRow 2051521 480664 480728 := by
  decide +kernel

private theorem r_480728 : RangeOk getRow 2051521 480728 480794 := by
  decide +kernel

private theorem r_480794 : RangeOk getRow 2051521 480794 480864 := by
  decide +kernel

private theorem r_480864 : RangeOk getRow 2051521 480864 480931 := by
  decide +kernel

private theorem r_480931 : RangeOk getRow 2051521 480931 480999 := by
  decide +kernel

private theorem r_480999 : RangeOk getRow 2051521 480999 481068 := by
  decide +kernel

private theorem r_481068 : RangeOk getRow 2051521 481068 481136 := by
  decide +kernel

private theorem r_481136 : RangeOk getRow 2051521 481136 481205 := by
  decide +kernel

private theorem r_481205 : RangeOk getRow 2051521 481205 481275 := by
  decide +kernel

private theorem r_481275 : RangeOk getRow 2051521 481275 481344 := by
  decide +kernel

private theorem r_481344 : RangeOk getRow 2051521 481344 481412 := by
  decide +kernel

private theorem r_481412 : RangeOk getRow 2051521 481412 481479 := by
  decide +kernel

private theorem r_481479 : RangeOk getRow 2051521 481479 481546 := by
  decide +kernel

private theorem r_481546 : RangeOk getRow 2051521 481546 481614 := by
  decide +kernel

private theorem r_481614 : RangeOk getRow 2051521 481614 481682 := by
  decide +kernel

private theorem r_481682 : RangeOk getRow 2051521 481682 481751 := by
  decide +kernel

private theorem r_481751 : RangeOk getRow 2051521 481751 481819 := by
  decide +kernel

private theorem r_481819 : RangeOk getRow 2051521 481819 481887 := by
  decide +kernel

private theorem r_481887 : RangeOk getRow 2051521 481887 481955 := by
  decide +kernel

private theorem r_481955 : RangeOk getRow 2051521 481955 482022 := by
  decide +kernel

private theorem r_482022 : RangeOk getRow 2051521 482022 482090 := by
  decide +kernel

private theorem r_482090 : RangeOk getRow 2051521 482090 482160 := by
  decide +kernel

private theorem r_482160 : RangeOk getRow 2051521 482160 482229 := by
  decide +kernel

private theorem r_482229 : RangeOk getRow 2051521 482229 482297 := by
  decide +kernel

private theorem r_482297 : RangeOk getRow 2051521 482297 482365 := by
  decide +kernel

private theorem r_482365 : RangeOk getRow 2051521 482365 482434 := by
  decide +kernel

private theorem r_482434 : RangeOk getRow 2051521 482434 482503 := by
  decide +kernel

private theorem s_480274 : RangeOk getRow 2051521 480205 480274 := r_480205
private theorem s_480343 : RangeOk getRow 2051521 480205 480343 :=
  s_480274.append (by norm_num) r_480274
private theorem s_480407 : RangeOk getRow 2051521 480205 480407 :=
  s_480343.append (by norm_num) r_480343
private theorem s_480472 : RangeOk getRow 2051521 480205 480472 :=
  s_480407.append (by norm_num) r_480407
private theorem s_480536 : RangeOk getRow 2051521 480205 480536 :=
  s_480472.append (by norm_num) r_480472
private theorem s_480600 : RangeOk getRow 2051521 480205 480600 :=
  s_480536.append (by norm_num) r_480536
private theorem s_480664 : RangeOk getRow 2051521 480205 480664 :=
  s_480600.append (by norm_num) r_480600
private theorem s_480728 : RangeOk getRow 2051521 480205 480728 :=
  s_480664.append (by norm_num) r_480664
private theorem s_480794 : RangeOk getRow 2051521 480205 480794 :=
  s_480728.append (by norm_num) r_480728
private theorem s_480864 : RangeOk getRow 2051521 480205 480864 :=
  s_480794.append (by norm_num) r_480794
private theorem s_480931 : RangeOk getRow 2051521 480205 480931 :=
  s_480864.append (by norm_num) r_480864
private theorem s_480999 : RangeOk getRow 2051521 480205 480999 :=
  s_480931.append (by norm_num) r_480931
private theorem s_481068 : RangeOk getRow 2051521 480205 481068 :=
  s_480999.append (by norm_num) r_480999
private theorem s_481136 : RangeOk getRow 2051521 480205 481136 :=
  s_481068.append (by norm_num) r_481068
private theorem s_481205 : RangeOk getRow 2051521 480205 481205 :=
  s_481136.append (by norm_num) r_481136
private theorem s_481275 : RangeOk getRow 2051521 480205 481275 :=
  s_481205.append (by norm_num) r_481205
private theorem s_481344 : RangeOk getRow 2051521 480205 481344 :=
  s_481275.append (by norm_num) r_481275
private theorem s_481412 : RangeOk getRow 2051521 480205 481412 :=
  s_481344.append (by norm_num) r_481344
private theorem s_481479 : RangeOk getRow 2051521 480205 481479 :=
  s_481412.append (by norm_num) r_481412
private theorem s_481546 : RangeOk getRow 2051521 480205 481546 :=
  s_481479.append (by norm_num) r_481479
private theorem s_481614 : RangeOk getRow 2051521 480205 481614 :=
  s_481546.append (by norm_num) r_481546
private theorem s_481682 : RangeOk getRow 2051521 480205 481682 :=
  s_481614.append (by norm_num) r_481614
private theorem s_481751 : RangeOk getRow 2051521 480205 481751 :=
  s_481682.append (by norm_num) r_481682
private theorem s_481819 : RangeOk getRow 2051521 480205 481819 :=
  s_481751.append (by norm_num) r_481751
private theorem s_481887 : RangeOk getRow 2051521 480205 481887 :=
  s_481819.append (by norm_num) r_481819
private theorem s_481955 : RangeOk getRow 2051521 480205 481955 :=
  s_481887.append (by norm_num) r_481887
private theorem s_482022 : RangeOk getRow 2051521 480205 482022 :=
  s_481955.append (by norm_num) r_481955
private theorem s_482090 : RangeOk getRow 2051521 480205 482090 :=
  s_482022.append (by norm_num) r_482022
private theorem s_482160 : RangeOk getRow 2051521 480205 482160 :=
  s_482090.append (by norm_num) r_482090
private theorem s_482229 : RangeOk getRow 2051521 480205 482229 :=
  s_482160.append (by norm_num) r_482160
private theorem s_482297 : RangeOk getRow 2051521 480205 482297 :=
  s_482229.append (by norm_num) r_482229
private theorem s_482365 : RangeOk getRow 2051521 480205 482365 :=
  s_482297.append (by norm_num) r_482297
private theorem s_482434 : RangeOk getRow 2051521 480205 482434 :=
  s_482365.append (by norm_num) r_482365
private theorem s_482503 : RangeOk getRow 2051521 480205 482503 :=
  s_482434.append (by norm_num) r_482434

/-- Rows `[480205, 482503)` are valid. -/
theorem rangeOk_480205_482503 : RangeOk getRow 2051521 480205 482503 := s_482503

end Noperthedron.Solution
