import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[433006, 435294). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_433006 : RangeOk getRow 2051521 433006 433074 := by
  decide +kernel

private theorem r_433074 : RangeOk getRow 2051521 433074 433142 := by
  decide +kernel

private theorem r_433142 : RangeOk getRow 2051521 433142 433211 := by
  decide +kernel

private theorem r_433211 : RangeOk getRow 2051521 433211 433279 := by
  decide +kernel

private theorem r_433279 : RangeOk getRow 2051521 433279 433346 := by
  decide +kernel

private theorem r_433346 : RangeOk getRow 2051521 433346 433412 := by
  decide +kernel

private theorem r_433412 : RangeOk getRow 2051521 433412 433478 := by
  decide +kernel

private theorem r_433478 : RangeOk getRow 2051521 433478 433547 := by
  decide +kernel

private theorem r_433547 : RangeOk getRow 2051521 433547 433616 := by
  decide +kernel

private theorem r_433616 : RangeOk getRow 2051521 433616 433686 := by
  decide +kernel

private theorem r_433686 : RangeOk getRow 2051521 433686 433753 := by
  decide +kernel

private theorem r_433753 : RangeOk getRow 2051521 433753 433820 := by
  decide +kernel

private theorem r_433820 : RangeOk getRow 2051521 433820 433886 := by
  decide +kernel

private theorem r_433886 : RangeOk getRow 2051521 433886 433952 := by
  decide +kernel

private theorem r_433952 : RangeOk getRow 2051521 433952 434019 := by
  decide +kernel

private theorem r_434019 : RangeOk getRow 2051521 434019 434089 := by
  decide +kernel

private theorem r_434089 : RangeOk getRow 2051521 434089 434158 := by
  decide +kernel

private theorem r_434158 : RangeOk getRow 2051521 434158 434225 := by
  decide +kernel

private theorem r_434225 : RangeOk getRow 2051521 434225 434291 := by
  decide +kernel

private theorem r_434291 : RangeOk getRow 2051521 434291 434357 := by
  decide +kernel

private theorem r_434357 : RangeOk getRow 2051521 434357 434424 := by
  decide +kernel

private theorem r_434424 : RangeOk getRow 2051521 434424 434490 := by
  decide +kernel

private theorem r_434490 : RangeOk getRow 2051521 434490 434556 := by
  decide +kernel

private theorem r_434556 : RangeOk getRow 2051521 434556 434621 := by
  decide +kernel

private theorem r_434621 : RangeOk getRow 2051521 434621 434686 := by
  decide +kernel

private theorem r_434686 : RangeOk getRow 2051521 434686 434754 := by
  decide +kernel

private theorem r_434754 : RangeOk getRow 2051521 434754 434822 := by
  decide +kernel

private theorem r_434822 : RangeOk getRow 2051521 434822 434890 := by
  decide +kernel

private theorem r_434890 : RangeOk getRow 2051521 434890 434957 := by
  decide +kernel

private theorem r_434957 : RangeOk getRow 2051521 434957 435026 := by
  decide +kernel

private theorem r_435026 : RangeOk getRow 2051521 435026 435093 := by
  decide +kernel

private theorem r_435093 : RangeOk getRow 2051521 435093 435158 := by
  decide +kernel

private theorem r_435158 : RangeOk getRow 2051521 435158 435225 := by
  decide +kernel

private theorem r_435225 : RangeOk getRow 2051521 435225 435294 := by
  decide +kernel

private theorem s_433074 : RangeOk getRow 2051521 433006 433074 := r_433006
private theorem s_433142 : RangeOk getRow 2051521 433006 433142 :=
  s_433074.append (by norm_num) r_433074
private theorem s_433211 : RangeOk getRow 2051521 433006 433211 :=
  s_433142.append (by norm_num) r_433142
private theorem s_433279 : RangeOk getRow 2051521 433006 433279 :=
  s_433211.append (by norm_num) r_433211
private theorem s_433346 : RangeOk getRow 2051521 433006 433346 :=
  s_433279.append (by norm_num) r_433279
private theorem s_433412 : RangeOk getRow 2051521 433006 433412 :=
  s_433346.append (by norm_num) r_433346
private theorem s_433478 : RangeOk getRow 2051521 433006 433478 :=
  s_433412.append (by norm_num) r_433412
private theorem s_433547 : RangeOk getRow 2051521 433006 433547 :=
  s_433478.append (by norm_num) r_433478
private theorem s_433616 : RangeOk getRow 2051521 433006 433616 :=
  s_433547.append (by norm_num) r_433547
private theorem s_433686 : RangeOk getRow 2051521 433006 433686 :=
  s_433616.append (by norm_num) r_433616
private theorem s_433753 : RangeOk getRow 2051521 433006 433753 :=
  s_433686.append (by norm_num) r_433686
private theorem s_433820 : RangeOk getRow 2051521 433006 433820 :=
  s_433753.append (by norm_num) r_433753
private theorem s_433886 : RangeOk getRow 2051521 433006 433886 :=
  s_433820.append (by norm_num) r_433820
private theorem s_433952 : RangeOk getRow 2051521 433006 433952 :=
  s_433886.append (by norm_num) r_433886
private theorem s_434019 : RangeOk getRow 2051521 433006 434019 :=
  s_433952.append (by norm_num) r_433952
private theorem s_434089 : RangeOk getRow 2051521 433006 434089 :=
  s_434019.append (by norm_num) r_434019
private theorem s_434158 : RangeOk getRow 2051521 433006 434158 :=
  s_434089.append (by norm_num) r_434089
private theorem s_434225 : RangeOk getRow 2051521 433006 434225 :=
  s_434158.append (by norm_num) r_434158
private theorem s_434291 : RangeOk getRow 2051521 433006 434291 :=
  s_434225.append (by norm_num) r_434225
private theorem s_434357 : RangeOk getRow 2051521 433006 434357 :=
  s_434291.append (by norm_num) r_434291
private theorem s_434424 : RangeOk getRow 2051521 433006 434424 :=
  s_434357.append (by norm_num) r_434357
private theorem s_434490 : RangeOk getRow 2051521 433006 434490 :=
  s_434424.append (by norm_num) r_434424
private theorem s_434556 : RangeOk getRow 2051521 433006 434556 :=
  s_434490.append (by norm_num) r_434490
private theorem s_434621 : RangeOk getRow 2051521 433006 434621 :=
  s_434556.append (by norm_num) r_434556
private theorem s_434686 : RangeOk getRow 2051521 433006 434686 :=
  s_434621.append (by norm_num) r_434621
private theorem s_434754 : RangeOk getRow 2051521 433006 434754 :=
  s_434686.append (by norm_num) r_434686
private theorem s_434822 : RangeOk getRow 2051521 433006 434822 :=
  s_434754.append (by norm_num) r_434754
private theorem s_434890 : RangeOk getRow 2051521 433006 434890 :=
  s_434822.append (by norm_num) r_434822
private theorem s_434957 : RangeOk getRow 2051521 433006 434957 :=
  s_434890.append (by norm_num) r_434890
private theorem s_435026 : RangeOk getRow 2051521 433006 435026 :=
  s_434957.append (by norm_num) r_434957
private theorem s_435093 : RangeOk getRow 2051521 433006 435093 :=
  s_435026.append (by norm_num) r_435026
private theorem s_435158 : RangeOk getRow 2051521 433006 435158 :=
  s_435093.append (by norm_num) r_435093
private theorem s_435225 : RangeOk getRow 2051521 433006 435225 :=
  s_435158.append (by norm_num) r_435158
private theorem s_435294 : RangeOk getRow 2051521 433006 435294 :=
  s_435225.append (by norm_num) r_435225

/-- Rows `[433006, 435294)` are valid. -/
theorem rangeOk_433006_435294 : RangeOk getRow 2051521 433006 435294 := s_435294

end Noperthedron.Solution
