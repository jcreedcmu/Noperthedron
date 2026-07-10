import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[945776, 948320). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_945776 : RangeOk getRow 2051521 945776 945846 := by
  decide +kernel

private theorem r_945846 : RangeOk getRow 2051521 945846 945915 := by
  decide +kernel

private theorem r_945915 : RangeOk getRow 2051521 945915 945983 := by
  decide +kernel

private theorem r_945983 : RangeOk getRow 2051521 945983 946049 := by
  decide +kernel

private theorem r_946049 : RangeOk getRow 2051521 946049 946116 := by
  decide +kernel

private theorem r_946116 : RangeOk getRow 2051521 946116 946182 := by
  decide +kernel

private theorem r_946182 : RangeOk getRow 2051521 946182 946247 := by
  decide +kernel

private theorem r_946247 : RangeOk getRow 2051521 946247 946312 := by
  decide +kernel

private theorem r_946312 : RangeOk getRow 2051521 946312 946383 := by
  decide +kernel

private theorem r_946383 : RangeOk getRow 2051521 946383 946454 := by
  decide +kernel

private theorem r_946454 : RangeOk getRow 2051521 946454 946525 := by
  decide +kernel

private theorem r_946525 : RangeOk getRow 2051521 946525 946594 := by
  decide +kernel

private theorem r_946594 : RangeOk getRow 2051521 946594 946665 := by
  decide +kernel

private theorem r_946665 : RangeOk getRow 2051521 946665 946737 := by
  decide +kernel

private theorem r_946737 : RangeOk getRow 2051521 946737 946808 := by
  decide +kernel

private theorem r_946808 : RangeOk getRow 2051521 946808 946877 := by
  decide +kernel

private theorem r_946877 : RangeOk getRow 2051521 946877 946947 := by
  decide +kernel

private theorem r_946947 : RangeOk getRow 2051521 946947 947016 := by
  decide +kernel

private theorem r_947016 : RangeOk getRow 2051521 947016 947086 := by
  decide +kernel

private theorem r_947086 : RangeOk getRow 2051521 947086 947151 := by
  decide +kernel

private theorem r_947151 : RangeOk getRow 2051521 947151 947218 := by
  decide +kernel

private theorem r_947218 : RangeOk getRow 2051521 947218 947284 := by
  decide +kernel

private theorem r_947284 : RangeOk getRow 2051521 947284 947349 := by
  decide +kernel

private theorem r_947349 : RangeOk getRow 2051521 947349 947416 := by
  decide +kernel

private theorem r_947416 : RangeOk getRow 2051521 947416 947485 := by
  decide +kernel

private theorem r_947485 : RangeOk getRow 2051521 947485 947556 := by
  decide +kernel

private theorem r_947556 : RangeOk getRow 2051521 947556 947627 := by
  decide +kernel

private theorem r_947627 : RangeOk getRow 2051521 947627 947697 := by
  decide +kernel

private theorem r_947697 : RangeOk getRow 2051521 947697 947767 := by
  decide +kernel

private theorem r_947767 : RangeOk getRow 2051521 947767 947840 := by
  decide +kernel

private theorem r_947840 : RangeOk getRow 2051521 947840 947911 := by
  decide +kernel

private theorem r_947911 : RangeOk getRow 2051521 947911 947982 := by
  decide +kernel

private theorem r_947982 : RangeOk getRow 2051521 947982 948054 := by
  decide +kernel

private theorem r_948054 : RangeOk getRow 2051521 948054 948122 := by
  decide +kernel

private theorem r_948122 : RangeOk getRow 2051521 948122 948189 := by
  decide +kernel

private theorem r_948189 : RangeOk getRow 2051521 948189 948255 := by
  decide +kernel

private theorem r_948255 : RangeOk getRow 2051521 948255 948320 := by
  decide +kernel

private theorem s_945846 : RangeOk getRow 2051521 945776 945846 := r_945776
private theorem s_945915 : RangeOk getRow 2051521 945776 945915 :=
  s_945846.append (by norm_num) r_945846
private theorem s_945983 : RangeOk getRow 2051521 945776 945983 :=
  s_945915.append (by norm_num) r_945915
private theorem s_946049 : RangeOk getRow 2051521 945776 946049 :=
  s_945983.append (by norm_num) r_945983
private theorem s_946116 : RangeOk getRow 2051521 945776 946116 :=
  s_946049.append (by norm_num) r_946049
private theorem s_946182 : RangeOk getRow 2051521 945776 946182 :=
  s_946116.append (by norm_num) r_946116
private theorem s_946247 : RangeOk getRow 2051521 945776 946247 :=
  s_946182.append (by norm_num) r_946182
private theorem s_946312 : RangeOk getRow 2051521 945776 946312 :=
  s_946247.append (by norm_num) r_946247
private theorem s_946383 : RangeOk getRow 2051521 945776 946383 :=
  s_946312.append (by norm_num) r_946312
private theorem s_946454 : RangeOk getRow 2051521 945776 946454 :=
  s_946383.append (by norm_num) r_946383
private theorem s_946525 : RangeOk getRow 2051521 945776 946525 :=
  s_946454.append (by norm_num) r_946454
private theorem s_946594 : RangeOk getRow 2051521 945776 946594 :=
  s_946525.append (by norm_num) r_946525
private theorem s_946665 : RangeOk getRow 2051521 945776 946665 :=
  s_946594.append (by norm_num) r_946594
private theorem s_946737 : RangeOk getRow 2051521 945776 946737 :=
  s_946665.append (by norm_num) r_946665
private theorem s_946808 : RangeOk getRow 2051521 945776 946808 :=
  s_946737.append (by norm_num) r_946737
private theorem s_946877 : RangeOk getRow 2051521 945776 946877 :=
  s_946808.append (by norm_num) r_946808
private theorem s_946947 : RangeOk getRow 2051521 945776 946947 :=
  s_946877.append (by norm_num) r_946877
private theorem s_947016 : RangeOk getRow 2051521 945776 947016 :=
  s_946947.append (by norm_num) r_946947
private theorem s_947086 : RangeOk getRow 2051521 945776 947086 :=
  s_947016.append (by norm_num) r_947016
private theorem s_947151 : RangeOk getRow 2051521 945776 947151 :=
  s_947086.append (by norm_num) r_947086
private theorem s_947218 : RangeOk getRow 2051521 945776 947218 :=
  s_947151.append (by norm_num) r_947151
private theorem s_947284 : RangeOk getRow 2051521 945776 947284 :=
  s_947218.append (by norm_num) r_947218
private theorem s_947349 : RangeOk getRow 2051521 945776 947349 :=
  s_947284.append (by norm_num) r_947284
private theorem s_947416 : RangeOk getRow 2051521 945776 947416 :=
  s_947349.append (by norm_num) r_947349
private theorem s_947485 : RangeOk getRow 2051521 945776 947485 :=
  s_947416.append (by norm_num) r_947416
private theorem s_947556 : RangeOk getRow 2051521 945776 947556 :=
  s_947485.append (by norm_num) r_947485
private theorem s_947627 : RangeOk getRow 2051521 945776 947627 :=
  s_947556.append (by norm_num) r_947556
private theorem s_947697 : RangeOk getRow 2051521 945776 947697 :=
  s_947627.append (by norm_num) r_947627
private theorem s_947767 : RangeOk getRow 2051521 945776 947767 :=
  s_947697.append (by norm_num) r_947697
private theorem s_947840 : RangeOk getRow 2051521 945776 947840 :=
  s_947767.append (by norm_num) r_947767
private theorem s_947911 : RangeOk getRow 2051521 945776 947911 :=
  s_947840.append (by norm_num) r_947840
private theorem s_947982 : RangeOk getRow 2051521 945776 947982 :=
  s_947911.append (by norm_num) r_947911
private theorem s_948054 : RangeOk getRow 2051521 945776 948054 :=
  s_947982.append (by norm_num) r_947982
private theorem s_948122 : RangeOk getRow 2051521 945776 948122 :=
  s_948054.append (by norm_num) r_948054
private theorem s_948189 : RangeOk getRow 2051521 945776 948189 :=
  s_948122.append (by norm_num) r_948122
private theorem s_948255 : RangeOk getRow 2051521 945776 948255 :=
  s_948189.append (by norm_num) r_948189
private theorem s_948320 : RangeOk getRow 2051521 945776 948320 :=
  s_948255.append (by norm_num) r_948255

/-- Rows `[945776, 948320)` are valid. -/
theorem rangeOk_945776_948320 : RangeOk getRow 2051521 945776 948320 := s_948320

end Noperthedron.Solution
