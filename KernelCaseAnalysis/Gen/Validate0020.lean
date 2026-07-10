import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[39514, 41242). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_39514 : RangeOk getRow 2051521 39514 39578 := by
  decide +kernel

private theorem r_39578 : RangeOk getRow 2051521 39578 39642 := by
  decide +kernel

private theorem r_39642 : RangeOk getRow 2051521 39642 39706 := by
  decide +kernel

private theorem r_39706 : RangeOk getRow 2051521 39706 39770 := by
  decide +kernel

private theorem r_39770 : RangeOk getRow 2051521 39770 39834 := by
  decide +kernel

private theorem r_39834 : RangeOk getRow 2051521 39834 39898 := by
  decide +kernel

private theorem r_39898 : RangeOk getRow 2051521 39898 39962 := by
  decide +kernel

private theorem r_39962 : RangeOk getRow 2051521 39962 40026 := by
  decide +kernel

private theorem r_40026 : RangeOk getRow 2051521 40026 40090 := by
  decide +kernel

private theorem r_40090 : RangeOk getRow 2051521 40090 40154 := by
  decide +kernel

private theorem r_40154 : RangeOk getRow 2051521 40154 40218 := by
  decide +kernel

private theorem r_40218 : RangeOk getRow 2051521 40218 40282 := by
  decide +kernel

private theorem r_40282 : RangeOk getRow 2051521 40282 40346 := by
  decide +kernel

private theorem r_40346 : RangeOk getRow 2051521 40346 40410 := by
  decide +kernel

private theorem r_40410 : RangeOk getRow 2051521 40410 40474 := by
  decide +kernel

private theorem r_40474 : RangeOk getRow 2051521 40474 40538 := by
  decide +kernel

private theorem r_40538 : RangeOk getRow 2051521 40538 40602 := by
  decide +kernel

private theorem r_40602 : RangeOk getRow 2051521 40602 40666 := by
  decide +kernel

private theorem r_40666 : RangeOk getRow 2051521 40666 40730 := by
  decide +kernel

private theorem r_40730 : RangeOk getRow 2051521 40730 40794 := by
  decide +kernel

private theorem r_40794 : RangeOk getRow 2051521 40794 40858 := by
  decide +kernel

private theorem r_40858 : RangeOk getRow 2051521 40858 40922 := by
  decide +kernel

private theorem r_40922 : RangeOk getRow 2051521 40922 40986 := by
  decide +kernel

private theorem r_40986 : RangeOk getRow 2051521 40986 41050 := by
  decide +kernel

private theorem r_41050 : RangeOk getRow 2051521 41050 41114 := by
  decide +kernel

private theorem r_41114 : RangeOk getRow 2051521 41114 41178 := by
  decide +kernel

private theorem r_41178 : RangeOk getRow 2051521 41178 41242 := by
  decide +kernel

private theorem s_39578 : RangeOk getRow 2051521 39514 39578 := r_39514
private theorem s_39642 : RangeOk getRow 2051521 39514 39642 :=
  s_39578.append (by norm_num) r_39578
private theorem s_39706 : RangeOk getRow 2051521 39514 39706 :=
  s_39642.append (by norm_num) r_39642
private theorem s_39770 : RangeOk getRow 2051521 39514 39770 :=
  s_39706.append (by norm_num) r_39706
private theorem s_39834 : RangeOk getRow 2051521 39514 39834 :=
  s_39770.append (by norm_num) r_39770
private theorem s_39898 : RangeOk getRow 2051521 39514 39898 :=
  s_39834.append (by norm_num) r_39834
private theorem s_39962 : RangeOk getRow 2051521 39514 39962 :=
  s_39898.append (by norm_num) r_39898
private theorem s_40026 : RangeOk getRow 2051521 39514 40026 :=
  s_39962.append (by norm_num) r_39962
private theorem s_40090 : RangeOk getRow 2051521 39514 40090 :=
  s_40026.append (by norm_num) r_40026
private theorem s_40154 : RangeOk getRow 2051521 39514 40154 :=
  s_40090.append (by norm_num) r_40090
private theorem s_40218 : RangeOk getRow 2051521 39514 40218 :=
  s_40154.append (by norm_num) r_40154
private theorem s_40282 : RangeOk getRow 2051521 39514 40282 :=
  s_40218.append (by norm_num) r_40218
private theorem s_40346 : RangeOk getRow 2051521 39514 40346 :=
  s_40282.append (by norm_num) r_40282
private theorem s_40410 : RangeOk getRow 2051521 39514 40410 :=
  s_40346.append (by norm_num) r_40346
private theorem s_40474 : RangeOk getRow 2051521 39514 40474 :=
  s_40410.append (by norm_num) r_40410
private theorem s_40538 : RangeOk getRow 2051521 39514 40538 :=
  s_40474.append (by norm_num) r_40474
private theorem s_40602 : RangeOk getRow 2051521 39514 40602 :=
  s_40538.append (by norm_num) r_40538
private theorem s_40666 : RangeOk getRow 2051521 39514 40666 :=
  s_40602.append (by norm_num) r_40602
private theorem s_40730 : RangeOk getRow 2051521 39514 40730 :=
  s_40666.append (by norm_num) r_40666
private theorem s_40794 : RangeOk getRow 2051521 39514 40794 :=
  s_40730.append (by norm_num) r_40730
private theorem s_40858 : RangeOk getRow 2051521 39514 40858 :=
  s_40794.append (by norm_num) r_40794
private theorem s_40922 : RangeOk getRow 2051521 39514 40922 :=
  s_40858.append (by norm_num) r_40858
private theorem s_40986 : RangeOk getRow 2051521 39514 40986 :=
  s_40922.append (by norm_num) r_40922
private theorem s_41050 : RangeOk getRow 2051521 39514 41050 :=
  s_40986.append (by norm_num) r_40986
private theorem s_41114 : RangeOk getRow 2051521 39514 41114 :=
  s_41050.append (by norm_num) r_41050
private theorem s_41178 : RangeOk getRow 2051521 39514 41178 :=
  s_41114.append (by norm_num) r_41114
private theorem s_41242 : RangeOk getRow 2051521 39514 41242 :=
  s_41178.append (by norm_num) r_41178

/-- Rows `[39514, 41242)` are valid. -/
theorem rangeOk_39514_41242 : RangeOk getRow 2051521 39514 41242 := s_41242

end Noperthedron.Solution
