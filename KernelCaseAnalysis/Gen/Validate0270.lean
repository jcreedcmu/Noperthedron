import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[651549, 653845). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_651549 : RangeOk getRow 2051521 651549 651617 := by
  decide +kernel

private theorem r_651617 : RangeOk getRow 2051521 651617 651685 := by
  decide +kernel

private theorem r_651685 : RangeOk getRow 2051521 651685 651752 := by
  decide +kernel

private theorem r_651752 : RangeOk getRow 2051521 651752 651818 := by
  decide +kernel

private theorem r_651818 : RangeOk getRow 2051521 651818 651883 := by
  decide +kernel

private theorem r_651883 : RangeOk getRow 2051521 651883 651947 := by
  decide +kernel

private theorem r_651947 : RangeOk getRow 2051521 651947 652015 := by
  decide +kernel

private theorem r_652015 : RangeOk getRow 2051521 652015 652083 := by
  decide +kernel

private theorem r_652083 : RangeOk getRow 2051521 652083 652151 := by
  decide +kernel

private theorem r_652151 : RangeOk getRow 2051521 652151 652220 := by
  decide +kernel

private theorem r_652220 : RangeOk getRow 2051521 652220 652288 := by
  decide +kernel

private theorem r_652288 : RangeOk getRow 2051521 652288 652355 := by
  decide +kernel

private theorem r_652355 : RangeOk getRow 2051521 652355 652423 := by
  decide +kernel

private theorem r_652423 : RangeOk getRow 2051521 652423 652489 := by
  decide +kernel

private theorem r_652489 : RangeOk getRow 2051521 652489 652555 := by
  decide +kernel

private theorem r_652555 : RangeOk getRow 2051521 652555 652623 := by
  decide +kernel

private theorem r_652623 : RangeOk getRow 2051521 652623 652692 := by
  decide +kernel

private theorem r_652692 : RangeOk getRow 2051521 652692 652761 := by
  decide +kernel

private theorem r_652761 : RangeOk getRow 2051521 652761 652831 := by
  decide +kernel

private theorem r_652831 : RangeOk getRow 2051521 652831 652901 := by
  decide +kernel

private theorem r_652901 : RangeOk getRow 2051521 652901 652968 := by
  decide +kernel

private theorem r_652968 : RangeOk getRow 2051521 652968 653034 := by
  decide +kernel

private theorem r_653034 : RangeOk getRow 2051521 653034 653103 := by
  decide +kernel

private theorem r_653103 : RangeOk getRow 2051521 653103 653169 := by
  decide +kernel

private theorem r_653169 : RangeOk getRow 2051521 653169 653236 := by
  decide +kernel

private theorem r_653236 : RangeOk getRow 2051521 653236 653305 := by
  decide +kernel

private theorem r_653305 : RangeOk getRow 2051521 653305 653375 := by
  decide +kernel

private theorem r_653375 : RangeOk getRow 2051521 653375 653443 := by
  decide +kernel

private theorem r_653443 : RangeOk getRow 2051521 653443 653511 := by
  decide +kernel

private theorem r_653511 : RangeOk getRow 2051521 653511 653580 := by
  decide +kernel

private theorem r_653580 : RangeOk getRow 2051521 653580 653647 := by
  decide +kernel

private theorem r_653647 : RangeOk getRow 2051521 653647 653714 := by
  decide +kernel

private theorem r_653714 : RangeOk getRow 2051521 653714 653778 := by
  decide +kernel

private theorem r_653778 : RangeOk getRow 2051521 653778 653845 := by
  decide +kernel

private theorem s_651617 : RangeOk getRow 2051521 651549 651617 := r_651549
private theorem s_651685 : RangeOk getRow 2051521 651549 651685 :=
  s_651617.append (by norm_num) r_651617
private theorem s_651752 : RangeOk getRow 2051521 651549 651752 :=
  s_651685.append (by norm_num) r_651685
private theorem s_651818 : RangeOk getRow 2051521 651549 651818 :=
  s_651752.append (by norm_num) r_651752
private theorem s_651883 : RangeOk getRow 2051521 651549 651883 :=
  s_651818.append (by norm_num) r_651818
private theorem s_651947 : RangeOk getRow 2051521 651549 651947 :=
  s_651883.append (by norm_num) r_651883
private theorem s_652015 : RangeOk getRow 2051521 651549 652015 :=
  s_651947.append (by norm_num) r_651947
private theorem s_652083 : RangeOk getRow 2051521 651549 652083 :=
  s_652015.append (by norm_num) r_652015
private theorem s_652151 : RangeOk getRow 2051521 651549 652151 :=
  s_652083.append (by norm_num) r_652083
private theorem s_652220 : RangeOk getRow 2051521 651549 652220 :=
  s_652151.append (by norm_num) r_652151
private theorem s_652288 : RangeOk getRow 2051521 651549 652288 :=
  s_652220.append (by norm_num) r_652220
private theorem s_652355 : RangeOk getRow 2051521 651549 652355 :=
  s_652288.append (by norm_num) r_652288
private theorem s_652423 : RangeOk getRow 2051521 651549 652423 :=
  s_652355.append (by norm_num) r_652355
private theorem s_652489 : RangeOk getRow 2051521 651549 652489 :=
  s_652423.append (by norm_num) r_652423
private theorem s_652555 : RangeOk getRow 2051521 651549 652555 :=
  s_652489.append (by norm_num) r_652489
private theorem s_652623 : RangeOk getRow 2051521 651549 652623 :=
  s_652555.append (by norm_num) r_652555
private theorem s_652692 : RangeOk getRow 2051521 651549 652692 :=
  s_652623.append (by norm_num) r_652623
private theorem s_652761 : RangeOk getRow 2051521 651549 652761 :=
  s_652692.append (by norm_num) r_652692
private theorem s_652831 : RangeOk getRow 2051521 651549 652831 :=
  s_652761.append (by norm_num) r_652761
private theorem s_652901 : RangeOk getRow 2051521 651549 652901 :=
  s_652831.append (by norm_num) r_652831
private theorem s_652968 : RangeOk getRow 2051521 651549 652968 :=
  s_652901.append (by norm_num) r_652901
private theorem s_653034 : RangeOk getRow 2051521 651549 653034 :=
  s_652968.append (by norm_num) r_652968
private theorem s_653103 : RangeOk getRow 2051521 651549 653103 :=
  s_653034.append (by norm_num) r_653034
private theorem s_653169 : RangeOk getRow 2051521 651549 653169 :=
  s_653103.append (by norm_num) r_653103
private theorem s_653236 : RangeOk getRow 2051521 651549 653236 :=
  s_653169.append (by norm_num) r_653169
private theorem s_653305 : RangeOk getRow 2051521 651549 653305 :=
  s_653236.append (by norm_num) r_653236
private theorem s_653375 : RangeOk getRow 2051521 651549 653375 :=
  s_653305.append (by norm_num) r_653305
private theorem s_653443 : RangeOk getRow 2051521 651549 653443 :=
  s_653375.append (by norm_num) r_653375
private theorem s_653511 : RangeOk getRow 2051521 651549 653511 :=
  s_653443.append (by norm_num) r_653443
private theorem s_653580 : RangeOk getRow 2051521 651549 653580 :=
  s_653511.append (by norm_num) r_653511
private theorem s_653647 : RangeOk getRow 2051521 651549 653647 :=
  s_653580.append (by norm_num) r_653580
private theorem s_653714 : RangeOk getRow 2051521 651549 653714 :=
  s_653647.append (by norm_num) r_653647
private theorem s_653778 : RangeOk getRow 2051521 651549 653778 :=
  s_653714.append (by norm_num) r_653714
private theorem s_653845 : RangeOk getRow 2051521 651549 653845 :=
  s_653778.append (by norm_num) r_653778

/-- Rows `[651549, 653845)` are valid. -/
theorem rangeOk_651549_653845 : RangeOk getRow 2051521 651549 653845 := s_653845

end Noperthedron.Solution
