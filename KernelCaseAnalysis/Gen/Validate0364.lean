import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[876407, 878693). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_876407 : RangeOk getRow 2051521 876407 876475 := by
  decide +kernel

private theorem r_876475 : RangeOk getRow 2051521 876475 876541 := by
  decide +kernel

private theorem r_876541 : RangeOk getRow 2051521 876541 876607 := by
  decide +kernel

private theorem r_876607 : RangeOk getRow 2051521 876607 876674 := by
  decide +kernel

private theorem r_876674 : RangeOk getRow 2051521 876674 876739 := by
  decide +kernel

private theorem r_876739 : RangeOk getRow 2051521 876739 876805 := by
  decide +kernel

private theorem r_876805 : RangeOk getRow 2051521 876805 876871 := by
  decide +kernel

private theorem r_876871 : RangeOk getRow 2051521 876871 876939 := by
  decide +kernel

private theorem r_876939 : RangeOk getRow 2051521 876939 877007 := by
  decide +kernel

private theorem r_877007 : RangeOk getRow 2051521 877007 877075 := by
  decide +kernel

private theorem r_877075 : RangeOk getRow 2051521 877075 877145 := by
  decide +kernel

private theorem r_877145 : RangeOk getRow 2051521 877145 877212 := by
  decide +kernel

private theorem r_877212 : RangeOk getRow 2051521 877212 877277 := by
  decide +kernel

private theorem r_877277 : RangeOk getRow 2051521 877277 877343 := by
  decide +kernel

private theorem r_877343 : RangeOk getRow 2051521 877343 877411 := by
  decide +kernel

private theorem r_877411 : RangeOk getRow 2051521 877411 877479 := by
  decide +kernel

private theorem r_877479 : RangeOk getRow 2051521 877479 877547 := by
  decide +kernel

private theorem r_877547 : RangeOk getRow 2051521 877547 877614 := by
  decide +kernel

private theorem r_877614 : RangeOk getRow 2051521 877614 877680 := by
  decide +kernel

private theorem r_877680 : RangeOk getRow 2051521 877680 877747 := by
  decide +kernel

private theorem r_877747 : RangeOk getRow 2051521 877747 877814 := by
  decide +kernel

private theorem r_877814 : RangeOk getRow 2051521 877814 877884 := by
  decide +kernel

private theorem r_877884 : RangeOk getRow 2051521 877884 877952 := by
  decide +kernel

private theorem r_877952 : RangeOk getRow 2051521 877952 878020 := by
  decide +kernel

private theorem r_878020 : RangeOk getRow 2051521 878020 878088 := by
  decide +kernel

private theorem r_878088 : RangeOk getRow 2051521 878088 878154 := by
  decide +kernel

private theorem r_878154 : RangeOk getRow 2051521 878154 878221 := by
  decide +kernel

private theorem r_878221 : RangeOk getRow 2051521 878221 878291 := by
  decide +kernel

private theorem r_878291 : RangeOk getRow 2051521 878291 878359 := by
  decide +kernel

private theorem r_878359 : RangeOk getRow 2051521 878359 878428 := by
  decide +kernel

private theorem r_878428 : RangeOk getRow 2051521 878428 878494 := by
  decide +kernel

private theorem r_878494 : RangeOk getRow 2051521 878494 878560 := by
  decide +kernel

private theorem r_878560 : RangeOk getRow 2051521 878560 878627 := by
  decide +kernel

private theorem r_878627 : RangeOk getRow 2051521 878627 878693 := by
  decide +kernel

private theorem s_876475 : RangeOk getRow 2051521 876407 876475 := r_876407
private theorem s_876541 : RangeOk getRow 2051521 876407 876541 :=
  s_876475.append (by norm_num) r_876475
private theorem s_876607 : RangeOk getRow 2051521 876407 876607 :=
  s_876541.append (by norm_num) r_876541
private theorem s_876674 : RangeOk getRow 2051521 876407 876674 :=
  s_876607.append (by norm_num) r_876607
private theorem s_876739 : RangeOk getRow 2051521 876407 876739 :=
  s_876674.append (by norm_num) r_876674
private theorem s_876805 : RangeOk getRow 2051521 876407 876805 :=
  s_876739.append (by norm_num) r_876739
private theorem s_876871 : RangeOk getRow 2051521 876407 876871 :=
  s_876805.append (by norm_num) r_876805
private theorem s_876939 : RangeOk getRow 2051521 876407 876939 :=
  s_876871.append (by norm_num) r_876871
private theorem s_877007 : RangeOk getRow 2051521 876407 877007 :=
  s_876939.append (by norm_num) r_876939
private theorem s_877075 : RangeOk getRow 2051521 876407 877075 :=
  s_877007.append (by norm_num) r_877007
private theorem s_877145 : RangeOk getRow 2051521 876407 877145 :=
  s_877075.append (by norm_num) r_877075
private theorem s_877212 : RangeOk getRow 2051521 876407 877212 :=
  s_877145.append (by norm_num) r_877145
private theorem s_877277 : RangeOk getRow 2051521 876407 877277 :=
  s_877212.append (by norm_num) r_877212
private theorem s_877343 : RangeOk getRow 2051521 876407 877343 :=
  s_877277.append (by norm_num) r_877277
private theorem s_877411 : RangeOk getRow 2051521 876407 877411 :=
  s_877343.append (by norm_num) r_877343
private theorem s_877479 : RangeOk getRow 2051521 876407 877479 :=
  s_877411.append (by norm_num) r_877411
private theorem s_877547 : RangeOk getRow 2051521 876407 877547 :=
  s_877479.append (by norm_num) r_877479
private theorem s_877614 : RangeOk getRow 2051521 876407 877614 :=
  s_877547.append (by norm_num) r_877547
private theorem s_877680 : RangeOk getRow 2051521 876407 877680 :=
  s_877614.append (by norm_num) r_877614
private theorem s_877747 : RangeOk getRow 2051521 876407 877747 :=
  s_877680.append (by norm_num) r_877680
private theorem s_877814 : RangeOk getRow 2051521 876407 877814 :=
  s_877747.append (by norm_num) r_877747
private theorem s_877884 : RangeOk getRow 2051521 876407 877884 :=
  s_877814.append (by norm_num) r_877814
private theorem s_877952 : RangeOk getRow 2051521 876407 877952 :=
  s_877884.append (by norm_num) r_877884
private theorem s_878020 : RangeOk getRow 2051521 876407 878020 :=
  s_877952.append (by norm_num) r_877952
private theorem s_878088 : RangeOk getRow 2051521 876407 878088 :=
  s_878020.append (by norm_num) r_878020
private theorem s_878154 : RangeOk getRow 2051521 876407 878154 :=
  s_878088.append (by norm_num) r_878088
private theorem s_878221 : RangeOk getRow 2051521 876407 878221 :=
  s_878154.append (by norm_num) r_878154
private theorem s_878291 : RangeOk getRow 2051521 876407 878291 :=
  s_878221.append (by norm_num) r_878221
private theorem s_878359 : RangeOk getRow 2051521 876407 878359 :=
  s_878291.append (by norm_num) r_878291
private theorem s_878428 : RangeOk getRow 2051521 876407 878428 :=
  s_878359.append (by norm_num) r_878359
private theorem s_878494 : RangeOk getRow 2051521 876407 878494 :=
  s_878428.append (by norm_num) r_878428
private theorem s_878560 : RangeOk getRow 2051521 876407 878560 :=
  s_878494.append (by norm_num) r_878494
private theorem s_878627 : RangeOk getRow 2051521 876407 878627 :=
  s_878560.append (by norm_num) r_878560
private theorem s_878693 : RangeOk getRow 2051521 876407 878693 :=
  s_878627.append (by norm_num) r_878627

/-- Rows `[876407, 878693)` are valid. -/
theorem rangeOk_876407_878693 : RangeOk getRow 2051521 876407 878693 := s_878693

end Noperthedron.Solution
