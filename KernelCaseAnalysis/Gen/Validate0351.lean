import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[844834, 847127). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_844834 : RangeOk getRow 2051521 844834 844904 := by
  decide +kernel

private theorem r_844904 : RangeOk getRow 2051521 844904 844973 := by
  decide +kernel

private theorem r_844973 : RangeOk getRow 2051521 844973 845040 := by
  decide +kernel

private theorem r_845040 : RangeOk getRow 2051521 845040 845108 := by
  decide +kernel

private theorem r_845108 : RangeOk getRow 2051521 845108 845179 := by
  decide +kernel

private theorem r_845179 : RangeOk getRow 2051521 845179 845247 := by
  decide +kernel

private theorem r_845247 : RangeOk getRow 2051521 845247 845316 := by
  decide +kernel

private theorem r_845316 : RangeOk getRow 2051521 845316 845382 := by
  decide +kernel

private theorem r_845382 : RangeOk getRow 2051521 845382 845447 := by
  decide +kernel

private theorem r_845447 : RangeOk getRow 2051521 845447 845515 := by
  decide +kernel

private theorem r_845515 : RangeOk getRow 2051521 845515 845584 := by
  decide +kernel

private theorem r_845584 : RangeOk getRow 2051521 845584 845653 := by
  decide +kernel

private theorem r_845653 : RangeOk getRow 2051521 845653 845719 := by
  decide +kernel

private theorem r_845719 : RangeOk getRow 2051521 845719 845785 := by
  decide +kernel

private theorem r_845785 : RangeOk getRow 2051521 845785 845851 := by
  decide +kernel

private theorem r_845851 : RangeOk getRow 2051521 845851 845917 := by
  decide +kernel

private theorem r_845917 : RangeOk getRow 2051521 845917 845982 := by
  decide +kernel

private theorem r_845982 : RangeOk getRow 2051521 845982 846050 := by
  decide +kernel

private theorem r_846050 : RangeOk getRow 2051521 846050 846116 := by
  decide +kernel

private theorem r_846116 : RangeOk getRow 2051521 846116 846182 := by
  decide +kernel

private theorem r_846182 : RangeOk getRow 2051521 846182 846249 := by
  decide +kernel

private theorem r_846249 : RangeOk getRow 2051521 846249 846316 := by
  decide +kernel

private theorem r_846316 : RangeOk getRow 2051521 846316 846387 := by
  decide +kernel

private theorem r_846387 : RangeOk getRow 2051521 846387 846455 := by
  decide +kernel

private theorem r_846455 : RangeOk getRow 2051521 846455 846524 := by
  decide +kernel

private theorem r_846524 : RangeOk getRow 2051521 846524 846590 := by
  decide +kernel

private theorem r_846590 : RangeOk getRow 2051521 846590 846658 := by
  decide +kernel

private theorem r_846658 : RangeOk getRow 2051521 846658 846725 := by
  decide +kernel

private theorem r_846725 : RangeOk getRow 2051521 846725 846793 := by
  decide +kernel

private theorem r_846793 : RangeOk getRow 2051521 846793 846860 := by
  decide +kernel

private theorem r_846860 : RangeOk getRow 2051521 846860 846926 := by
  decide +kernel

private theorem r_846926 : RangeOk getRow 2051521 846926 846994 := by
  decide +kernel

private theorem r_846994 : RangeOk getRow 2051521 846994 847060 := by
  decide +kernel

private theorem r_847060 : RangeOk getRow 2051521 847060 847127 := by
  decide +kernel

private theorem s_844904 : RangeOk getRow 2051521 844834 844904 := r_844834
private theorem s_844973 : RangeOk getRow 2051521 844834 844973 :=
  s_844904.append (by norm_num) r_844904
private theorem s_845040 : RangeOk getRow 2051521 844834 845040 :=
  s_844973.append (by norm_num) r_844973
private theorem s_845108 : RangeOk getRow 2051521 844834 845108 :=
  s_845040.append (by norm_num) r_845040
private theorem s_845179 : RangeOk getRow 2051521 844834 845179 :=
  s_845108.append (by norm_num) r_845108
private theorem s_845247 : RangeOk getRow 2051521 844834 845247 :=
  s_845179.append (by norm_num) r_845179
private theorem s_845316 : RangeOk getRow 2051521 844834 845316 :=
  s_845247.append (by norm_num) r_845247
private theorem s_845382 : RangeOk getRow 2051521 844834 845382 :=
  s_845316.append (by norm_num) r_845316
private theorem s_845447 : RangeOk getRow 2051521 844834 845447 :=
  s_845382.append (by norm_num) r_845382
private theorem s_845515 : RangeOk getRow 2051521 844834 845515 :=
  s_845447.append (by norm_num) r_845447
private theorem s_845584 : RangeOk getRow 2051521 844834 845584 :=
  s_845515.append (by norm_num) r_845515
private theorem s_845653 : RangeOk getRow 2051521 844834 845653 :=
  s_845584.append (by norm_num) r_845584
private theorem s_845719 : RangeOk getRow 2051521 844834 845719 :=
  s_845653.append (by norm_num) r_845653
private theorem s_845785 : RangeOk getRow 2051521 844834 845785 :=
  s_845719.append (by norm_num) r_845719
private theorem s_845851 : RangeOk getRow 2051521 844834 845851 :=
  s_845785.append (by norm_num) r_845785
private theorem s_845917 : RangeOk getRow 2051521 844834 845917 :=
  s_845851.append (by norm_num) r_845851
private theorem s_845982 : RangeOk getRow 2051521 844834 845982 :=
  s_845917.append (by norm_num) r_845917
private theorem s_846050 : RangeOk getRow 2051521 844834 846050 :=
  s_845982.append (by norm_num) r_845982
private theorem s_846116 : RangeOk getRow 2051521 844834 846116 :=
  s_846050.append (by norm_num) r_846050
private theorem s_846182 : RangeOk getRow 2051521 844834 846182 :=
  s_846116.append (by norm_num) r_846116
private theorem s_846249 : RangeOk getRow 2051521 844834 846249 :=
  s_846182.append (by norm_num) r_846182
private theorem s_846316 : RangeOk getRow 2051521 844834 846316 :=
  s_846249.append (by norm_num) r_846249
private theorem s_846387 : RangeOk getRow 2051521 844834 846387 :=
  s_846316.append (by norm_num) r_846316
private theorem s_846455 : RangeOk getRow 2051521 844834 846455 :=
  s_846387.append (by norm_num) r_846387
private theorem s_846524 : RangeOk getRow 2051521 844834 846524 :=
  s_846455.append (by norm_num) r_846455
private theorem s_846590 : RangeOk getRow 2051521 844834 846590 :=
  s_846524.append (by norm_num) r_846524
private theorem s_846658 : RangeOk getRow 2051521 844834 846658 :=
  s_846590.append (by norm_num) r_846590
private theorem s_846725 : RangeOk getRow 2051521 844834 846725 :=
  s_846658.append (by norm_num) r_846658
private theorem s_846793 : RangeOk getRow 2051521 844834 846793 :=
  s_846725.append (by norm_num) r_846725
private theorem s_846860 : RangeOk getRow 2051521 844834 846860 :=
  s_846793.append (by norm_num) r_846793
private theorem s_846926 : RangeOk getRow 2051521 844834 846926 :=
  s_846860.append (by norm_num) r_846860
private theorem s_846994 : RangeOk getRow 2051521 844834 846994 :=
  s_846926.append (by norm_num) r_846926
private theorem s_847060 : RangeOk getRow 2051521 844834 847060 :=
  s_846994.append (by norm_num) r_846994
private theorem s_847127 : RangeOk getRow 2051521 844834 847127 :=
  s_847060.append (by norm_num) r_847060

/-- Rows `[844834, 847127)` are valid. -/
theorem rangeOk_844834_847127 : RangeOk getRow 2051521 844834 847127 := s_847127

end Noperthedron.Solution
