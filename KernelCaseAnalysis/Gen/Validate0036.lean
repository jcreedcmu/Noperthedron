import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[79534, 81262). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_79534 : RangeOk getRow 2051521 79534 79598 := by
  decide +kernel

private theorem r_79598 : RangeOk getRow 2051521 79598 79662 := by
  decide +kernel

private theorem r_79662 : RangeOk getRow 2051521 79662 79726 := by
  decide +kernel

private theorem r_79726 : RangeOk getRow 2051521 79726 79790 := by
  decide +kernel

private theorem r_79790 : RangeOk getRow 2051521 79790 79854 := by
  decide +kernel

private theorem r_79854 : RangeOk getRow 2051521 79854 79918 := by
  decide +kernel

private theorem r_79918 : RangeOk getRow 2051521 79918 79982 := by
  decide +kernel

private theorem r_79982 : RangeOk getRow 2051521 79982 80046 := by
  decide +kernel

private theorem r_80046 : RangeOk getRow 2051521 80046 80110 := by
  decide +kernel

private theorem r_80110 : RangeOk getRow 2051521 80110 80174 := by
  decide +kernel

private theorem r_80174 : RangeOk getRow 2051521 80174 80238 := by
  decide +kernel

private theorem r_80238 : RangeOk getRow 2051521 80238 80302 := by
  decide +kernel

private theorem r_80302 : RangeOk getRow 2051521 80302 80366 := by
  decide +kernel

private theorem r_80366 : RangeOk getRow 2051521 80366 80430 := by
  decide +kernel

private theorem r_80430 : RangeOk getRow 2051521 80430 80494 := by
  decide +kernel

private theorem r_80494 : RangeOk getRow 2051521 80494 80558 := by
  decide +kernel

private theorem r_80558 : RangeOk getRow 2051521 80558 80622 := by
  decide +kernel

private theorem r_80622 : RangeOk getRow 2051521 80622 80686 := by
  decide +kernel

private theorem r_80686 : RangeOk getRow 2051521 80686 80750 := by
  decide +kernel

private theorem r_80750 : RangeOk getRow 2051521 80750 80814 := by
  decide +kernel

private theorem r_80814 : RangeOk getRow 2051521 80814 80878 := by
  decide +kernel

private theorem r_80878 : RangeOk getRow 2051521 80878 80942 := by
  decide +kernel

private theorem r_80942 : RangeOk getRow 2051521 80942 81006 := by
  decide +kernel

private theorem r_81006 : RangeOk getRow 2051521 81006 81070 := by
  decide +kernel

private theorem r_81070 : RangeOk getRow 2051521 81070 81134 := by
  decide +kernel

private theorem r_81134 : RangeOk getRow 2051521 81134 81198 := by
  decide +kernel

private theorem r_81198 : RangeOk getRow 2051521 81198 81262 := by
  decide +kernel

private theorem s_79598 : RangeOk getRow 2051521 79534 79598 := r_79534
private theorem s_79662 : RangeOk getRow 2051521 79534 79662 :=
  s_79598.append (by norm_num) r_79598
private theorem s_79726 : RangeOk getRow 2051521 79534 79726 :=
  s_79662.append (by norm_num) r_79662
private theorem s_79790 : RangeOk getRow 2051521 79534 79790 :=
  s_79726.append (by norm_num) r_79726
private theorem s_79854 : RangeOk getRow 2051521 79534 79854 :=
  s_79790.append (by norm_num) r_79790
private theorem s_79918 : RangeOk getRow 2051521 79534 79918 :=
  s_79854.append (by norm_num) r_79854
private theorem s_79982 : RangeOk getRow 2051521 79534 79982 :=
  s_79918.append (by norm_num) r_79918
private theorem s_80046 : RangeOk getRow 2051521 79534 80046 :=
  s_79982.append (by norm_num) r_79982
private theorem s_80110 : RangeOk getRow 2051521 79534 80110 :=
  s_80046.append (by norm_num) r_80046
private theorem s_80174 : RangeOk getRow 2051521 79534 80174 :=
  s_80110.append (by norm_num) r_80110
private theorem s_80238 : RangeOk getRow 2051521 79534 80238 :=
  s_80174.append (by norm_num) r_80174
private theorem s_80302 : RangeOk getRow 2051521 79534 80302 :=
  s_80238.append (by norm_num) r_80238
private theorem s_80366 : RangeOk getRow 2051521 79534 80366 :=
  s_80302.append (by norm_num) r_80302
private theorem s_80430 : RangeOk getRow 2051521 79534 80430 :=
  s_80366.append (by norm_num) r_80366
private theorem s_80494 : RangeOk getRow 2051521 79534 80494 :=
  s_80430.append (by norm_num) r_80430
private theorem s_80558 : RangeOk getRow 2051521 79534 80558 :=
  s_80494.append (by norm_num) r_80494
private theorem s_80622 : RangeOk getRow 2051521 79534 80622 :=
  s_80558.append (by norm_num) r_80558
private theorem s_80686 : RangeOk getRow 2051521 79534 80686 :=
  s_80622.append (by norm_num) r_80622
private theorem s_80750 : RangeOk getRow 2051521 79534 80750 :=
  s_80686.append (by norm_num) r_80686
private theorem s_80814 : RangeOk getRow 2051521 79534 80814 :=
  s_80750.append (by norm_num) r_80750
private theorem s_80878 : RangeOk getRow 2051521 79534 80878 :=
  s_80814.append (by norm_num) r_80814
private theorem s_80942 : RangeOk getRow 2051521 79534 80942 :=
  s_80878.append (by norm_num) r_80878
private theorem s_81006 : RangeOk getRow 2051521 79534 81006 :=
  s_80942.append (by norm_num) r_80942
private theorem s_81070 : RangeOk getRow 2051521 79534 81070 :=
  s_81006.append (by norm_num) r_81006
private theorem s_81134 : RangeOk getRow 2051521 79534 81134 :=
  s_81070.append (by norm_num) r_81070
private theorem s_81198 : RangeOk getRow 2051521 79534 81198 :=
  s_81134.append (by norm_num) r_81134
private theorem s_81262 : RangeOk getRow 2051521 79534 81262 :=
  s_81198.append (by norm_num) r_81198

/-- Rows `[79534, 81262)` are valid. -/
theorem rangeOk_79534_81262 : RangeOk getRow 2051521 79534 81262 := s_81262

end Noperthedron.Solution
