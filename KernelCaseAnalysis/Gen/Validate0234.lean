import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[566750, 569042). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_566750 : RangeOk getRow 2051521 566750 566818 := by
  decide +kernel

private theorem r_566818 : RangeOk getRow 2051521 566818 566885 := by
  decide +kernel

private theorem r_566885 : RangeOk getRow 2051521 566885 566953 := by
  decide +kernel

private theorem r_566953 : RangeOk getRow 2051521 566953 567020 := by
  decide +kernel

private theorem r_567020 : RangeOk getRow 2051521 567020 567085 := by
  decide +kernel

private theorem r_567085 : RangeOk getRow 2051521 567085 567151 := by
  decide +kernel

private theorem r_567151 : RangeOk getRow 2051521 567151 567219 := by
  decide +kernel

private theorem r_567219 : RangeOk getRow 2051521 567219 567287 := by
  decide +kernel

private theorem r_567287 : RangeOk getRow 2051521 567287 567356 := by
  decide +kernel

private theorem r_567356 : RangeOk getRow 2051521 567356 567422 := by
  decide +kernel

private theorem r_567422 : RangeOk getRow 2051521 567422 567490 := by
  decide +kernel

private theorem r_567490 : RangeOk getRow 2051521 567490 567558 := by
  decide +kernel

private theorem r_567558 : RangeOk getRow 2051521 567558 567626 := by
  decide +kernel

private theorem r_567626 : RangeOk getRow 2051521 567626 567692 := by
  decide +kernel

private theorem r_567692 : RangeOk getRow 2051521 567692 567760 := by
  decide +kernel

private theorem r_567760 : RangeOk getRow 2051521 567760 567828 := by
  decide +kernel

private theorem r_567828 : RangeOk getRow 2051521 567828 567897 := by
  decide +kernel

private theorem r_567897 : RangeOk getRow 2051521 567897 567965 := by
  decide +kernel

private theorem r_567965 : RangeOk getRow 2051521 567965 568032 := by
  decide +kernel

private theorem r_568032 : RangeOk getRow 2051521 568032 568100 := by
  decide +kernel

private theorem r_568100 : RangeOk getRow 2051521 568100 568166 := by
  decide +kernel

private theorem r_568166 : RangeOk getRow 2051521 568166 568233 := by
  decide +kernel

private theorem r_568233 : RangeOk getRow 2051521 568233 568301 := by
  decide +kernel

private theorem r_568301 : RangeOk getRow 2051521 568301 568369 := by
  decide +kernel

private theorem r_568369 : RangeOk getRow 2051521 568369 568437 := by
  decide +kernel

private theorem r_568437 : RangeOk getRow 2051521 568437 568504 := by
  decide +kernel

private theorem r_568504 : RangeOk getRow 2051521 568504 568571 := by
  decide +kernel

private theorem r_568571 : RangeOk getRow 2051521 568571 568637 := by
  decide +kernel

private theorem r_568637 : RangeOk getRow 2051521 568637 568705 := by
  decide +kernel

private theorem r_568705 : RangeOk getRow 2051521 568705 568771 := by
  decide +kernel

private theorem r_568771 : RangeOk getRow 2051521 568771 568840 := by
  decide +kernel

private theorem r_568840 : RangeOk getRow 2051521 568840 568908 := by
  decide +kernel

private theorem r_568908 : RangeOk getRow 2051521 568908 568976 := by
  decide +kernel

private theorem r_568976 : RangeOk getRow 2051521 568976 569042 := by
  decide +kernel

private theorem s_566818 : RangeOk getRow 2051521 566750 566818 := r_566750
private theorem s_566885 : RangeOk getRow 2051521 566750 566885 :=
  s_566818.append (by norm_num) r_566818
private theorem s_566953 : RangeOk getRow 2051521 566750 566953 :=
  s_566885.append (by norm_num) r_566885
private theorem s_567020 : RangeOk getRow 2051521 566750 567020 :=
  s_566953.append (by norm_num) r_566953
private theorem s_567085 : RangeOk getRow 2051521 566750 567085 :=
  s_567020.append (by norm_num) r_567020
private theorem s_567151 : RangeOk getRow 2051521 566750 567151 :=
  s_567085.append (by norm_num) r_567085
private theorem s_567219 : RangeOk getRow 2051521 566750 567219 :=
  s_567151.append (by norm_num) r_567151
private theorem s_567287 : RangeOk getRow 2051521 566750 567287 :=
  s_567219.append (by norm_num) r_567219
private theorem s_567356 : RangeOk getRow 2051521 566750 567356 :=
  s_567287.append (by norm_num) r_567287
private theorem s_567422 : RangeOk getRow 2051521 566750 567422 :=
  s_567356.append (by norm_num) r_567356
private theorem s_567490 : RangeOk getRow 2051521 566750 567490 :=
  s_567422.append (by norm_num) r_567422
private theorem s_567558 : RangeOk getRow 2051521 566750 567558 :=
  s_567490.append (by norm_num) r_567490
private theorem s_567626 : RangeOk getRow 2051521 566750 567626 :=
  s_567558.append (by norm_num) r_567558
private theorem s_567692 : RangeOk getRow 2051521 566750 567692 :=
  s_567626.append (by norm_num) r_567626
private theorem s_567760 : RangeOk getRow 2051521 566750 567760 :=
  s_567692.append (by norm_num) r_567692
private theorem s_567828 : RangeOk getRow 2051521 566750 567828 :=
  s_567760.append (by norm_num) r_567760
private theorem s_567897 : RangeOk getRow 2051521 566750 567897 :=
  s_567828.append (by norm_num) r_567828
private theorem s_567965 : RangeOk getRow 2051521 566750 567965 :=
  s_567897.append (by norm_num) r_567897
private theorem s_568032 : RangeOk getRow 2051521 566750 568032 :=
  s_567965.append (by norm_num) r_567965
private theorem s_568100 : RangeOk getRow 2051521 566750 568100 :=
  s_568032.append (by norm_num) r_568032
private theorem s_568166 : RangeOk getRow 2051521 566750 568166 :=
  s_568100.append (by norm_num) r_568100
private theorem s_568233 : RangeOk getRow 2051521 566750 568233 :=
  s_568166.append (by norm_num) r_568166
private theorem s_568301 : RangeOk getRow 2051521 566750 568301 :=
  s_568233.append (by norm_num) r_568233
private theorem s_568369 : RangeOk getRow 2051521 566750 568369 :=
  s_568301.append (by norm_num) r_568301
private theorem s_568437 : RangeOk getRow 2051521 566750 568437 :=
  s_568369.append (by norm_num) r_568369
private theorem s_568504 : RangeOk getRow 2051521 566750 568504 :=
  s_568437.append (by norm_num) r_568437
private theorem s_568571 : RangeOk getRow 2051521 566750 568571 :=
  s_568504.append (by norm_num) r_568504
private theorem s_568637 : RangeOk getRow 2051521 566750 568637 :=
  s_568571.append (by norm_num) r_568571
private theorem s_568705 : RangeOk getRow 2051521 566750 568705 :=
  s_568637.append (by norm_num) r_568637
private theorem s_568771 : RangeOk getRow 2051521 566750 568771 :=
  s_568705.append (by norm_num) r_568705
private theorem s_568840 : RangeOk getRow 2051521 566750 568840 :=
  s_568771.append (by norm_num) r_568771
private theorem s_568908 : RangeOk getRow 2051521 566750 568908 :=
  s_568840.append (by norm_num) r_568840
private theorem s_568976 : RangeOk getRow 2051521 566750 568976 :=
  s_568908.append (by norm_num) r_568908
private theorem s_569042 : RangeOk getRow 2051521 566750 569042 :=
  s_568976.append (by norm_num) r_568976

/-- Rows `[566750, 569042)` are valid. -/
theorem rangeOk_566750_569042 : RangeOk getRow 2051521 566750 569042 := s_569042

end Noperthedron.Solution
