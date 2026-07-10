import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[673713, 676000). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_673713 : RangeOk getRow 2051521 673713 673781 := by
  decide +kernel

private theorem r_673781 : RangeOk getRow 2051521 673781 673849 := by
  decide +kernel

private theorem r_673849 : RangeOk getRow 2051521 673849 673917 := by
  decide +kernel

private theorem r_673917 : RangeOk getRow 2051521 673917 673987 := by
  decide +kernel

private theorem r_673987 : RangeOk getRow 2051521 673987 674054 := by
  decide +kernel

private theorem r_674054 : RangeOk getRow 2051521 674054 674121 := by
  decide +kernel

private theorem r_674121 : RangeOk getRow 2051521 674121 674187 := by
  decide +kernel

private theorem r_674187 : RangeOk getRow 2051521 674187 674252 := by
  decide +kernel

private theorem r_674252 : RangeOk getRow 2051521 674252 674317 := by
  decide +kernel

private theorem r_674317 : RangeOk getRow 2051521 674317 674384 := by
  decide +kernel

private theorem r_674384 : RangeOk getRow 2051521 674384 674451 := by
  decide +kernel

private theorem r_674451 : RangeOk getRow 2051521 674451 674518 := by
  decide +kernel

private theorem r_674518 : RangeOk getRow 2051521 674518 674586 := by
  decide +kernel

private theorem r_674586 : RangeOk getRow 2051521 674586 674651 := by
  decide +kernel

private theorem r_674651 : RangeOk getRow 2051521 674651 674718 := by
  decide +kernel

private theorem r_674718 : RangeOk getRow 2051521 674718 674783 := by
  decide +kernel

private theorem r_674783 : RangeOk getRow 2051521 674783 674852 := by
  decide +kernel

private theorem r_674852 : RangeOk getRow 2051521 674852 674919 := by
  decide +kernel

private theorem r_674919 : RangeOk getRow 2051521 674919 674987 := by
  decide +kernel

private theorem r_674987 : RangeOk getRow 2051521 674987 675055 := by
  decide +kernel

private theorem r_675055 : RangeOk getRow 2051521 675055 675124 := by
  decide +kernel

private theorem r_675124 : RangeOk getRow 2051521 675124 675191 := by
  decide +kernel

private theorem r_675191 : RangeOk getRow 2051521 675191 675258 := by
  decide +kernel

private theorem r_675258 : RangeOk getRow 2051521 675258 675325 := by
  decide +kernel

private theorem r_675325 : RangeOk getRow 2051521 675325 675392 := by
  decide +kernel

private theorem r_675392 : RangeOk getRow 2051521 675392 675460 := by
  decide +kernel

private theorem r_675460 : RangeOk getRow 2051521 675460 675528 := by
  decide +kernel

private theorem r_675528 : RangeOk getRow 2051521 675528 675596 := by
  decide +kernel

private theorem r_675596 : RangeOk getRow 2051521 675596 675664 := by
  decide +kernel

private theorem r_675664 : RangeOk getRow 2051521 675664 675731 := by
  decide +kernel

private theorem r_675731 : RangeOk getRow 2051521 675731 675799 := by
  decide +kernel

private theorem r_675799 : RangeOk getRow 2051521 675799 675866 := by
  decide +kernel

private theorem r_675866 : RangeOk getRow 2051521 675866 675932 := by
  decide +kernel

private theorem r_675932 : RangeOk getRow 2051521 675932 676000 := by
  decide +kernel

private theorem s_673781 : RangeOk getRow 2051521 673713 673781 := r_673713
private theorem s_673849 : RangeOk getRow 2051521 673713 673849 :=
  s_673781.append (by norm_num) r_673781
private theorem s_673917 : RangeOk getRow 2051521 673713 673917 :=
  s_673849.append (by norm_num) r_673849
private theorem s_673987 : RangeOk getRow 2051521 673713 673987 :=
  s_673917.append (by norm_num) r_673917
private theorem s_674054 : RangeOk getRow 2051521 673713 674054 :=
  s_673987.append (by norm_num) r_673987
private theorem s_674121 : RangeOk getRow 2051521 673713 674121 :=
  s_674054.append (by norm_num) r_674054
private theorem s_674187 : RangeOk getRow 2051521 673713 674187 :=
  s_674121.append (by norm_num) r_674121
private theorem s_674252 : RangeOk getRow 2051521 673713 674252 :=
  s_674187.append (by norm_num) r_674187
private theorem s_674317 : RangeOk getRow 2051521 673713 674317 :=
  s_674252.append (by norm_num) r_674252
private theorem s_674384 : RangeOk getRow 2051521 673713 674384 :=
  s_674317.append (by norm_num) r_674317
private theorem s_674451 : RangeOk getRow 2051521 673713 674451 :=
  s_674384.append (by norm_num) r_674384
private theorem s_674518 : RangeOk getRow 2051521 673713 674518 :=
  s_674451.append (by norm_num) r_674451
private theorem s_674586 : RangeOk getRow 2051521 673713 674586 :=
  s_674518.append (by norm_num) r_674518
private theorem s_674651 : RangeOk getRow 2051521 673713 674651 :=
  s_674586.append (by norm_num) r_674586
private theorem s_674718 : RangeOk getRow 2051521 673713 674718 :=
  s_674651.append (by norm_num) r_674651
private theorem s_674783 : RangeOk getRow 2051521 673713 674783 :=
  s_674718.append (by norm_num) r_674718
private theorem s_674852 : RangeOk getRow 2051521 673713 674852 :=
  s_674783.append (by norm_num) r_674783
private theorem s_674919 : RangeOk getRow 2051521 673713 674919 :=
  s_674852.append (by norm_num) r_674852
private theorem s_674987 : RangeOk getRow 2051521 673713 674987 :=
  s_674919.append (by norm_num) r_674919
private theorem s_675055 : RangeOk getRow 2051521 673713 675055 :=
  s_674987.append (by norm_num) r_674987
private theorem s_675124 : RangeOk getRow 2051521 673713 675124 :=
  s_675055.append (by norm_num) r_675055
private theorem s_675191 : RangeOk getRow 2051521 673713 675191 :=
  s_675124.append (by norm_num) r_675124
private theorem s_675258 : RangeOk getRow 2051521 673713 675258 :=
  s_675191.append (by norm_num) r_675191
private theorem s_675325 : RangeOk getRow 2051521 673713 675325 :=
  s_675258.append (by norm_num) r_675258
private theorem s_675392 : RangeOk getRow 2051521 673713 675392 :=
  s_675325.append (by norm_num) r_675325
private theorem s_675460 : RangeOk getRow 2051521 673713 675460 :=
  s_675392.append (by norm_num) r_675392
private theorem s_675528 : RangeOk getRow 2051521 673713 675528 :=
  s_675460.append (by norm_num) r_675460
private theorem s_675596 : RangeOk getRow 2051521 673713 675596 :=
  s_675528.append (by norm_num) r_675528
private theorem s_675664 : RangeOk getRow 2051521 673713 675664 :=
  s_675596.append (by norm_num) r_675596
private theorem s_675731 : RangeOk getRow 2051521 673713 675731 :=
  s_675664.append (by norm_num) r_675664
private theorem s_675799 : RangeOk getRow 2051521 673713 675799 :=
  s_675731.append (by norm_num) r_675731
private theorem s_675866 : RangeOk getRow 2051521 673713 675866 :=
  s_675799.append (by norm_num) r_675799
private theorem s_675932 : RangeOk getRow 2051521 673713 675932 :=
  s_675866.append (by norm_num) r_675866
private theorem s_676000 : RangeOk getRow 2051521 673713 676000 :=
  s_675932.append (by norm_num) r_675932

/-- Rows `[673713, 676000)` are valid. -/
theorem rangeOk_673713_676000 : RangeOk getRow 2051521 673713 676000 := s_676000

end Noperthedron.Solution
