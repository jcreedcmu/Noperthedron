import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[142473, 144204). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_142473 : RangeOk getRow 2051521 142473 142538 := by
  decide +kernel

private theorem r_142538 : RangeOk getRow 2051521 142538 142602 := by
  decide +kernel

private theorem r_142602 : RangeOk getRow 2051521 142602 142667 := by
  decide +kernel

private theorem r_142667 : RangeOk getRow 2051521 142667 142732 := by
  decide +kernel

private theorem r_142732 : RangeOk getRow 2051521 142732 142796 := by
  decide +kernel

private theorem r_142796 : RangeOk getRow 2051521 142796 142860 := by
  decide +kernel

private theorem r_142860 : RangeOk getRow 2051521 142860 142924 := by
  decide +kernel

private theorem r_142924 : RangeOk getRow 2051521 142924 142988 := by
  decide +kernel

private theorem r_142988 : RangeOk getRow 2051521 142988 143052 := by
  decide +kernel

private theorem r_143052 : RangeOk getRow 2051521 143052 143116 := by
  decide +kernel

private theorem r_143116 : RangeOk getRow 2051521 143116 143180 := by
  decide +kernel

private theorem r_143180 : RangeOk getRow 2051521 143180 143244 := by
  decide +kernel

private theorem r_143244 : RangeOk getRow 2051521 143244 143308 := by
  decide +kernel

private theorem r_143308 : RangeOk getRow 2051521 143308 143372 := by
  decide +kernel

private theorem r_143372 : RangeOk getRow 2051521 143372 143436 := by
  decide +kernel

private theorem r_143436 : RangeOk getRow 2051521 143436 143500 := by
  decide +kernel

private theorem r_143500 : RangeOk getRow 2051521 143500 143564 := by
  decide +kernel

private theorem r_143564 : RangeOk getRow 2051521 143564 143628 := by
  decide +kernel

private theorem r_143628 : RangeOk getRow 2051521 143628 143692 := by
  decide +kernel

private theorem r_143692 : RangeOk getRow 2051521 143692 143756 := by
  decide +kernel

private theorem r_143756 : RangeOk getRow 2051521 143756 143820 := by
  decide +kernel

private theorem r_143820 : RangeOk getRow 2051521 143820 143884 := by
  decide +kernel

private theorem r_143884 : RangeOk getRow 2051521 143884 143948 := by
  decide +kernel

private theorem r_143948 : RangeOk getRow 2051521 143948 144012 := by
  decide +kernel

private theorem r_144012 : RangeOk getRow 2051521 144012 144076 := by
  decide +kernel

private theorem r_144076 : RangeOk getRow 2051521 144076 144140 := by
  decide +kernel

private theorem r_144140 : RangeOk getRow 2051521 144140 144204 := by
  decide +kernel

private theorem s_142538 : RangeOk getRow 2051521 142473 142538 := r_142473
private theorem s_142602 : RangeOk getRow 2051521 142473 142602 :=
  s_142538.append (by norm_num) r_142538
private theorem s_142667 : RangeOk getRow 2051521 142473 142667 :=
  s_142602.append (by norm_num) r_142602
private theorem s_142732 : RangeOk getRow 2051521 142473 142732 :=
  s_142667.append (by norm_num) r_142667
private theorem s_142796 : RangeOk getRow 2051521 142473 142796 :=
  s_142732.append (by norm_num) r_142732
private theorem s_142860 : RangeOk getRow 2051521 142473 142860 :=
  s_142796.append (by norm_num) r_142796
private theorem s_142924 : RangeOk getRow 2051521 142473 142924 :=
  s_142860.append (by norm_num) r_142860
private theorem s_142988 : RangeOk getRow 2051521 142473 142988 :=
  s_142924.append (by norm_num) r_142924
private theorem s_143052 : RangeOk getRow 2051521 142473 143052 :=
  s_142988.append (by norm_num) r_142988
private theorem s_143116 : RangeOk getRow 2051521 142473 143116 :=
  s_143052.append (by norm_num) r_143052
private theorem s_143180 : RangeOk getRow 2051521 142473 143180 :=
  s_143116.append (by norm_num) r_143116
private theorem s_143244 : RangeOk getRow 2051521 142473 143244 :=
  s_143180.append (by norm_num) r_143180
private theorem s_143308 : RangeOk getRow 2051521 142473 143308 :=
  s_143244.append (by norm_num) r_143244
private theorem s_143372 : RangeOk getRow 2051521 142473 143372 :=
  s_143308.append (by norm_num) r_143308
private theorem s_143436 : RangeOk getRow 2051521 142473 143436 :=
  s_143372.append (by norm_num) r_143372
private theorem s_143500 : RangeOk getRow 2051521 142473 143500 :=
  s_143436.append (by norm_num) r_143436
private theorem s_143564 : RangeOk getRow 2051521 142473 143564 :=
  s_143500.append (by norm_num) r_143500
private theorem s_143628 : RangeOk getRow 2051521 142473 143628 :=
  s_143564.append (by norm_num) r_143564
private theorem s_143692 : RangeOk getRow 2051521 142473 143692 :=
  s_143628.append (by norm_num) r_143628
private theorem s_143756 : RangeOk getRow 2051521 142473 143756 :=
  s_143692.append (by norm_num) r_143692
private theorem s_143820 : RangeOk getRow 2051521 142473 143820 :=
  s_143756.append (by norm_num) r_143756
private theorem s_143884 : RangeOk getRow 2051521 142473 143884 :=
  s_143820.append (by norm_num) r_143820
private theorem s_143948 : RangeOk getRow 2051521 142473 143948 :=
  s_143884.append (by norm_num) r_143884
private theorem s_144012 : RangeOk getRow 2051521 142473 144012 :=
  s_143948.append (by norm_num) r_143948
private theorem s_144076 : RangeOk getRow 2051521 142473 144076 :=
  s_144012.append (by norm_num) r_144012
private theorem s_144140 : RangeOk getRow 2051521 142473 144140 :=
  s_144076.append (by norm_num) r_144076
private theorem s_144204 : RangeOk getRow 2051521 142473 144204 :=
  s_144140.append (by norm_num) r_144140

/-- Rows `[142473, 144204)` are valid. -/
theorem rangeOk_142473_144204 : RangeOk getRow 2051521 142473 144204 := s_144204

end Noperthedron.Solution
