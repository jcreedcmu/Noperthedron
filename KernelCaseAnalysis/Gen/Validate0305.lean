import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[735559, 737686). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_735559 : RangeOk getRow 2051521 735559 735626 := by
  decide +kernel

private theorem r_735626 : RangeOk getRow 2051521 735626 735696 := by
  decide +kernel

private theorem r_735696 : RangeOk getRow 2051521 735696 735764 := by
  decide +kernel

private theorem r_735764 : RangeOk getRow 2051521 735764 735829 := by
  decide +kernel

private theorem r_735829 : RangeOk getRow 2051521 735829 735896 := by
  decide +kernel

private theorem r_735896 : RangeOk getRow 2051521 735896 735963 := by
  decide +kernel

private theorem r_735963 : RangeOk getRow 2051521 735963 736028 := by
  decide +kernel

private theorem r_736028 : RangeOk getRow 2051521 736028 736095 := by
  decide +kernel

private theorem r_736095 : RangeOk getRow 2051521 736095 736162 := by
  decide +kernel

private theorem r_736162 : RangeOk getRow 2051521 736162 736229 := by
  decide +kernel

private theorem r_736229 : RangeOk getRow 2051521 736229 736297 := by
  decide +kernel

private theorem r_736297 : RangeOk getRow 2051521 736297 736364 := by
  decide +kernel

private theorem r_736364 : RangeOk getRow 2051521 736364 736429 := by
  decide +kernel

private theorem r_736429 : RangeOk getRow 2051521 736429 736493 := by
  decide +kernel

private theorem r_736493 : RangeOk getRow 2051521 736493 736558 := by
  decide +kernel

private theorem r_736558 : RangeOk getRow 2051521 736558 736624 := by
  decide +kernel

private theorem r_736624 : RangeOk getRow 2051521 736624 736690 := by
  decide +kernel

private theorem r_736690 : RangeOk getRow 2051521 736690 736755 := by
  decide +kernel

private theorem r_736755 : RangeOk getRow 2051521 736755 736822 := by
  decide +kernel

private theorem r_736822 : RangeOk getRow 2051521 736822 736887 := by
  decide +kernel

private theorem r_736887 : RangeOk getRow 2051521 736887 736951 := by
  decide +kernel

private theorem r_736951 : RangeOk getRow 2051521 736951 737017 := by
  decide +kernel

private theorem r_737017 : RangeOk getRow 2051521 737017 737087 := by
  decide +kernel

private theorem r_737087 : RangeOk getRow 2051521 737087 737153 := by
  decide +kernel

private theorem r_737153 : RangeOk getRow 2051521 737153 737218 := by
  decide +kernel

private theorem r_737218 : RangeOk getRow 2051521 737218 737285 := by
  decide +kernel

private theorem r_737285 : RangeOk getRow 2051521 737285 737351 := by
  decide +kernel

private theorem r_737351 : RangeOk getRow 2051521 737351 737417 := by
  decide +kernel

private theorem r_737417 : RangeOk getRow 2051521 737417 737484 := by
  decide +kernel

private theorem r_737484 : RangeOk getRow 2051521 737484 737552 := by
  decide +kernel

private theorem r_737552 : RangeOk getRow 2051521 737552 737618 := by
  decide +kernel

private theorem r_737618 : RangeOk getRow 2051521 737618 737686 := by
  decide +kernel

private theorem s_735626 : RangeOk getRow 2051521 735559 735626 := r_735559
private theorem s_735696 : RangeOk getRow 2051521 735559 735696 :=
  s_735626.append (by norm_num) r_735626
private theorem s_735764 : RangeOk getRow 2051521 735559 735764 :=
  s_735696.append (by norm_num) r_735696
private theorem s_735829 : RangeOk getRow 2051521 735559 735829 :=
  s_735764.append (by norm_num) r_735764
private theorem s_735896 : RangeOk getRow 2051521 735559 735896 :=
  s_735829.append (by norm_num) r_735829
private theorem s_735963 : RangeOk getRow 2051521 735559 735963 :=
  s_735896.append (by norm_num) r_735896
private theorem s_736028 : RangeOk getRow 2051521 735559 736028 :=
  s_735963.append (by norm_num) r_735963
private theorem s_736095 : RangeOk getRow 2051521 735559 736095 :=
  s_736028.append (by norm_num) r_736028
private theorem s_736162 : RangeOk getRow 2051521 735559 736162 :=
  s_736095.append (by norm_num) r_736095
private theorem s_736229 : RangeOk getRow 2051521 735559 736229 :=
  s_736162.append (by norm_num) r_736162
private theorem s_736297 : RangeOk getRow 2051521 735559 736297 :=
  s_736229.append (by norm_num) r_736229
private theorem s_736364 : RangeOk getRow 2051521 735559 736364 :=
  s_736297.append (by norm_num) r_736297
private theorem s_736429 : RangeOk getRow 2051521 735559 736429 :=
  s_736364.append (by norm_num) r_736364
private theorem s_736493 : RangeOk getRow 2051521 735559 736493 :=
  s_736429.append (by norm_num) r_736429
private theorem s_736558 : RangeOk getRow 2051521 735559 736558 :=
  s_736493.append (by norm_num) r_736493
private theorem s_736624 : RangeOk getRow 2051521 735559 736624 :=
  s_736558.append (by norm_num) r_736558
private theorem s_736690 : RangeOk getRow 2051521 735559 736690 :=
  s_736624.append (by norm_num) r_736624
private theorem s_736755 : RangeOk getRow 2051521 735559 736755 :=
  s_736690.append (by norm_num) r_736690
private theorem s_736822 : RangeOk getRow 2051521 735559 736822 :=
  s_736755.append (by norm_num) r_736755
private theorem s_736887 : RangeOk getRow 2051521 735559 736887 :=
  s_736822.append (by norm_num) r_736822
private theorem s_736951 : RangeOk getRow 2051521 735559 736951 :=
  s_736887.append (by norm_num) r_736887
private theorem s_737017 : RangeOk getRow 2051521 735559 737017 :=
  s_736951.append (by norm_num) r_736951
private theorem s_737087 : RangeOk getRow 2051521 735559 737087 :=
  s_737017.append (by norm_num) r_737017
private theorem s_737153 : RangeOk getRow 2051521 735559 737153 :=
  s_737087.append (by norm_num) r_737087
private theorem s_737218 : RangeOk getRow 2051521 735559 737218 :=
  s_737153.append (by norm_num) r_737153
private theorem s_737285 : RangeOk getRow 2051521 735559 737285 :=
  s_737218.append (by norm_num) r_737218
private theorem s_737351 : RangeOk getRow 2051521 735559 737351 :=
  s_737285.append (by norm_num) r_737285
private theorem s_737417 : RangeOk getRow 2051521 735559 737417 :=
  s_737351.append (by norm_num) r_737351
private theorem s_737484 : RangeOk getRow 2051521 735559 737484 :=
  s_737417.append (by norm_num) r_737417
private theorem s_737552 : RangeOk getRow 2051521 735559 737552 :=
  s_737484.append (by norm_num) r_737484
private theorem s_737618 : RangeOk getRow 2051521 735559 737618 :=
  s_737552.append (by norm_num) r_737552
private theorem s_737686 : RangeOk getRow 2051521 735559 737686 :=
  s_737618.append (by norm_num) r_737618

/-- Rows `[735559, 737686)` are valid. -/
theorem rangeOk_735559_737686 : RangeOk getRow 2051521 735559 737686 := s_737686

end Noperthedron.Solution
