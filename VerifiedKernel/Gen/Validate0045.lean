import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[95223, 96951). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_95223 : RangeOk getRow 2051521 95223 95287 := by
  decide +kernel

private theorem r_95287 : RangeOk getRow 2051521 95287 95351 := by
  decide +kernel

private theorem r_95351 : RangeOk getRow 2051521 95351 95415 := by
  decide +kernel

private theorem r_95415 : RangeOk getRow 2051521 95415 95479 := by
  decide +kernel

private theorem r_95479 : RangeOk getRow 2051521 95479 95543 := by
  decide +kernel

private theorem r_95543 : RangeOk getRow 2051521 95543 95607 := by
  decide +kernel

private theorem r_95607 : RangeOk getRow 2051521 95607 95671 := by
  decide +kernel

private theorem r_95671 : RangeOk getRow 2051521 95671 95735 := by
  decide +kernel

private theorem r_95735 : RangeOk getRow 2051521 95735 95799 := by
  decide +kernel

private theorem r_95799 : RangeOk getRow 2051521 95799 95863 := by
  decide +kernel

private theorem r_95863 : RangeOk getRow 2051521 95863 95927 := by
  decide +kernel

private theorem r_95927 : RangeOk getRow 2051521 95927 95991 := by
  decide +kernel

private theorem r_95991 : RangeOk getRow 2051521 95991 96055 := by
  decide +kernel

private theorem r_96055 : RangeOk getRow 2051521 96055 96119 := by
  decide +kernel

private theorem r_96119 : RangeOk getRow 2051521 96119 96183 := by
  decide +kernel

private theorem r_96183 : RangeOk getRow 2051521 96183 96247 := by
  decide +kernel

private theorem r_96247 : RangeOk getRow 2051521 96247 96311 := by
  decide +kernel

private theorem r_96311 : RangeOk getRow 2051521 96311 96375 := by
  decide +kernel

private theorem r_96375 : RangeOk getRow 2051521 96375 96439 := by
  decide +kernel

private theorem r_96439 : RangeOk getRow 2051521 96439 96503 := by
  decide +kernel

private theorem r_96503 : RangeOk getRow 2051521 96503 96567 := by
  decide +kernel

private theorem r_96567 : RangeOk getRow 2051521 96567 96631 := by
  decide +kernel

private theorem r_96631 : RangeOk getRow 2051521 96631 96695 := by
  decide +kernel

private theorem r_96695 : RangeOk getRow 2051521 96695 96759 := by
  decide +kernel

private theorem r_96759 : RangeOk getRow 2051521 96759 96823 := by
  decide +kernel

private theorem r_96823 : RangeOk getRow 2051521 96823 96887 := by
  decide +kernel

private theorem r_96887 : RangeOk getRow 2051521 96887 96951 := by
  decide +kernel

private theorem s_95287 : RangeOk getRow 2051521 95223 95287 := r_95223
private theorem s_95351 : RangeOk getRow 2051521 95223 95351 :=
  s_95287.append (by norm_num) r_95287
private theorem s_95415 : RangeOk getRow 2051521 95223 95415 :=
  s_95351.append (by norm_num) r_95351
private theorem s_95479 : RangeOk getRow 2051521 95223 95479 :=
  s_95415.append (by norm_num) r_95415
private theorem s_95543 : RangeOk getRow 2051521 95223 95543 :=
  s_95479.append (by norm_num) r_95479
private theorem s_95607 : RangeOk getRow 2051521 95223 95607 :=
  s_95543.append (by norm_num) r_95543
private theorem s_95671 : RangeOk getRow 2051521 95223 95671 :=
  s_95607.append (by norm_num) r_95607
private theorem s_95735 : RangeOk getRow 2051521 95223 95735 :=
  s_95671.append (by norm_num) r_95671
private theorem s_95799 : RangeOk getRow 2051521 95223 95799 :=
  s_95735.append (by norm_num) r_95735
private theorem s_95863 : RangeOk getRow 2051521 95223 95863 :=
  s_95799.append (by norm_num) r_95799
private theorem s_95927 : RangeOk getRow 2051521 95223 95927 :=
  s_95863.append (by norm_num) r_95863
private theorem s_95991 : RangeOk getRow 2051521 95223 95991 :=
  s_95927.append (by norm_num) r_95927
private theorem s_96055 : RangeOk getRow 2051521 95223 96055 :=
  s_95991.append (by norm_num) r_95991
private theorem s_96119 : RangeOk getRow 2051521 95223 96119 :=
  s_96055.append (by norm_num) r_96055
private theorem s_96183 : RangeOk getRow 2051521 95223 96183 :=
  s_96119.append (by norm_num) r_96119
private theorem s_96247 : RangeOk getRow 2051521 95223 96247 :=
  s_96183.append (by norm_num) r_96183
private theorem s_96311 : RangeOk getRow 2051521 95223 96311 :=
  s_96247.append (by norm_num) r_96247
private theorem s_96375 : RangeOk getRow 2051521 95223 96375 :=
  s_96311.append (by norm_num) r_96311
private theorem s_96439 : RangeOk getRow 2051521 95223 96439 :=
  s_96375.append (by norm_num) r_96375
private theorem s_96503 : RangeOk getRow 2051521 95223 96503 :=
  s_96439.append (by norm_num) r_96439
private theorem s_96567 : RangeOk getRow 2051521 95223 96567 :=
  s_96503.append (by norm_num) r_96503
private theorem s_96631 : RangeOk getRow 2051521 95223 96631 :=
  s_96567.append (by norm_num) r_96567
private theorem s_96695 : RangeOk getRow 2051521 95223 96695 :=
  s_96631.append (by norm_num) r_96631
private theorem s_96759 : RangeOk getRow 2051521 95223 96759 :=
  s_96695.append (by norm_num) r_96695
private theorem s_96823 : RangeOk getRow 2051521 95223 96823 :=
  s_96759.append (by norm_num) r_96759
private theorem s_96887 : RangeOk getRow 2051521 95223 96887 :=
  s_96823.append (by norm_num) r_96823
private theorem s_96951 : RangeOk getRow 2051521 95223 96951 :=
  s_96887.append (by norm_num) r_96887

/-- Rows `[95223, 96951)` are valid. -/
theorem rangeOk_95223_96951 : RangeOk getRow 2051521 95223 96951 := s_96951

end Noperthedron.Solution
