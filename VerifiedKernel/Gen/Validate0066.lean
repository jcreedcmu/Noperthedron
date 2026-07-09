import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[144204, 145925). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_144204 : RangeOk getRow 2051521 144204 144268 := by
  decide +kernel

private theorem r_144268 : RangeOk getRow 2051521 144268 144332 := by
  decide +kernel

private theorem r_144332 : RangeOk getRow 2051521 144332 144396 := by
  decide +kernel

private theorem r_144396 : RangeOk getRow 2051521 144396 144460 := by
  decide +kernel

private theorem r_144460 : RangeOk getRow 2051521 144460 144524 := by
  decide +kernel

private theorem r_144524 : RangeOk getRow 2051521 144524 144588 := by
  decide +kernel

private theorem r_144588 : RangeOk getRow 2051521 144588 144652 := by
  decide +kernel

private theorem r_144652 : RangeOk getRow 2051521 144652 144716 := by
  decide +kernel

private theorem r_144716 : RangeOk getRow 2051521 144716 144780 := by
  decide +kernel

private theorem r_144780 : RangeOk getRow 2051521 144780 144844 := by
  decide +kernel

private theorem r_144844 : RangeOk getRow 2051521 144844 144908 := by
  decide +kernel

private theorem r_144908 : RangeOk getRow 2051521 144908 144972 := by
  decide +kernel

private theorem r_144972 : RangeOk getRow 2051521 144972 145036 := by
  decide +kernel

private theorem r_145036 : RangeOk getRow 2051521 145036 145100 := by
  decide +kernel

private theorem r_145100 : RangeOk getRow 2051521 145100 145164 := by
  decide +kernel

private theorem r_145164 : RangeOk getRow 2051521 145164 145228 := by
  decide +kernel

private theorem r_145228 : RangeOk getRow 2051521 145228 145292 := by
  decide +kernel

private theorem r_145292 : RangeOk getRow 2051521 145292 145357 := by
  decide +kernel

private theorem r_145357 : RangeOk getRow 2051521 145357 145422 := by
  decide +kernel

private theorem r_145422 : RangeOk getRow 2051521 145422 145486 := by
  decide +kernel

private theorem r_145486 : RangeOk getRow 2051521 145486 145550 := by
  decide +kernel

private theorem r_145550 : RangeOk getRow 2051521 145550 145614 := by
  decide +kernel

private theorem r_145614 : RangeOk getRow 2051521 145614 145678 := by
  decide +kernel

private theorem r_145678 : RangeOk getRow 2051521 145678 145742 := by
  decide +kernel

private theorem r_145742 : RangeOk getRow 2051521 145742 145806 := by
  decide +kernel

private theorem r_145806 : RangeOk getRow 2051521 145806 145870 := by
  decide +kernel

private theorem r_145870 : RangeOk getRow 2051521 145870 145925 := by
  decide +kernel

private theorem s_144268 : RangeOk getRow 2051521 144204 144268 := r_144204
private theorem s_144332 : RangeOk getRow 2051521 144204 144332 :=
  s_144268.append (by norm_num) r_144268
private theorem s_144396 : RangeOk getRow 2051521 144204 144396 :=
  s_144332.append (by norm_num) r_144332
private theorem s_144460 : RangeOk getRow 2051521 144204 144460 :=
  s_144396.append (by norm_num) r_144396
private theorem s_144524 : RangeOk getRow 2051521 144204 144524 :=
  s_144460.append (by norm_num) r_144460
private theorem s_144588 : RangeOk getRow 2051521 144204 144588 :=
  s_144524.append (by norm_num) r_144524
private theorem s_144652 : RangeOk getRow 2051521 144204 144652 :=
  s_144588.append (by norm_num) r_144588
private theorem s_144716 : RangeOk getRow 2051521 144204 144716 :=
  s_144652.append (by norm_num) r_144652
private theorem s_144780 : RangeOk getRow 2051521 144204 144780 :=
  s_144716.append (by norm_num) r_144716
private theorem s_144844 : RangeOk getRow 2051521 144204 144844 :=
  s_144780.append (by norm_num) r_144780
private theorem s_144908 : RangeOk getRow 2051521 144204 144908 :=
  s_144844.append (by norm_num) r_144844
private theorem s_144972 : RangeOk getRow 2051521 144204 144972 :=
  s_144908.append (by norm_num) r_144908
private theorem s_145036 : RangeOk getRow 2051521 144204 145036 :=
  s_144972.append (by norm_num) r_144972
private theorem s_145100 : RangeOk getRow 2051521 144204 145100 :=
  s_145036.append (by norm_num) r_145036
private theorem s_145164 : RangeOk getRow 2051521 144204 145164 :=
  s_145100.append (by norm_num) r_145100
private theorem s_145228 : RangeOk getRow 2051521 144204 145228 :=
  s_145164.append (by norm_num) r_145164
private theorem s_145292 : RangeOk getRow 2051521 144204 145292 :=
  s_145228.append (by norm_num) r_145228
private theorem s_145357 : RangeOk getRow 2051521 144204 145357 :=
  s_145292.append (by norm_num) r_145292
private theorem s_145422 : RangeOk getRow 2051521 144204 145422 :=
  s_145357.append (by norm_num) r_145357
private theorem s_145486 : RangeOk getRow 2051521 144204 145486 :=
  s_145422.append (by norm_num) r_145422
private theorem s_145550 : RangeOk getRow 2051521 144204 145550 :=
  s_145486.append (by norm_num) r_145486
private theorem s_145614 : RangeOk getRow 2051521 144204 145614 :=
  s_145550.append (by norm_num) r_145550
private theorem s_145678 : RangeOk getRow 2051521 144204 145678 :=
  s_145614.append (by norm_num) r_145614
private theorem s_145742 : RangeOk getRow 2051521 144204 145742 :=
  s_145678.append (by norm_num) r_145678
private theorem s_145806 : RangeOk getRow 2051521 144204 145806 :=
  s_145742.append (by norm_num) r_145742
private theorem s_145870 : RangeOk getRow 2051521 144204 145870 :=
  s_145806.append (by norm_num) r_145806
private theorem s_145925 : RangeOk getRow 2051521 144204 145925 :=
  s_145870.append (by norm_num) r_145870

/-- Rows `[144204, 145925)` are valid. -/
theorem rangeOk_144204_145925 : RangeOk getRow 2051521 144204 145925 := s_145925

end Noperthedron.Solution
