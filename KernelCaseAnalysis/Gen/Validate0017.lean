import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[34257, 36057). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_34257 : RangeOk getRow 2051521 34257 34321 := by
  decide +kernel

private theorem r_34321 : RangeOk getRow 2051521 34321 34385 := by
  decide +kernel

private theorem r_34385 : RangeOk getRow 2051521 34385 34449 := by
  decide +kernel

private theorem r_34449 : RangeOk getRow 2051521 34449 34513 := by
  decide +kernel

private theorem r_34513 : RangeOk getRow 2051521 34513 34577 := by
  decide +kernel

private theorem r_34577 : RangeOk getRow 2051521 34577 34641 := by
  decide +kernel

private theorem r_34641 : RangeOk getRow 2051521 34641 34705 := by
  decide +kernel

private theorem r_34705 : RangeOk getRow 2051521 34705 34769 := by
  decide +kernel

private theorem r_34769 : RangeOk getRow 2051521 34769 34833 := by
  decide +kernel

private theorem r_34833 : RangeOk getRow 2051521 34833 34897 := by
  decide +kernel

private theorem r_34897 : RangeOk getRow 2051521 34897 34961 := by
  decide +kernel

private theorem r_34961 : RangeOk getRow 2051521 34961 35025 := by
  decide +kernel

private theorem r_35025 : RangeOk getRow 2051521 35025 35090 := by
  decide +kernel

private theorem r_35090 : RangeOk getRow 2051521 35090 35155 := by
  decide +kernel

private theorem r_35155 : RangeOk getRow 2051521 35155 35219 := by
  decide +kernel

private theorem r_35219 : RangeOk getRow 2051521 35219 35283 := by
  decide +kernel

private theorem r_35283 : RangeOk getRow 2051521 35283 35348 := by
  decide +kernel

private theorem r_35348 : RangeOk getRow 2051521 35348 35413 := by
  decide +kernel

private theorem r_35413 : RangeOk getRow 2051521 35413 35477 := by
  decide +kernel

private theorem r_35477 : RangeOk getRow 2051521 35477 35542 := by
  decide +kernel

private theorem r_35542 : RangeOk getRow 2051521 35542 35607 := by
  decide +kernel

private theorem r_35607 : RangeOk getRow 2051521 35607 35671 := by
  decide +kernel

private theorem r_35671 : RangeOk getRow 2051521 35671 35735 := by
  decide +kernel

private theorem r_35735 : RangeOk getRow 2051521 35735 35799 := by
  decide +kernel

private theorem r_35799 : RangeOk getRow 2051521 35799 35863 := by
  decide +kernel

private theorem r_35863 : RangeOk getRow 2051521 35863 35927 := by
  decide +kernel

private theorem r_35927 : RangeOk getRow 2051521 35927 35992 := by
  decide +kernel

private theorem r_35992 : RangeOk getRow 2051521 35992 36057 := by
  decide +kernel

private theorem s_34321 : RangeOk getRow 2051521 34257 34321 := r_34257
private theorem s_34385 : RangeOk getRow 2051521 34257 34385 :=
  s_34321.append (by norm_num) r_34321
private theorem s_34449 : RangeOk getRow 2051521 34257 34449 :=
  s_34385.append (by norm_num) r_34385
private theorem s_34513 : RangeOk getRow 2051521 34257 34513 :=
  s_34449.append (by norm_num) r_34449
private theorem s_34577 : RangeOk getRow 2051521 34257 34577 :=
  s_34513.append (by norm_num) r_34513
private theorem s_34641 : RangeOk getRow 2051521 34257 34641 :=
  s_34577.append (by norm_num) r_34577
private theorem s_34705 : RangeOk getRow 2051521 34257 34705 :=
  s_34641.append (by norm_num) r_34641
private theorem s_34769 : RangeOk getRow 2051521 34257 34769 :=
  s_34705.append (by norm_num) r_34705
private theorem s_34833 : RangeOk getRow 2051521 34257 34833 :=
  s_34769.append (by norm_num) r_34769
private theorem s_34897 : RangeOk getRow 2051521 34257 34897 :=
  s_34833.append (by norm_num) r_34833
private theorem s_34961 : RangeOk getRow 2051521 34257 34961 :=
  s_34897.append (by norm_num) r_34897
private theorem s_35025 : RangeOk getRow 2051521 34257 35025 :=
  s_34961.append (by norm_num) r_34961
private theorem s_35090 : RangeOk getRow 2051521 34257 35090 :=
  s_35025.append (by norm_num) r_35025
private theorem s_35155 : RangeOk getRow 2051521 34257 35155 :=
  s_35090.append (by norm_num) r_35090
private theorem s_35219 : RangeOk getRow 2051521 34257 35219 :=
  s_35155.append (by norm_num) r_35155
private theorem s_35283 : RangeOk getRow 2051521 34257 35283 :=
  s_35219.append (by norm_num) r_35219
private theorem s_35348 : RangeOk getRow 2051521 34257 35348 :=
  s_35283.append (by norm_num) r_35283
private theorem s_35413 : RangeOk getRow 2051521 34257 35413 :=
  s_35348.append (by norm_num) r_35348
private theorem s_35477 : RangeOk getRow 2051521 34257 35477 :=
  s_35413.append (by norm_num) r_35413
private theorem s_35542 : RangeOk getRow 2051521 34257 35542 :=
  s_35477.append (by norm_num) r_35477
private theorem s_35607 : RangeOk getRow 2051521 34257 35607 :=
  s_35542.append (by norm_num) r_35542
private theorem s_35671 : RangeOk getRow 2051521 34257 35671 :=
  s_35607.append (by norm_num) r_35607
private theorem s_35735 : RangeOk getRow 2051521 34257 35735 :=
  s_35671.append (by norm_num) r_35671
private theorem s_35799 : RangeOk getRow 2051521 34257 35799 :=
  s_35735.append (by norm_num) r_35735
private theorem s_35863 : RangeOk getRow 2051521 34257 35863 :=
  s_35799.append (by norm_num) r_35799
private theorem s_35927 : RangeOk getRow 2051521 34257 35927 :=
  s_35863.append (by norm_num) r_35863
private theorem s_35992 : RangeOk getRow 2051521 34257 35992 :=
  s_35927.append (by norm_num) r_35927
private theorem s_36057 : RangeOk getRow 2051521 34257 36057 :=
  s_35992.append (by norm_num) r_35992

/-- Rows `[34257, 36057)` are valid. -/
theorem rangeOk_34257_36057 : RangeOk getRow 2051521 34257 36057 := s_36057

end Noperthedron.Solution
