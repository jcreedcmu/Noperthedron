import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[512391, 514769). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_512391 : RangeOk getRow 2051521 512391 512458 := by
  decide +kernel

private theorem r_512458 : RangeOk getRow 2051521 512458 512523 := by
  decide +kernel

private theorem r_512523 : RangeOk getRow 2051521 512523 512589 := by
  decide +kernel

private theorem r_512589 : RangeOk getRow 2051521 512589 512656 := by
  decide +kernel

private theorem r_512656 : RangeOk getRow 2051521 512656 512721 := by
  decide +kernel

private theorem r_512721 : RangeOk getRow 2051521 512721 512788 := by
  decide +kernel

private theorem r_512788 : RangeOk getRow 2051521 512788 512854 := by
  decide +kernel

private theorem r_512854 : RangeOk getRow 2051521 512854 512921 := by
  decide +kernel

private theorem r_512921 : RangeOk getRow 2051521 512921 512986 := by
  decide +kernel

private theorem r_512986 : RangeOk getRow 2051521 512986 513051 := by
  decide +kernel

private theorem r_513051 : RangeOk getRow 2051521 513051 513118 := by
  decide +kernel

private theorem r_513118 : RangeOk getRow 2051521 513118 513185 := by
  decide +kernel

private theorem r_513185 : RangeOk getRow 2051521 513185 513254 := by
  decide +kernel

private theorem r_513254 : RangeOk getRow 2051521 513254 513323 := by
  decide +kernel

private theorem r_513323 : RangeOk getRow 2051521 513323 513393 := by
  decide +kernel

private theorem r_513393 : RangeOk getRow 2051521 513393 513463 := by
  decide +kernel

private theorem r_513463 : RangeOk getRow 2051521 513463 513532 := by
  decide +kernel

private theorem r_513532 : RangeOk getRow 2051521 513532 513601 := by
  decide +kernel

private theorem r_513601 : RangeOk getRow 2051521 513601 513668 := by
  decide +kernel

private theorem r_513668 : RangeOk getRow 2051521 513668 513736 := by
  decide +kernel

private theorem r_513736 : RangeOk getRow 2051521 513736 513805 := by
  decide +kernel

private theorem r_513805 : RangeOk getRow 2051521 513805 513873 := by
  decide +kernel

private theorem r_513873 : RangeOk getRow 2051521 513873 513941 := by
  decide +kernel

private theorem r_513941 : RangeOk getRow 2051521 513941 514010 := by
  decide +kernel

private theorem r_514010 : RangeOk getRow 2051521 514010 514080 := by
  decide +kernel

private theorem r_514080 : RangeOk getRow 2051521 514080 514151 := by
  decide +kernel

private theorem r_514151 : RangeOk getRow 2051521 514151 514222 := by
  decide +kernel

private theorem r_514222 : RangeOk getRow 2051521 514222 514292 := by
  decide +kernel

private theorem r_514292 : RangeOk getRow 2051521 514292 514361 := by
  decide +kernel

private theorem r_514361 : RangeOk getRow 2051521 514361 514428 := by
  decide +kernel

private theorem r_514428 : RangeOk getRow 2051521 514428 514496 := by
  decide +kernel

private theorem r_514496 : RangeOk getRow 2051521 514496 514564 := by
  decide +kernel

private theorem r_514564 : RangeOk getRow 2051521 514564 514634 := by
  decide +kernel

private theorem r_514634 : RangeOk getRow 2051521 514634 514701 := by
  decide +kernel

private theorem r_514701 : RangeOk getRow 2051521 514701 514769 := by
  decide +kernel

private theorem s_512458 : RangeOk getRow 2051521 512391 512458 := r_512391
private theorem s_512523 : RangeOk getRow 2051521 512391 512523 :=
  s_512458.append (by norm_num) r_512458
private theorem s_512589 : RangeOk getRow 2051521 512391 512589 :=
  s_512523.append (by norm_num) r_512523
private theorem s_512656 : RangeOk getRow 2051521 512391 512656 :=
  s_512589.append (by norm_num) r_512589
private theorem s_512721 : RangeOk getRow 2051521 512391 512721 :=
  s_512656.append (by norm_num) r_512656
private theorem s_512788 : RangeOk getRow 2051521 512391 512788 :=
  s_512721.append (by norm_num) r_512721
private theorem s_512854 : RangeOk getRow 2051521 512391 512854 :=
  s_512788.append (by norm_num) r_512788
private theorem s_512921 : RangeOk getRow 2051521 512391 512921 :=
  s_512854.append (by norm_num) r_512854
private theorem s_512986 : RangeOk getRow 2051521 512391 512986 :=
  s_512921.append (by norm_num) r_512921
private theorem s_513051 : RangeOk getRow 2051521 512391 513051 :=
  s_512986.append (by norm_num) r_512986
private theorem s_513118 : RangeOk getRow 2051521 512391 513118 :=
  s_513051.append (by norm_num) r_513051
private theorem s_513185 : RangeOk getRow 2051521 512391 513185 :=
  s_513118.append (by norm_num) r_513118
private theorem s_513254 : RangeOk getRow 2051521 512391 513254 :=
  s_513185.append (by norm_num) r_513185
private theorem s_513323 : RangeOk getRow 2051521 512391 513323 :=
  s_513254.append (by norm_num) r_513254
private theorem s_513393 : RangeOk getRow 2051521 512391 513393 :=
  s_513323.append (by norm_num) r_513323
private theorem s_513463 : RangeOk getRow 2051521 512391 513463 :=
  s_513393.append (by norm_num) r_513393
private theorem s_513532 : RangeOk getRow 2051521 512391 513532 :=
  s_513463.append (by norm_num) r_513463
private theorem s_513601 : RangeOk getRow 2051521 512391 513601 :=
  s_513532.append (by norm_num) r_513532
private theorem s_513668 : RangeOk getRow 2051521 512391 513668 :=
  s_513601.append (by norm_num) r_513601
private theorem s_513736 : RangeOk getRow 2051521 512391 513736 :=
  s_513668.append (by norm_num) r_513668
private theorem s_513805 : RangeOk getRow 2051521 512391 513805 :=
  s_513736.append (by norm_num) r_513736
private theorem s_513873 : RangeOk getRow 2051521 512391 513873 :=
  s_513805.append (by norm_num) r_513805
private theorem s_513941 : RangeOk getRow 2051521 512391 513941 :=
  s_513873.append (by norm_num) r_513873
private theorem s_514010 : RangeOk getRow 2051521 512391 514010 :=
  s_513941.append (by norm_num) r_513941
private theorem s_514080 : RangeOk getRow 2051521 512391 514080 :=
  s_514010.append (by norm_num) r_514010
private theorem s_514151 : RangeOk getRow 2051521 512391 514151 :=
  s_514080.append (by norm_num) r_514080
private theorem s_514222 : RangeOk getRow 2051521 512391 514222 :=
  s_514151.append (by norm_num) r_514151
private theorem s_514292 : RangeOk getRow 2051521 512391 514292 :=
  s_514222.append (by norm_num) r_514222
private theorem s_514361 : RangeOk getRow 2051521 512391 514361 :=
  s_514292.append (by norm_num) r_514292
private theorem s_514428 : RangeOk getRow 2051521 512391 514428 :=
  s_514361.append (by norm_num) r_514361
private theorem s_514496 : RangeOk getRow 2051521 512391 514496 :=
  s_514428.append (by norm_num) r_514428
private theorem s_514564 : RangeOk getRow 2051521 512391 514564 :=
  s_514496.append (by norm_num) r_514496
private theorem s_514634 : RangeOk getRow 2051521 512391 514634 :=
  s_514564.append (by norm_num) r_514564
private theorem s_514701 : RangeOk getRow 2051521 512391 514701 :=
  s_514634.append (by norm_num) r_514634
private theorem s_514769 : RangeOk getRow 2051521 512391 514769 :=
  s_514701.append (by norm_num) r_514701

/-- Rows `[512391, 514769)` are valid. -/
theorem rangeOk_512391_514769 : RangeOk getRow 2051521 512391 514769 := s_514769

end Noperthedron.Solution
