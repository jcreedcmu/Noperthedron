import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[140677, 142473). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_140677 : RangeOk getRow 2051521 140677 140741 := by
  decide +kernel

private theorem r_140741 : RangeOk getRow 2051521 140741 140805 := by
  decide +kernel

private theorem r_140805 : RangeOk getRow 2051521 140805 140869 := by
  decide +kernel

private theorem r_140869 : RangeOk getRow 2051521 140869 140933 := by
  decide +kernel

private theorem r_140933 : RangeOk getRow 2051521 140933 140993 := by
  decide +kernel

private theorem r_140993 : RangeOk getRow 2051521 140993 141057 := by
  decide +kernel

private theorem r_141057 : RangeOk getRow 2051521 141057 141121 := by
  decide +kernel

private theorem r_141121 : RangeOk getRow 2051521 141121 141185 := by
  decide +kernel

private theorem r_141185 : RangeOk getRow 2051521 141185 141249 := by
  decide +kernel

private theorem r_141249 : RangeOk getRow 2051521 141249 141314 := by
  decide +kernel

private theorem r_141314 : RangeOk getRow 2051521 141314 141378 := by
  decide +kernel

private theorem r_141378 : RangeOk getRow 2051521 141378 141442 := by
  decide +kernel

private theorem r_141442 : RangeOk getRow 2051521 141442 141506 := by
  decide +kernel

private theorem r_141506 : RangeOk getRow 2051521 141506 141570 := by
  decide +kernel

private theorem r_141570 : RangeOk getRow 2051521 141570 141635 := by
  decide +kernel

private theorem r_141635 : RangeOk getRow 2051521 141635 141699 := by
  decide +kernel

private theorem r_141699 : RangeOk getRow 2051521 141699 141765 := by
  decide +kernel

private theorem r_141765 : RangeOk getRow 2051521 141765 141830 := by
  decide +kernel

private theorem r_141830 : RangeOk getRow 2051521 141830 141894 := by
  decide +kernel

private theorem r_141894 : RangeOk getRow 2051521 141894 141958 := by
  decide +kernel

private theorem r_141958 : RangeOk getRow 2051521 141958 142022 := by
  decide +kernel

private theorem r_142022 : RangeOk getRow 2051521 142022 142087 := by
  decide +kernel

private theorem r_142087 : RangeOk getRow 2051521 142087 142151 := by
  decide +kernel

private theorem r_142151 : RangeOk getRow 2051521 142151 142216 := by
  decide +kernel

private theorem r_142216 : RangeOk getRow 2051521 142216 142281 := by
  decide +kernel

private theorem r_142281 : RangeOk getRow 2051521 142281 142345 := by
  decide +kernel

private theorem r_142345 : RangeOk getRow 2051521 142345 142409 := by
  decide +kernel

private theorem r_142409 : RangeOk getRow 2051521 142409 142473 := by
  decide +kernel

private theorem s_140741 : RangeOk getRow 2051521 140677 140741 := r_140677
private theorem s_140805 : RangeOk getRow 2051521 140677 140805 :=
  s_140741.append (by norm_num) r_140741
private theorem s_140869 : RangeOk getRow 2051521 140677 140869 :=
  s_140805.append (by norm_num) r_140805
private theorem s_140933 : RangeOk getRow 2051521 140677 140933 :=
  s_140869.append (by norm_num) r_140869
private theorem s_140993 : RangeOk getRow 2051521 140677 140993 :=
  s_140933.append (by norm_num) r_140933
private theorem s_141057 : RangeOk getRow 2051521 140677 141057 :=
  s_140993.append (by norm_num) r_140993
private theorem s_141121 : RangeOk getRow 2051521 140677 141121 :=
  s_141057.append (by norm_num) r_141057
private theorem s_141185 : RangeOk getRow 2051521 140677 141185 :=
  s_141121.append (by norm_num) r_141121
private theorem s_141249 : RangeOk getRow 2051521 140677 141249 :=
  s_141185.append (by norm_num) r_141185
private theorem s_141314 : RangeOk getRow 2051521 140677 141314 :=
  s_141249.append (by norm_num) r_141249
private theorem s_141378 : RangeOk getRow 2051521 140677 141378 :=
  s_141314.append (by norm_num) r_141314
private theorem s_141442 : RangeOk getRow 2051521 140677 141442 :=
  s_141378.append (by norm_num) r_141378
private theorem s_141506 : RangeOk getRow 2051521 140677 141506 :=
  s_141442.append (by norm_num) r_141442
private theorem s_141570 : RangeOk getRow 2051521 140677 141570 :=
  s_141506.append (by norm_num) r_141506
private theorem s_141635 : RangeOk getRow 2051521 140677 141635 :=
  s_141570.append (by norm_num) r_141570
private theorem s_141699 : RangeOk getRow 2051521 140677 141699 :=
  s_141635.append (by norm_num) r_141635
private theorem s_141765 : RangeOk getRow 2051521 140677 141765 :=
  s_141699.append (by norm_num) r_141699
private theorem s_141830 : RangeOk getRow 2051521 140677 141830 :=
  s_141765.append (by norm_num) r_141765
private theorem s_141894 : RangeOk getRow 2051521 140677 141894 :=
  s_141830.append (by norm_num) r_141830
private theorem s_141958 : RangeOk getRow 2051521 140677 141958 :=
  s_141894.append (by norm_num) r_141894
private theorem s_142022 : RangeOk getRow 2051521 140677 142022 :=
  s_141958.append (by norm_num) r_141958
private theorem s_142087 : RangeOk getRow 2051521 140677 142087 :=
  s_142022.append (by norm_num) r_142022
private theorem s_142151 : RangeOk getRow 2051521 140677 142151 :=
  s_142087.append (by norm_num) r_142087
private theorem s_142216 : RangeOk getRow 2051521 140677 142216 :=
  s_142151.append (by norm_num) r_142151
private theorem s_142281 : RangeOk getRow 2051521 140677 142281 :=
  s_142216.append (by norm_num) r_142216
private theorem s_142345 : RangeOk getRow 2051521 140677 142345 :=
  s_142281.append (by norm_num) r_142281
private theorem s_142409 : RangeOk getRow 2051521 140677 142409 :=
  s_142345.append (by norm_num) r_142345
private theorem s_142473 : RangeOk getRow 2051521 140677 142473 :=
  s_142409.append (by norm_num) r_142409

/-- Rows `[140677, 142473)` are valid. -/
theorem rangeOk_140677_142473 : RangeOk getRow 2051521 140677 142473 := s_142473

end Noperthedron.Solution
