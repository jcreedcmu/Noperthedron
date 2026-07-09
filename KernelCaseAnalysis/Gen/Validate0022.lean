import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[42970, 44700). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_42970 : RangeOk getRow 2051521 42970 43034 := by
  decide +kernel

private theorem r_43034 : RangeOk getRow 2051521 43034 43098 := by
  decide +kernel

private theorem r_43098 : RangeOk getRow 2051521 43098 43162 := by
  decide +kernel

private theorem r_43162 : RangeOk getRow 2051521 43162 43226 := by
  decide +kernel

private theorem r_43226 : RangeOk getRow 2051521 43226 43290 := by
  decide +kernel

private theorem r_43290 : RangeOk getRow 2051521 43290 43354 := by
  decide +kernel

private theorem r_43354 : RangeOk getRow 2051521 43354 43418 := by
  decide +kernel

private theorem r_43418 : RangeOk getRow 2051521 43418 43482 := by
  decide +kernel

private theorem r_43482 : RangeOk getRow 2051521 43482 43546 := by
  decide +kernel

private theorem r_43546 : RangeOk getRow 2051521 43546 43610 := by
  decide +kernel

private theorem r_43610 : RangeOk getRow 2051521 43610 43674 := by
  decide +kernel

private theorem r_43674 : RangeOk getRow 2051521 43674 43738 := by
  decide +kernel

private theorem r_43738 : RangeOk getRow 2051521 43738 43802 := by
  decide +kernel

private theorem r_43802 : RangeOk getRow 2051521 43802 43866 := by
  decide +kernel

private theorem r_43866 : RangeOk getRow 2051521 43866 43930 := by
  decide +kernel

private theorem r_43930 : RangeOk getRow 2051521 43930 43994 := by
  decide +kernel

private theorem r_43994 : RangeOk getRow 2051521 43994 44058 := by
  decide +kernel

private theorem r_44058 : RangeOk getRow 2051521 44058 44123 := by
  decide +kernel

private theorem r_44123 : RangeOk getRow 2051521 44123 44187 := by
  decide +kernel

private theorem r_44187 : RangeOk getRow 2051521 44187 44251 := by
  decide +kernel

private theorem r_44251 : RangeOk getRow 2051521 44251 44315 := by
  decide +kernel

private theorem r_44315 : RangeOk getRow 2051521 44315 44379 := by
  decide +kernel

private theorem r_44379 : RangeOk getRow 2051521 44379 44443 := by
  decide +kernel

private theorem r_44443 : RangeOk getRow 2051521 44443 44507 := by
  decide +kernel

private theorem r_44507 : RangeOk getRow 2051521 44507 44572 := by
  decide +kernel

private theorem r_44572 : RangeOk getRow 2051521 44572 44636 := by
  decide +kernel

private theorem r_44636 : RangeOk getRow 2051521 44636 44700 := by
  decide +kernel

private theorem s_43034 : RangeOk getRow 2051521 42970 43034 := r_42970
private theorem s_43098 : RangeOk getRow 2051521 42970 43098 :=
  s_43034.append (by norm_num) r_43034
private theorem s_43162 : RangeOk getRow 2051521 42970 43162 :=
  s_43098.append (by norm_num) r_43098
private theorem s_43226 : RangeOk getRow 2051521 42970 43226 :=
  s_43162.append (by norm_num) r_43162
private theorem s_43290 : RangeOk getRow 2051521 42970 43290 :=
  s_43226.append (by norm_num) r_43226
private theorem s_43354 : RangeOk getRow 2051521 42970 43354 :=
  s_43290.append (by norm_num) r_43290
private theorem s_43418 : RangeOk getRow 2051521 42970 43418 :=
  s_43354.append (by norm_num) r_43354
private theorem s_43482 : RangeOk getRow 2051521 42970 43482 :=
  s_43418.append (by norm_num) r_43418
private theorem s_43546 : RangeOk getRow 2051521 42970 43546 :=
  s_43482.append (by norm_num) r_43482
private theorem s_43610 : RangeOk getRow 2051521 42970 43610 :=
  s_43546.append (by norm_num) r_43546
private theorem s_43674 : RangeOk getRow 2051521 42970 43674 :=
  s_43610.append (by norm_num) r_43610
private theorem s_43738 : RangeOk getRow 2051521 42970 43738 :=
  s_43674.append (by norm_num) r_43674
private theorem s_43802 : RangeOk getRow 2051521 42970 43802 :=
  s_43738.append (by norm_num) r_43738
private theorem s_43866 : RangeOk getRow 2051521 42970 43866 :=
  s_43802.append (by norm_num) r_43802
private theorem s_43930 : RangeOk getRow 2051521 42970 43930 :=
  s_43866.append (by norm_num) r_43866
private theorem s_43994 : RangeOk getRow 2051521 42970 43994 :=
  s_43930.append (by norm_num) r_43930
private theorem s_44058 : RangeOk getRow 2051521 42970 44058 :=
  s_43994.append (by norm_num) r_43994
private theorem s_44123 : RangeOk getRow 2051521 42970 44123 :=
  s_44058.append (by norm_num) r_44058
private theorem s_44187 : RangeOk getRow 2051521 42970 44187 :=
  s_44123.append (by norm_num) r_44123
private theorem s_44251 : RangeOk getRow 2051521 42970 44251 :=
  s_44187.append (by norm_num) r_44187
private theorem s_44315 : RangeOk getRow 2051521 42970 44315 :=
  s_44251.append (by norm_num) r_44251
private theorem s_44379 : RangeOk getRow 2051521 42970 44379 :=
  s_44315.append (by norm_num) r_44315
private theorem s_44443 : RangeOk getRow 2051521 42970 44443 :=
  s_44379.append (by norm_num) r_44379
private theorem s_44507 : RangeOk getRow 2051521 42970 44507 :=
  s_44443.append (by norm_num) r_44443
private theorem s_44572 : RangeOk getRow 2051521 42970 44572 :=
  s_44507.append (by norm_num) r_44507
private theorem s_44636 : RangeOk getRow 2051521 42970 44636 :=
  s_44572.append (by norm_num) r_44572
private theorem s_44700 : RangeOk getRow 2051521 42970 44700 :=
  s_44636.append (by norm_num) r_44636

/-- Rows `[42970, 44700)` are valid. -/
theorem rangeOk_42970_44700 : RangeOk getRow 2051521 42970 44700 := s_44700

end Noperthedron.Solution
