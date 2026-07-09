import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[88320, 90054). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_88320 : RangeOk getRow 2051521 88320 88384 := by
  decide +kernel

private theorem r_88384 : RangeOk getRow 2051521 88384 88449 := by
  decide +kernel

private theorem r_88449 : RangeOk getRow 2051521 88449 88514 := by
  decide +kernel

private theorem r_88514 : RangeOk getRow 2051521 88514 88579 := by
  decide +kernel

private theorem r_88579 : RangeOk getRow 2051521 88579 88645 := by
  decide +kernel

private theorem r_88645 : RangeOk getRow 2051521 88645 88710 := by
  decide +kernel

private theorem r_88710 : RangeOk getRow 2051521 88710 88774 := by
  decide +kernel

private theorem r_88774 : RangeOk getRow 2051521 88774 88838 := by
  decide +kernel

private theorem r_88838 : RangeOk getRow 2051521 88838 88902 := by
  decide +kernel

private theorem r_88902 : RangeOk getRow 2051521 88902 88966 := by
  decide +kernel

private theorem r_88966 : RangeOk getRow 2051521 88966 89030 := by
  decide +kernel

private theorem r_89030 : RangeOk getRow 2051521 89030 89094 := by
  decide +kernel

private theorem r_89094 : RangeOk getRow 2051521 89094 89158 := by
  decide +kernel

private theorem r_89158 : RangeOk getRow 2051521 89158 89222 := by
  decide +kernel

private theorem r_89222 : RangeOk getRow 2051521 89222 89286 := by
  decide +kernel

private theorem r_89286 : RangeOk getRow 2051521 89286 89350 := by
  decide +kernel

private theorem r_89350 : RangeOk getRow 2051521 89350 89414 := by
  decide +kernel

private theorem r_89414 : RangeOk getRow 2051521 89414 89478 := by
  decide +kernel

private theorem r_89478 : RangeOk getRow 2051521 89478 89542 := by
  decide +kernel

private theorem r_89542 : RangeOk getRow 2051521 89542 89606 := by
  decide +kernel

private theorem r_89606 : RangeOk getRow 2051521 89606 89670 := by
  decide +kernel

private theorem r_89670 : RangeOk getRow 2051521 89670 89734 := by
  decide +kernel

private theorem r_89734 : RangeOk getRow 2051521 89734 89798 := by
  decide +kernel

private theorem r_89798 : RangeOk getRow 2051521 89798 89862 := by
  decide +kernel

private theorem r_89862 : RangeOk getRow 2051521 89862 89926 := by
  decide +kernel

private theorem r_89926 : RangeOk getRow 2051521 89926 89990 := by
  decide +kernel

private theorem r_89990 : RangeOk getRow 2051521 89990 90054 := by
  decide +kernel

private theorem s_88384 : RangeOk getRow 2051521 88320 88384 := r_88320
private theorem s_88449 : RangeOk getRow 2051521 88320 88449 :=
  s_88384.append (by norm_num) r_88384
private theorem s_88514 : RangeOk getRow 2051521 88320 88514 :=
  s_88449.append (by norm_num) r_88449
private theorem s_88579 : RangeOk getRow 2051521 88320 88579 :=
  s_88514.append (by norm_num) r_88514
private theorem s_88645 : RangeOk getRow 2051521 88320 88645 :=
  s_88579.append (by norm_num) r_88579
private theorem s_88710 : RangeOk getRow 2051521 88320 88710 :=
  s_88645.append (by norm_num) r_88645
private theorem s_88774 : RangeOk getRow 2051521 88320 88774 :=
  s_88710.append (by norm_num) r_88710
private theorem s_88838 : RangeOk getRow 2051521 88320 88838 :=
  s_88774.append (by norm_num) r_88774
private theorem s_88902 : RangeOk getRow 2051521 88320 88902 :=
  s_88838.append (by norm_num) r_88838
private theorem s_88966 : RangeOk getRow 2051521 88320 88966 :=
  s_88902.append (by norm_num) r_88902
private theorem s_89030 : RangeOk getRow 2051521 88320 89030 :=
  s_88966.append (by norm_num) r_88966
private theorem s_89094 : RangeOk getRow 2051521 88320 89094 :=
  s_89030.append (by norm_num) r_89030
private theorem s_89158 : RangeOk getRow 2051521 88320 89158 :=
  s_89094.append (by norm_num) r_89094
private theorem s_89222 : RangeOk getRow 2051521 88320 89222 :=
  s_89158.append (by norm_num) r_89158
private theorem s_89286 : RangeOk getRow 2051521 88320 89286 :=
  s_89222.append (by norm_num) r_89222
private theorem s_89350 : RangeOk getRow 2051521 88320 89350 :=
  s_89286.append (by norm_num) r_89286
private theorem s_89414 : RangeOk getRow 2051521 88320 89414 :=
  s_89350.append (by norm_num) r_89350
private theorem s_89478 : RangeOk getRow 2051521 88320 89478 :=
  s_89414.append (by norm_num) r_89414
private theorem s_89542 : RangeOk getRow 2051521 88320 89542 :=
  s_89478.append (by norm_num) r_89478
private theorem s_89606 : RangeOk getRow 2051521 88320 89606 :=
  s_89542.append (by norm_num) r_89542
private theorem s_89670 : RangeOk getRow 2051521 88320 89670 :=
  s_89606.append (by norm_num) r_89606
private theorem s_89734 : RangeOk getRow 2051521 88320 89734 :=
  s_89670.append (by norm_num) r_89670
private theorem s_89798 : RangeOk getRow 2051521 88320 89798 :=
  s_89734.append (by norm_num) r_89734
private theorem s_89862 : RangeOk getRow 2051521 88320 89862 :=
  s_89798.append (by norm_num) r_89798
private theorem s_89926 : RangeOk getRow 2051521 88320 89926 :=
  s_89862.append (by norm_num) r_89862
private theorem s_89990 : RangeOk getRow 2051521 88320 89990 :=
  s_89926.append (by norm_num) r_89926
private theorem s_90054 : RangeOk getRow 2051521 88320 90054 :=
  s_89990.append (by norm_num) r_89990

/-- Rows `[88320, 90054)` are valid. -/
theorem rangeOk_88320_90054 : RangeOk getRow 2051521 88320 90054 := s_90054

end Noperthedron.Solution
