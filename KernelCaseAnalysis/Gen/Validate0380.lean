import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[915752, 918052). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_915752 : RangeOk getRow 2051521 915752 915819 := by
  decide +kernel

private theorem r_915819 : RangeOk getRow 2051521 915819 915889 := by
  decide +kernel

private theorem r_915889 : RangeOk getRow 2051521 915889 915956 := by
  decide +kernel

private theorem r_915956 : RangeOk getRow 2051521 915956 916022 := by
  decide +kernel

private theorem r_916022 : RangeOk getRow 2051521 916022 916089 := by
  decide +kernel

private theorem r_916089 : RangeOk getRow 2051521 916089 916157 := by
  decide +kernel

private theorem r_916157 : RangeOk getRow 2051521 916157 916226 := by
  decide +kernel

private theorem r_916226 : RangeOk getRow 2051521 916226 916296 := by
  decide +kernel

private theorem r_916296 : RangeOk getRow 2051521 916296 916364 := by
  decide +kernel

private theorem r_916364 : RangeOk getRow 2051521 916364 916431 := by
  decide +kernel

private theorem r_916431 : RangeOk getRow 2051521 916431 916498 := by
  decide +kernel

private theorem r_916498 : RangeOk getRow 2051521 916498 916566 := by
  decide +kernel

private theorem r_916566 : RangeOk getRow 2051521 916566 916634 := by
  decide +kernel

private theorem r_916634 : RangeOk getRow 2051521 916634 916703 := by
  decide +kernel

private theorem r_916703 : RangeOk getRow 2051521 916703 916771 := by
  decide +kernel

private theorem r_916771 : RangeOk getRow 2051521 916771 916839 := by
  decide +kernel

private theorem r_916839 : RangeOk getRow 2051521 916839 916905 := by
  decide +kernel

private theorem r_916905 : RangeOk getRow 2051521 916905 916974 := by
  decide +kernel

private theorem r_916974 : RangeOk getRow 2051521 916974 917040 := by
  decide +kernel

private theorem r_917040 : RangeOk getRow 2051521 917040 917105 := by
  decide +kernel

private theorem r_917105 : RangeOk getRow 2051521 917105 917173 := by
  decide +kernel

private theorem r_917173 : RangeOk getRow 2051521 917173 917241 := by
  decide +kernel

private theorem r_917241 : RangeOk getRow 2051521 917241 917307 := by
  decide +kernel

private theorem r_917307 : RangeOk getRow 2051521 917307 917374 := by
  decide +kernel

private theorem r_917374 : RangeOk getRow 2051521 917374 917442 := by
  decide +kernel

private theorem r_917442 : RangeOk getRow 2051521 917442 917512 := by
  decide +kernel

private theorem r_917512 : RangeOk getRow 2051521 917512 917579 := by
  decide +kernel

private theorem r_917579 : RangeOk getRow 2051521 917579 917646 := by
  decide +kernel

private theorem r_917646 : RangeOk getRow 2051521 917646 917714 := by
  decide +kernel

private theorem r_917714 : RangeOk getRow 2051521 917714 917782 := by
  decide +kernel

private theorem r_917782 : RangeOk getRow 2051521 917782 917850 := by
  decide +kernel

private theorem r_917850 : RangeOk getRow 2051521 917850 917916 := by
  decide +kernel

private theorem r_917916 : RangeOk getRow 2051521 917916 917984 := by
  decide +kernel

private theorem r_917984 : RangeOk getRow 2051521 917984 918052 := by
  decide +kernel

private theorem s_915819 : RangeOk getRow 2051521 915752 915819 := r_915752
private theorem s_915889 : RangeOk getRow 2051521 915752 915889 :=
  s_915819.append (by norm_num) r_915819
private theorem s_915956 : RangeOk getRow 2051521 915752 915956 :=
  s_915889.append (by norm_num) r_915889
private theorem s_916022 : RangeOk getRow 2051521 915752 916022 :=
  s_915956.append (by norm_num) r_915956
private theorem s_916089 : RangeOk getRow 2051521 915752 916089 :=
  s_916022.append (by norm_num) r_916022
private theorem s_916157 : RangeOk getRow 2051521 915752 916157 :=
  s_916089.append (by norm_num) r_916089
private theorem s_916226 : RangeOk getRow 2051521 915752 916226 :=
  s_916157.append (by norm_num) r_916157
private theorem s_916296 : RangeOk getRow 2051521 915752 916296 :=
  s_916226.append (by norm_num) r_916226
private theorem s_916364 : RangeOk getRow 2051521 915752 916364 :=
  s_916296.append (by norm_num) r_916296
private theorem s_916431 : RangeOk getRow 2051521 915752 916431 :=
  s_916364.append (by norm_num) r_916364
private theorem s_916498 : RangeOk getRow 2051521 915752 916498 :=
  s_916431.append (by norm_num) r_916431
private theorem s_916566 : RangeOk getRow 2051521 915752 916566 :=
  s_916498.append (by norm_num) r_916498
private theorem s_916634 : RangeOk getRow 2051521 915752 916634 :=
  s_916566.append (by norm_num) r_916566
private theorem s_916703 : RangeOk getRow 2051521 915752 916703 :=
  s_916634.append (by norm_num) r_916634
private theorem s_916771 : RangeOk getRow 2051521 915752 916771 :=
  s_916703.append (by norm_num) r_916703
private theorem s_916839 : RangeOk getRow 2051521 915752 916839 :=
  s_916771.append (by norm_num) r_916771
private theorem s_916905 : RangeOk getRow 2051521 915752 916905 :=
  s_916839.append (by norm_num) r_916839
private theorem s_916974 : RangeOk getRow 2051521 915752 916974 :=
  s_916905.append (by norm_num) r_916905
private theorem s_917040 : RangeOk getRow 2051521 915752 917040 :=
  s_916974.append (by norm_num) r_916974
private theorem s_917105 : RangeOk getRow 2051521 915752 917105 :=
  s_917040.append (by norm_num) r_917040
private theorem s_917173 : RangeOk getRow 2051521 915752 917173 :=
  s_917105.append (by norm_num) r_917105
private theorem s_917241 : RangeOk getRow 2051521 915752 917241 :=
  s_917173.append (by norm_num) r_917173
private theorem s_917307 : RangeOk getRow 2051521 915752 917307 :=
  s_917241.append (by norm_num) r_917241
private theorem s_917374 : RangeOk getRow 2051521 915752 917374 :=
  s_917307.append (by norm_num) r_917307
private theorem s_917442 : RangeOk getRow 2051521 915752 917442 :=
  s_917374.append (by norm_num) r_917374
private theorem s_917512 : RangeOk getRow 2051521 915752 917512 :=
  s_917442.append (by norm_num) r_917442
private theorem s_917579 : RangeOk getRow 2051521 915752 917579 :=
  s_917512.append (by norm_num) r_917512
private theorem s_917646 : RangeOk getRow 2051521 915752 917646 :=
  s_917579.append (by norm_num) r_917579
private theorem s_917714 : RangeOk getRow 2051521 915752 917714 :=
  s_917646.append (by norm_num) r_917646
private theorem s_917782 : RangeOk getRow 2051521 915752 917782 :=
  s_917714.append (by norm_num) r_917714
private theorem s_917850 : RangeOk getRow 2051521 915752 917850 :=
  s_917782.append (by norm_num) r_917782
private theorem s_917916 : RangeOk getRow 2051521 915752 917916 :=
  s_917850.append (by norm_num) r_917850
private theorem s_917984 : RangeOk getRow 2051521 915752 917984 :=
  s_917916.append (by norm_num) r_917916
private theorem s_918052 : RangeOk getRow 2051521 915752 918052 :=
  s_917984.append (by norm_num) r_917984

/-- Rows `[915752, 918052)` are valid. -/
theorem rangeOk_915752_918052 : RangeOk getRow 2051521 915752 918052 := s_918052

end Noperthedron.Solution
