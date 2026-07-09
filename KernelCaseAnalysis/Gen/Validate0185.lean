import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[444824, 447160). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_444824 : RangeOk getRow 2051521 444824 444890 := by
  decide +kernel

private theorem r_444890 : RangeOk getRow 2051521 444890 444958 := by
  decide +kernel

private theorem r_444958 : RangeOk getRow 2051521 444958 445027 := by
  decide +kernel

private theorem r_445027 : RangeOk getRow 2051521 445027 445095 := by
  decide +kernel

private theorem r_445095 : RangeOk getRow 2051521 445095 445163 := by
  decide +kernel

private theorem r_445163 : RangeOk getRow 2051521 445163 445231 := by
  decide +kernel

private theorem r_445231 : RangeOk getRow 2051521 445231 445301 := by
  decide +kernel

private theorem r_445301 : RangeOk getRow 2051521 445301 445371 := by
  decide +kernel

private theorem r_445371 : RangeOk getRow 2051521 445371 445441 := by
  decide +kernel

private theorem r_445441 : RangeOk getRow 2051521 445441 445510 := by
  decide +kernel

private theorem r_445510 : RangeOk getRow 2051521 445510 445577 := by
  decide +kernel

private theorem r_445577 : RangeOk getRow 2051521 445577 445645 := by
  decide +kernel

private theorem r_445645 : RangeOk getRow 2051521 445645 445713 := by
  decide +kernel

private theorem r_445713 : RangeOk getRow 2051521 445713 445781 := by
  decide +kernel

private theorem r_445781 : RangeOk getRow 2051521 445781 445849 := by
  decide +kernel

private theorem r_445849 : RangeOk getRow 2051521 445849 445919 := by
  decide +kernel

private theorem r_445919 : RangeOk getRow 2051521 445919 445988 := by
  decide +kernel

private theorem r_445988 : RangeOk getRow 2051521 445988 446057 := by
  decide +kernel

private theorem r_446057 : RangeOk getRow 2051521 446057 446124 := by
  decide +kernel

private theorem r_446124 : RangeOk getRow 2051521 446124 446188 := by
  decide +kernel

private theorem r_446188 : RangeOk getRow 2051521 446188 446252 := by
  decide +kernel

private theorem r_446252 : RangeOk getRow 2051521 446252 446316 := by
  decide +kernel

private theorem r_446316 : RangeOk getRow 2051521 446316 446369 := by
  decide +kernel

private theorem r_446369 : RangeOk getRow 2051521 446369 446437 := by
  decide +kernel

private theorem r_446437 : RangeOk getRow 2051521 446437 446505 := by
  decide +kernel

private theorem r_446505 : RangeOk getRow 2051521 446505 446573 := by
  decide +kernel

private theorem r_446573 : RangeOk getRow 2051521 446573 446641 := by
  decide +kernel

private theorem r_446641 : RangeOk getRow 2051521 446641 446709 := by
  decide +kernel

private theorem r_446709 : RangeOk getRow 2051521 446709 446779 := by
  decide +kernel

private theorem r_446779 : RangeOk getRow 2051521 446779 446849 := by
  decide +kernel

private theorem r_446849 : RangeOk getRow 2051521 446849 446919 := by
  decide +kernel

private theorem r_446919 : RangeOk getRow 2051521 446919 446986 := by
  decide +kernel

private theorem r_446986 : RangeOk getRow 2051521 446986 447041 := by
  decide +kernel

private theorem r_447041 : RangeOk getRow 2051521 447041 447105 := by
  decide +kernel

private theorem r_447105 : RangeOk getRow 2051521 447105 447160 := by
  decide +kernel

private theorem s_444890 : RangeOk getRow 2051521 444824 444890 := r_444824
private theorem s_444958 : RangeOk getRow 2051521 444824 444958 :=
  s_444890.append (by norm_num) r_444890
private theorem s_445027 : RangeOk getRow 2051521 444824 445027 :=
  s_444958.append (by norm_num) r_444958
private theorem s_445095 : RangeOk getRow 2051521 444824 445095 :=
  s_445027.append (by norm_num) r_445027
private theorem s_445163 : RangeOk getRow 2051521 444824 445163 :=
  s_445095.append (by norm_num) r_445095
private theorem s_445231 : RangeOk getRow 2051521 444824 445231 :=
  s_445163.append (by norm_num) r_445163
private theorem s_445301 : RangeOk getRow 2051521 444824 445301 :=
  s_445231.append (by norm_num) r_445231
private theorem s_445371 : RangeOk getRow 2051521 444824 445371 :=
  s_445301.append (by norm_num) r_445301
private theorem s_445441 : RangeOk getRow 2051521 444824 445441 :=
  s_445371.append (by norm_num) r_445371
private theorem s_445510 : RangeOk getRow 2051521 444824 445510 :=
  s_445441.append (by norm_num) r_445441
private theorem s_445577 : RangeOk getRow 2051521 444824 445577 :=
  s_445510.append (by norm_num) r_445510
private theorem s_445645 : RangeOk getRow 2051521 444824 445645 :=
  s_445577.append (by norm_num) r_445577
private theorem s_445713 : RangeOk getRow 2051521 444824 445713 :=
  s_445645.append (by norm_num) r_445645
private theorem s_445781 : RangeOk getRow 2051521 444824 445781 :=
  s_445713.append (by norm_num) r_445713
private theorem s_445849 : RangeOk getRow 2051521 444824 445849 :=
  s_445781.append (by norm_num) r_445781
private theorem s_445919 : RangeOk getRow 2051521 444824 445919 :=
  s_445849.append (by norm_num) r_445849
private theorem s_445988 : RangeOk getRow 2051521 444824 445988 :=
  s_445919.append (by norm_num) r_445919
private theorem s_446057 : RangeOk getRow 2051521 444824 446057 :=
  s_445988.append (by norm_num) r_445988
private theorem s_446124 : RangeOk getRow 2051521 444824 446124 :=
  s_446057.append (by norm_num) r_446057
private theorem s_446188 : RangeOk getRow 2051521 444824 446188 :=
  s_446124.append (by norm_num) r_446124
private theorem s_446252 : RangeOk getRow 2051521 444824 446252 :=
  s_446188.append (by norm_num) r_446188
private theorem s_446316 : RangeOk getRow 2051521 444824 446316 :=
  s_446252.append (by norm_num) r_446252
private theorem s_446369 : RangeOk getRow 2051521 444824 446369 :=
  s_446316.append (by norm_num) r_446316
private theorem s_446437 : RangeOk getRow 2051521 444824 446437 :=
  s_446369.append (by norm_num) r_446369
private theorem s_446505 : RangeOk getRow 2051521 444824 446505 :=
  s_446437.append (by norm_num) r_446437
private theorem s_446573 : RangeOk getRow 2051521 444824 446573 :=
  s_446505.append (by norm_num) r_446505
private theorem s_446641 : RangeOk getRow 2051521 444824 446641 :=
  s_446573.append (by norm_num) r_446573
private theorem s_446709 : RangeOk getRow 2051521 444824 446709 :=
  s_446641.append (by norm_num) r_446641
private theorem s_446779 : RangeOk getRow 2051521 444824 446779 :=
  s_446709.append (by norm_num) r_446709
private theorem s_446849 : RangeOk getRow 2051521 444824 446849 :=
  s_446779.append (by norm_num) r_446779
private theorem s_446919 : RangeOk getRow 2051521 444824 446919 :=
  s_446849.append (by norm_num) r_446849
private theorem s_446986 : RangeOk getRow 2051521 444824 446986 :=
  s_446919.append (by norm_num) r_446919
private theorem s_447041 : RangeOk getRow 2051521 444824 447041 :=
  s_446986.append (by norm_num) r_446986
private theorem s_447105 : RangeOk getRow 2051521 444824 447105 :=
  s_447041.append (by norm_num) r_447041
private theorem s_447160 : RangeOk getRow 2051521 444824 447160 :=
  s_447105.append (by norm_num) r_447105

/-- Rows `[444824, 447160)` are valid. -/
theorem rangeOk_444824_447160 : RangeOk getRow 2051521 444824 447160 := s_447160

end Noperthedron.Solution
