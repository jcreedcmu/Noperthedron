import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[856702, 859247). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_856702 : RangeOk getRow 2051521 856702 856768 := by
  decide +kernel

private theorem r_856768 : RangeOk getRow 2051521 856768 856834 := by
  decide +kernel

private theorem r_856834 : RangeOk getRow 2051521 856834 856902 := by
  decide +kernel

private theorem r_856902 : RangeOk getRow 2051521 856902 856972 := by
  decide +kernel

private theorem r_856972 : RangeOk getRow 2051521 856972 857040 := by
  decide +kernel

private theorem r_857040 : RangeOk getRow 2051521 857040 857107 := by
  decide +kernel

private theorem r_857107 : RangeOk getRow 2051521 857107 857174 := by
  decide +kernel

private theorem r_857174 : RangeOk getRow 2051521 857174 857243 := by
  decide +kernel

private theorem r_857243 : RangeOk getRow 2051521 857243 857313 := by
  decide +kernel

private theorem r_857313 : RangeOk getRow 2051521 857313 857381 := by
  decide +kernel

private theorem r_857381 : RangeOk getRow 2051521 857381 857450 := by
  decide +kernel

private theorem r_857450 : RangeOk getRow 2051521 857450 857519 := by
  decide +kernel

private theorem r_857519 : RangeOk getRow 2051521 857519 857590 := by
  decide +kernel

private theorem r_857590 : RangeOk getRow 2051521 857590 857662 := by
  decide +kernel

private theorem r_857662 : RangeOk getRow 2051521 857662 857735 := by
  decide +kernel

private theorem r_857735 : RangeOk getRow 2051521 857735 857808 := by
  decide +kernel

private theorem r_857808 : RangeOk getRow 2051521 857808 857878 := by
  decide +kernel

private theorem r_857878 : RangeOk getRow 2051521 857878 857947 := by
  decide +kernel

private theorem r_857947 : RangeOk getRow 2051521 857947 858018 := by
  decide +kernel

private theorem r_858018 : RangeOk getRow 2051521 858018 858089 := by
  decide +kernel

private theorem r_858089 : RangeOk getRow 2051521 858089 858159 := by
  decide +kernel

private theorem r_858159 : RangeOk getRow 2051521 858159 858228 := by
  decide +kernel

private theorem r_858228 : RangeOk getRow 2051521 858228 858299 := by
  decide +kernel

private theorem r_858299 : RangeOk getRow 2051521 858299 858370 := by
  decide +kernel

private theorem r_858370 : RangeOk getRow 2051521 858370 858438 := by
  decide +kernel

private theorem r_858438 : RangeOk getRow 2051521 858438 858504 := by
  decide +kernel

private theorem r_858504 : RangeOk getRow 2051521 858504 858572 := by
  decide +kernel

private theorem r_858572 : RangeOk getRow 2051521 858572 858640 := by
  decide +kernel

private theorem r_858640 : RangeOk getRow 2051521 858640 858707 := by
  decide +kernel

private theorem r_858707 : RangeOk getRow 2051521 858707 858775 := by
  decide +kernel

private theorem r_858775 : RangeOk getRow 2051521 858775 858841 := by
  decide +kernel

private theorem r_858841 : RangeOk getRow 2051521 858841 858908 := by
  decide +kernel

private theorem r_858908 : RangeOk getRow 2051521 858908 858974 := by
  decide +kernel

private theorem r_858974 : RangeOk getRow 2051521 858974 859040 := by
  decide +kernel

private theorem r_859040 : RangeOk getRow 2051521 859040 859104 := by
  decide +kernel

private theorem r_859104 : RangeOk getRow 2051521 859104 859176 := by
  decide +kernel

private theorem r_859176 : RangeOk getRow 2051521 859176 859247 := by
  decide +kernel

private theorem s_856768 : RangeOk getRow 2051521 856702 856768 := r_856702
private theorem s_856834 : RangeOk getRow 2051521 856702 856834 :=
  s_856768.append (by norm_num) r_856768
private theorem s_856902 : RangeOk getRow 2051521 856702 856902 :=
  s_856834.append (by norm_num) r_856834
private theorem s_856972 : RangeOk getRow 2051521 856702 856972 :=
  s_856902.append (by norm_num) r_856902
private theorem s_857040 : RangeOk getRow 2051521 856702 857040 :=
  s_856972.append (by norm_num) r_856972
private theorem s_857107 : RangeOk getRow 2051521 856702 857107 :=
  s_857040.append (by norm_num) r_857040
private theorem s_857174 : RangeOk getRow 2051521 856702 857174 :=
  s_857107.append (by norm_num) r_857107
private theorem s_857243 : RangeOk getRow 2051521 856702 857243 :=
  s_857174.append (by norm_num) r_857174
private theorem s_857313 : RangeOk getRow 2051521 856702 857313 :=
  s_857243.append (by norm_num) r_857243
private theorem s_857381 : RangeOk getRow 2051521 856702 857381 :=
  s_857313.append (by norm_num) r_857313
private theorem s_857450 : RangeOk getRow 2051521 856702 857450 :=
  s_857381.append (by norm_num) r_857381
private theorem s_857519 : RangeOk getRow 2051521 856702 857519 :=
  s_857450.append (by norm_num) r_857450
private theorem s_857590 : RangeOk getRow 2051521 856702 857590 :=
  s_857519.append (by norm_num) r_857519
private theorem s_857662 : RangeOk getRow 2051521 856702 857662 :=
  s_857590.append (by norm_num) r_857590
private theorem s_857735 : RangeOk getRow 2051521 856702 857735 :=
  s_857662.append (by norm_num) r_857662
private theorem s_857808 : RangeOk getRow 2051521 856702 857808 :=
  s_857735.append (by norm_num) r_857735
private theorem s_857878 : RangeOk getRow 2051521 856702 857878 :=
  s_857808.append (by norm_num) r_857808
private theorem s_857947 : RangeOk getRow 2051521 856702 857947 :=
  s_857878.append (by norm_num) r_857878
private theorem s_858018 : RangeOk getRow 2051521 856702 858018 :=
  s_857947.append (by norm_num) r_857947
private theorem s_858089 : RangeOk getRow 2051521 856702 858089 :=
  s_858018.append (by norm_num) r_858018
private theorem s_858159 : RangeOk getRow 2051521 856702 858159 :=
  s_858089.append (by norm_num) r_858089
private theorem s_858228 : RangeOk getRow 2051521 856702 858228 :=
  s_858159.append (by norm_num) r_858159
private theorem s_858299 : RangeOk getRow 2051521 856702 858299 :=
  s_858228.append (by norm_num) r_858228
private theorem s_858370 : RangeOk getRow 2051521 856702 858370 :=
  s_858299.append (by norm_num) r_858299
private theorem s_858438 : RangeOk getRow 2051521 856702 858438 :=
  s_858370.append (by norm_num) r_858370
private theorem s_858504 : RangeOk getRow 2051521 856702 858504 :=
  s_858438.append (by norm_num) r_858438
private theorem s_858572 : RangeOk getRow 2051521 856702 858572 :=
  s_858504.append (by norm_num) r_858504
private theorem s_858640 : RangeOk getRow 2051521 856702 858640 :=
  s_858572.append (by norm_num) r_858572
private theorem s_858707 : RangeOk getRow 2051521 856702 858707 :=
  s_858640.append (by norm_num) r_858640
private theorem s_858775 : RangeOk getRow 2051521 856702 858775 :=
  s_858707.append (by norm_num) r_858707
private theorem s_858841 : RangeOk getRow 2051521 856702 858841 :=
  s_858775.append (by norm_num) r_858775
private theorem s_858908 : RangeOk getRow 2051521 856702 858908 :=
  s_858841.append (by norm_num) r_858841
private theorem s_858974 : RangeOk getRow 2051521 856702 858974 :=
  s_858908.append (by norm_num) r_858908
private theorem s_859040 : RangeOk getRow 2051521 856702 859040 :=
  s_858974.append (by norm_num) r_858974
private theorem s_859104 : RangeOk getRow 2051521 856702 859104 :=
  s_859040.append (by norm_num) r_859040
private theorem s_859176 : RangeOk getRow 2051521 856702 859176 :=
  s_859104.append (by norm_num) r_859104
private theorem s_859247 : RangeOk getRow 2051521 856702 859247 :=
  s_859176.append (by norm_num) r_859176

/-- Rows `[856702, 859247)` are valid. -/
theorem rangeOk_856702_859247 : RangeOk getRow 2051521 856702 859247 := s_859247

end Noperthedron.Solution
