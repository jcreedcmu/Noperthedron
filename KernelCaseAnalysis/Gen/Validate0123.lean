import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[282603, 285139). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_282603 : RangeOk getRow 2051521 282603 282673 := by
  decide +kernel

private theorem r_282673 : RangeOk getRow 2051521 282673 282740 := by
  decide +kernel

private theorem r_282740 : RangeOk getRow 2051521 282740 282808 := by
  decide +kernel

private theorem r_282808 : RangeOk getRow 2051521 282808 282876 := by
  decide +kernel

private theorem r_282876 : RangeOk getRow 2051521 282876 282944 := by
  decide +kernel

private theorem r_282944 : RangeOk getRow 2051521 282944 283012 := by
  decide +kernel

private theorem r_283012 : RangeOk getRow 2051521 283012 283077 := by
  decide +kernel

private theorem r_283077 : RangeOk getRow 2051521 283077 283146 := by
  decide +kernel

private theorem r_283146 : RangeOk getRow 2051521 283146 283215 := by
  decide +kernel

private theorem r_283215 : RangeOk getRow 2051521 283215 283285 := by
  decide +kernel

private theorem r_283285 : RangeOk getRow 2051521 283285 283356 := by
  decide +kernel

private theorem r_283356 : RangeOk getRow 2051521 283356 283425 := by
  decide +kernel

private theorem r_283425 : RangeOk getRow 2051521 283425 283495 := by
  decide +kernel

private theorem r_283495 : RangeOk getRow 2051521 283495 283564 := by
  decide +kernel

private theorem r_283564 : RangeOk getRow 2051521 283564 283632 := by
  decide +kernel

private theorem r_283632 : RangeOk getRow 2051521 283632 283700 := by
  decide +kernel

private theorem r_283700 : RangeOk getRow 2051521 283700 283766 := by
  decide +kernel

private theorem r_283766 : RangeOk getRow 2051521 283766 283835 := by
  decide +kernel

private theorem r_283835 : RangeOk getRow 2051521 283835 283905 := by
  decide +kernel

private theorem r_283905 : RangeOk getRow 2051521 283905 283973 := by
  decide +kernel

private theorem r_283973 : RangeOk getRow 2051521 283973 284043 := by
  decide +kernel

private theorem r_284043 : RangeOk getRow 2051521 284043 284112 := by
  decide +kernel

private theorem r_284112 : RangeOk getRow 2051521 284112 284179 := by
  decide +kernel

private theorem r_284179 : RangeOk getRow 2051521 284179 284248 := by
  decide +kernel

private theorem r_284248 : RangeOk getRow 2051521 284248 284318 := by
  decide +kernel

private theorem r_284318 : RangeOk getRow 2051521 284318 284387 := by
  decide +kernel

private theorem r_284387 : RangeOk getRow 2051521 284387 284455 := by
  decide +kernel

private theorem r_284455 : RangeOk getRow 2051521 284455 284524 := by
  decide +kernel

private theorem r_284524 : RangeOk getRow 2051521 284524 284594 := by
  decide +kernel

private theorem r_284594 : RangeOk getRow 2051521 284594 284664 := by
  decide +kernel

private theorem r_284664 : RangeOk getRow 2051521 284664 284731 := by
  decide +kernel

private theorem r_284731 : RangeOk getRow 2051521 284731 284800 := by
  decide +kernel

private theorem r_284800 : RangeOk getRow 2051521 284800 284862 := by
  decide +kernel

private theorem r_284862 : RangeOk getRow 2051521 284862 284932 := by
  decide +kernel

private theorem r_284932 : RangeOk getRow 2051521 284932 285002 := by
  decide +kernel

private theorem r_285002 : RangeOk getRow 2051521 285002 285070 := by
  decide +kernel

private theorem r_285070 : RangeOk getRow 2051521 285070 285139 := by
  decide +kernel

private theorem s_282673 : RangeOk getRow 2051521 282603 282673 := r_282603
private theorem s_282740 : RangeOk getRow 2051521 282603 282740 :=
  s_282673.append (by norm_num) r_282673
private theorem s_282808 : RangeOk getRow 2051521 282603 282808 :=
  s_282740.append (by norm_num) r_282740
private theorem s_282876 : RangeOk getRow 2051521 282603 282876 :=
  s_282808.append (by norm_num) r_282808
private theorem s_282944 : RangeOk getRow 2051521 282603 282944 :=
  s_282876.append (by norm_num) r_282876
private theorem s_283012 : RangeOk getRow 2051521 282603 283012 :=
  s_282944.append (by norm_num) r_282944
private theorem s_283077 : RangeOk getRow 2051521 282603 283077 :=
  s_283012.append (by norm_num) r_283012
private theorem s_283146 : RangeOk getRow 2051521 282603 283146 :=
  s_283077.append (by norm_num) r_283077
private theorem s_283215 : RangeOk getRow 2051521 282603 283215 :=
  s_283146.append (by norm_num) r_283146
private theorem s_283285 : RangeOk getRow 2051521 282603 283285 :=
  s_283215.append (by norm_num) r_283215
private theorem s_283356 : RangeOk getRow 2051521 282603 283356 :=
  s_283285.append (by norm_num) r_283285
private theorem s_283425 : RangeOk getRow 2051521 282603 283425 :=
  s_283356.append (by norm_num) r_283356
private theorem s_283495 : RangeOk getRow 2051521 282603 283495 :=
  s_283425.append (by norm_num) r_283425
private theorem s_283564 : RangeOk getRow 2051521 282603 283564 :=
  s_283495.append (by norm_num) r_283495
private theorem s_283632 : RangeOk getRow 2051521 282603 283632 :=
  s_283564.append (by norm_num) r_283564
private theorem s_283700 : RangeOk getRow 2051521 282603 283700 :=
  s_283632.append (by norm_num) r_283632
private theorem s_283766 : RangeOk getRow 2051521 282603 283766 :=
  s_283700.append (by norm_num) r_283700
private theorem s_283835 : RangeOk getRow 2051521 282603 283835 :=
  s_283766.append (by norm_num) r_283766
private theorem s_283905 : RangeOk getRow 2051521 282603 283905 :=
  s_283835.append (by norm_num) r_283835
private theorem s_283973 : RangeOk getRow 2051521 282603 283973 :=
  s_283905.append (by norm_num) r_283905
private theorem s_284043 : RangeOk getRow 2051521 282603 284043 :=
  s_283973.append (by norm_num) r_283973
private theorem s_284112 : RangeOk getRow 2051521 282603 284112 :=
  s_284043.append (by norm_num) r_284043
private theorem s_284179 : RangeOk getRow 2051521 282603 284179 :=
  s_284112.append (by norm_num) r_284112
private theorem s_284248 : RangeOk getRow 2051521 282603 284248 :=
  s_284179.append (by norm_num) r_284179
private theorem s_284318 : RangeOk getRow 2051521 282603 284318 :=
  s_284248.append (by norm_num) r_284248
private theorem s_284387 : RangeOk getRow 2051521 282603 284387 :=
  s_284318.append (by norm_num) r_284318
private theorem s_284455 : RangeOk getRow 2051521 282603 284455 :=
  s_284387.append (by norm_num) r_284387
private theorem s_284524 : RangeOk getRow 2051521 282603 284524 :=
  s_284455.append (by norm_num) r_284455
private theorem s_284594 : RangeOk getRow 2051521 282603 284594 :=
  s_284524.append (by norm_num) r_284524
private theorem s_284664 : RangeOk getRow 2051521 282603 284664 :=
  s_284594.append (by norm_num) r_284594
private theorem s_284731 : RangeOk getRow 2051521 282603 284731 :=
  s_284664.append (by norm_num) r_284664
private theorem s_284800 : RangeOk getRow 2051521 282603 284800 :=
  s_284731.append (by norm_num) r_284731
private theorem s_284862 : RangeOk getRow 2051521 282603 284862 :=
  s_284800.append (by norm_num) r_284800
private theorem s_284932 : RangeOk getRow 2051521 282603 284932 :=
  s_284862.append (by norm_num) r_284862
private theorem s_285002 : RangeOk getRow 2051521 282603 285002 :=
  s_284932.append (by norm_num) r_284932
private theorem s_285070 : RangeOk getRow 2051521 282603 285070 :=
  s_285002.append (by norm_num) r_285002
private theorem s_285139 : RangeOk getRow 2051521 282603 285139 :=
  s_285070.append (by norm_num) r_285070

/-- Rows `[282603, 285139)` are valid. -/
theorem rangeOk_282603_285139 : RangeOk getRow 2051521 282603 285139 := s_285139

end Noperthedron.Solution
