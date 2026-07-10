import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[559704, 562071). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_559704 : RangeOk getRow 2051521 559704 559771 := by
  decide +kernel

private theorem r_559771 : RangeOk getRow 2051521 559771 559839 := by
  decide +kernel

private theorem r_559839 : RangeOk getRow 2051521 559839 559905 := by
  decide +kernel

private theorem r_559905 : RangeOk getRow 2051521 559905 559972 := by
  decide +kernel

private theorem r_559972 : RangeOk getRow 2051521 559972 560039 := by
  decide +kernel

private theorem r_560039 : RangeOk getRow 2051521 560039 560105 := by
  decide +kernel

private theorem r_560105 : RangeOk getRow 2051521 560105 560170 := by
  decide +kernel

private theorem r_560170 : RangeOk getRow 2051521 560170 560238 := by
  decide +kernel

private theorem r_560238 : RangeOk getRow 2051521 560238 560305 := by
  decide +kernel

private theorem r_560305 : RangeOk getRow 2051521 560305 560373 := by
  decide +kernel

private theorem r_560373 : RangeOk getRow 2051521 560373 560438 := by
  decide +kernel

private theorem r_560438 : RangeOk getRow 2051521 560438 560503 := by
  decide +kernel

private theorem r_560503 : RangeOk getRow 2051521 560503 560569 := by
  decide +kernel

private theorem r_560569 : RangeOk getRow 2051521 560569 560638 := by
  decide +kernel

private theorem r_560638 : RangeOk getRow 2051521 560638 560708 := by
  decide +kernel

private theorem r_560708 : RangeOk getRow 2051521 560708 560777 := by
  decide +kernel

private theorem r_560777 : RangeOk getRow 2051521 560777 560845 := by
  decide +kernel

private theorem r_560845 : RangeOk getRow 2051521 560845 560914 := by
  decide +kernel

private theorem r_560914 : RangeOk getRow 2051521 560914 560982 := by
  decide +kernel

private theorem r_560982 : RangeOk getRow 2051521 560982 561050 := by
  decide +kernel

private theorem r_561050 : RangeOk getRow 2051521 561050 561116 := by
  decide +kernel

private theorem r_561116 : RangeOk getRow 2051521 561116 561181 := by
  decide +kernel

private theorem r_561181 : RangeOk getRow 2051521 561181 561249 := by
  decide +kernel

private theorem r_561249 : RangeOk getRow 2051521 561249 561318 := by
  decide +kernel

private theorem r_561318 : RangeOk getRow 2051521 561318 561388 := by
  decide +kernel

private theorem r_561388 : RangeOk getRow 2051521 561388 561458 := by
  decide +kernel

private theorem r_561458 : RangeOk getRow 2051521 561458 561527 := by
  decide +kernel

private theorem r_561527 : RangeOk getRow 2051521 561527 561596 := by
  decide +kernel

private theorem r_561596 : RangeOk getRow 2051521 561596 561665 := by
  decide +kernel

private theorem r_561665 : RangeOk getRow 2051521 561665 561732 := by
  decide +kernel

private theorem r_561732 : RangeOk getRow 2051521 561732 561801 := by
  decide +kernel

private theorem r_561801 : RangeOk getRow 2051521 561801 561868 := by
  decide +kernel

private theorem r_561868 : RangeOk getRow 2051521 561868 561934 := by
  decide +kernel

private theorem r_561934 : RangeOk getRow 2051521 561934 562003 := by
  decide +kernel

private theorem r_562003 : RangeOk getRow 2051521 562003 562071 := by
  decide +kernel

private theorem s_559771 : RangeOk getRow 2051521 559704 559771 := r_559704
private theorem s_559839 : RangeOk getRow 2051521 559704 559839 :=
  s_559771.append (by norm_num) r_559771
private theorem s_559905 : RangeOk getRow 2051521 559704 559905 :=
  s_559839.append (by norm_num) r_559839
private theorem s_559972 : RangeOk getRow 2051521 559704 559972 :=
  s_559905.append (by norm_num) r_559905
private theorem s_560039 : RangeOk getRow 2051521 559704 560039 :=
  s_559972.append (by norm_num) r_559972
private theorem s_560105 : RangeOk getRow 2051521 559704 560105 :=
  s_560039.append (by norm_num) r_560039
private theorem s_560170 : RangeOk getRow 2051521 559704 560170 :=
  s_560105.append (by norm_num) r_560105
private theorem s_560238 : RangeOk getRow 2051521 559704 560238 :=
  s_560170.append (by norm_num) r_560170
private theorem s_560305 : RangeOk getRow 2051521 559704 560305 :=
  s_560238.append (by norm_num) r_560238
private theorem s_560373 : RangeOk getRow 2051521 559704 560373 :=
  s_560305.append (by norm_num) r_560305
private theorem s_560438 : RangeOk getRow 2051521 559704 560438 :=
  s_560373.append (by norm_num) r_560373
private theorem s_560503 : RangeOk getRow 2051521 559704 560503 :=
  s_560438.append (by norm_num) r_560438
private theorem s_560569 : RangeOk getRow 2051521 559704 560569 :=
  s_560503.append (by norm_num) r_560503
private theorem s_560638 : RangeOk getRow 2051521 559704 560638 :=
  s_560569.append (by norm_num) r_560569
private theorem s_560708 : RangeOk getRow 2051521 559704 560708 :=
  s_560638.append (by norm_num) r_560638
private theorem s_560777 : RangeOk getRow 2051521 559704 560777 :=
  s_560708.append (by norm_num) r_560708
private theorem s_560845 : RangeOk getRow 2051521 559704 560845 :=
  s_560777.append (by norm_num) r_560777
private theorem s_560914 : RangeOk getRow 2051521 559704 560914 :=
  s_560845.append (by norm_num) r_560845
private theorem s_560982 : RangeOk getRow 2051521 559704 560982 :=
  s_560914.append (by norm_num) r_560914
private theorem s_561050 : RangeOk getRow 2051521 559704 561050 :=
  s_560982.append (by norm_num) r_560982
private theorem s_561116 : RangeOk getRow 2051521 559704 561116 :=
  s_561050.append (by norm_num) r_561050
private theorem s_561181 : RangeOk getRow 2051521 559704 561181 :=
  s_561116.append (by norm_num) r_561116
private theorem s_561249 : RangeOk getRow 2051521 559704 561249 :=
  s_561181.append (by norm_num) r_561181
private theorem s_561318 : RangeOk getRow 2051521 559704 561318 :=
  s_561249.append (by norm_num) r_561249
private theorem s_561388 : RangeOk getRow 2051521 559704 561388 :=
  s_561318.append (by norm_num) r_561318
private theorem s_561458 : RangeOk getRow 2051521 559704 561458 :=
  s_561388.append (by norm_num) r_561388
private theorem s_561527 : RangeOk getRow 2051521 559704 561527 :=
  s_561458.append (by norm_num) r_561458
private theorem s_561596 : RangeOk getRow 2051521 559704 561596 :=
  s_561527.append (by norm_num) r_561527
private theorem s_561665 : RangeOk getRow 2051521 559704 561665 :=
  s_561596.append (by norm_num) r_561596
private theorem s_561732 : RangeOk getRow 2051521 559704 561732 :=
  s_561665.append (by norm_num) r_561665
private theorem s_561801 : RangeOk getRow 2051521 559704 561801 :=
  s_561732.append (by norm_num) r_561732
private theorem s_561868 : RangeOk getRow 2051521 559704 561868 :=
  s_561801.append (by norm_num) r_561801
private theorem s_561934 : RangeOk getRow 2051521 559704 561934 :=
  s_561868.append (by norm_num) r_561868
private theorem s_562003 : RangeOk getRow 2051521 559704 562003 :=
  s_561934.append (by norm_num) r_561934
private theorem s_562071 : RangeOk getRow 2051521 559704 562071 :=
  s_562003.append (by norm_num) r_562003

/-- Rows `[559704, 562071)` are valid. -/
theorem rangeOk_559704_562071 : RangeOk getRow 2051521 559704 562071 := s_562071

end Noperthedron.Solution
