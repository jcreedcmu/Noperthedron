import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[77806, 79534). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_77806 : RangeOk getRow 2051521 77806 77870 := by
  decide +kernel

private theorem r_77870 : RangeOk getRow 2051521 77870 77934 := by
  decide +kernel

private theorem r_77934 : RangeOk getRow 2051521 77934 77998 := by
  decide +kernel

private theorem r_77998 : RangeOk getRow 2051521 77998 78062 := by
  decide +kernel

private theorem r_78062 : RangeOk getRow 2051521 78062 78126 := by
  decide +kernel

private theorem r_78126 : RangeOk getRow 2051521 78126 78190 := by
  decide +kernel

private theorem r_78190 : RangeOk getRow 2051521 78190 78254 := by
  decide +kernel

private theorem r_78254 : RangeOk getRow 2051521 78254 78318 := by
  decide +kernel

private theorem r_78318 : RangeOk getRow 2051521 78318 78382 := by
  decide +kernel

private theorem r_78382 : RangeOk getRow 2051521 78382 78446 := by
  decide +kernel

private theorem r_78446 : RangeOk getRow 2051521 78446 78510 := by
  decide +kernel

private theorem r_78510 : RangeOk getRow 2051521 78510 78574 := by
  decide +kernel

private theorem r_78574 : RangeOk getRow 2051521 78574 78638 := by
  decide +kernel

private theorem r_78638 : RangeOk getRow 2051521 78638 78702 := by
  decide +kernel

private theorem r_78702 : RangeOk getRow 2051521 78702 78766 := by
  decide +kernel

private theorem r_78766 : RangeOk getRow 2051521 78766 78830 := by
  decide +kernel

private theorem r_78830 : RangeOk getRow 2051521 78830 78894 := by
  decide +kernel

private theorem r_78894 : RangeOk getRow 2051521 78894 78958 := by
  decide +kernel

private theorem r_78958 : RangeOk getRow 2051521 78958 79022 := by
  decide +kernel

private theorem r_79022 : RangeOk getRow 2051521 79022 79086 := by
  decide +kernel

private theorem r_79086 : RangeOk getRow 2051521 79086 79150 := by
  decide +kernel

private theorem r_79150 : RangeOk getRow 2051521 79150 79214 := by
  decide +kernel

private theorem r_79214 : RangeOk getRow 2051521 79214 79278 := by
  decide +kernel

private theorem r_79278 : RangeOk getRow 2051521 79278 79342 := by
  decide +kernel

private theorem r_79342 : RangeOk getRow 2051521 79342 79406 := by
  decide +kernel

private theorem r_79406 : RangeOk getRow 2051521 79406 79470 := by
  decide +kernel

private theorem r_79470 : RangeOk getRow 2051521 79470 79534 := by
  decide +kernel

private theorem s_77870 : RangeOk getRow 2051521 77806 77870 := r_77806
private theorem s_77934 : RangeOk getRow 2051521 77806 77934 :=
  s_77870.append (by norm_num) r_77870
private theorem s_77998 : RangeOk getRow 2051521 77806 77998 :=
  s_77934.append (by norm_num) r_77934
private theorem s_78062 : RangeOk getRow 2051521 77806 78062 :=
  s_77998.append (by norm_num) r_77998
private theorem s_78126 : RangeOk getRow 2051521 77806 78126 :=
  s_78062.append (by norm_num) r_78062
private theorem s_78190 : RangeOk getRow 2051521 77806 78190 :=
  s_78126.append (by norm_num) r_78126
private theorem s_78254 : RangeOk getRow 2051521 77806 78254 :=
  s_78190.append (by norm_num) r_78190
private theorem s_78318 : RangeOk getRow 2051521 77806 78318 :=
  s_78254.append (by norm_num) r_78254
private theorem s_78382 : RangeOk getRow 2051521 77806 78382 :=
  s_78318.append (by norm_num) r_78318
private theorem s_78446 : RangeOk getRow 2051521 77806 78446 :=
  s_78382.append (by norm_num) r_78382
private theorem s_78510 : RangeOk getRow 2051521 77806 78510 :=
  s_78446.append (by norm_num) r_78446
private theorem s_78574 : RangeOk getRow 2051521 77806 78574 :=
  s_78510.append (by norm_num) r_78510
private theorem s_78638 : RangeOk getRow 2051521 77806 78638 :=
  s_78574.append (by norm_num) r_78574
private theorem s_78702 : RangeOk getRow 2051521 77806 78702 :=
  s_78638.append (by norm_num) r_78638
private theorem s_78766 : RangeOk getRow 2051521 77806 78766 :=
  s_78702.append (by norm_num) r_78702
private theorem s_78830 : RangeOk getRow 2051521 77806 78830 :=
  s_78766.append (by norm_num) r_78766
private theorem s_78894 : RangeOk getRow 2051521 77806 78894 :=
  s_78830.append (by norm_num) r_78830
private theorem s_78958 : RangeOk getRow 2051521 77806 78958 :=
  s_78894.append (by norm_num) r_78894
private theorem s_79022 : RangeOk getRow 2051521 77806 79022 :=
  s_78958.append (by norm_num) r_78958
private theorem s_79086 : RangeOk getRow 2051521 77806 79086 :=
  s_79022.append (by norm_num) r_79022
private theorem s_79150 : RangeOk getRow 2051521 77806 79150 :=
  s_79086.append (by norm_num) r_79086
private theorem s_79214 : RangeOk getRow 2051521 77806 79214 :=
  s_79150.append (by norm_num) r_79150
private theorem s_79278 : RangeOk getRow 2051521 77806 79278 :=
  s_79214.append (by norm_num) r_79214
private theorem s_79342 : RangeOk getRow 2051521 77806 79342 :=
  s_79278.append (by norm_num) r_79278
private theorem s_79406 : RangeOk getRow 2051521 77806 79406 :=
  s_79342.append (by norm_num) r_79342
private theorem s_79470 : RangeOk getRow 2051521 77806 79470 :=
  s_79406.append (by norm_num) r_79406
private theorem s_79534 : RangeOk getRow 2051521 77806 79534 :=
  s_79470.append (by norm_num) r_79470

/-- Rows `[77806, 79534)` are valid. -/
theorem rangeOk_77806_79534 : RangeOk getRow 2051521 77806 79534 := s_79534

end Noperthedron.Solution
