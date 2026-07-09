import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[98681, 100411). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_98681 : RangeOk getRow 2051521 98681 98745 := by
  decide +kernel

private theorem r_98745 : RangeOk getRow 2051521 98745 98809 := by
  decide +kernel

private theorem r_98809 : RangeOk getRow 2051521 98809 98873 := by
  decide +kernel

private theorem r_98873 : RangeOk getRow 2051521 98873 98937 := by
  decide +kernel

private theorem r_98937 : RangeOk getRow 2051521 98937 99001 := by
  decide +kernel

private theorem r_99001 : RangeOk getRow 2051521 99001 99065 := by
  decide +kernel

private theorem r_99065 : RangeOk getRow 2051521 99065 99129 := by
  decide +kernel

private theorem r_99129 : RangeOk getRow 2051521 99129 99193 := by
  decide +kernel

private theorem r_99193 : RangeOk getRow 2051521 99193 99257 := by
  decide +kernel

private theorem r_99257 : RangeOk getRow 2051521 99257 99321 := by
  decide +kernel

private theorem r_99321 : RangeOk getRow 2051521 99321 99385 := by
  decide +kernel

private theorem r_99385 : RangeOk getRow 2051521 99385 99445 := by
  decide +kernel

private theorem r_99445 : RangeOk getRow 2051521 99445 99509 := by
  decide +kernel

private theorem r_99509 : RangeOk getRow 2051521 99509 99573 := by
  decide +kernel

private theorem r_99573 : RangeOk getRow 2051521 99573 99637 := by
  decide +kernel

private theorem r_99637 : RangeOk getRow 2051521 99637 99701 := by
  decide +kernel

private theorem r_99701 : RangeOk getRow 2051521 99701 99765 := by
  decide +kernel

private theorem r_99765 : RangeOk getRow 2051521 99765 99829 := by
  decide +kernel

private theorem r_99829 : RangeOk getRow 2051521 99829 99895 := by
  decide +kernel

private theorem r_99895 : RangeOk getRow 2051521 99895 99960 := by
  decide +kernel

private theorem r_99960 : RangeOk getRow 2051521 99960 100024 := by
  decide +kernel

private theorem r_100024 : RangeOk getRow 2051521 100024 100088 := by
  decide +kernel

private theorem r_100088 : RangeOk getRow 2051521 100088 100152 := by
  decide +kernel

private theorem r_100152 : RangeOk getRow 2051521 100152 100217 := by
  decide +kernel

private theorem r_100217 : RangeOk getRow 2051521 100217 100281 := by
  decide +kernel

private theorem r_100281 : RangeOk getRow 2051521 100281 100346 := by
  decide +kernel

private theorem r_100346 : RangeOk getRow 2051521 100346 100411 := by
  decide +kernel

private theorem s_98745 : RangeOk getRow 2051521 98681 98745 := r_98681
private theorem s_98809 : RangeOk getRow 2051521 98681 98809 :=
  s_98745.append (by norm_num) r_98745
private theorem s_98873 : RangeOk getRow 2051521 98681 98873 :=
  s_98809.append (by norm_num) r_98809
private theorem s_98937 : RangeOk getRow 2051521 98681 98937 :=
  s_98873.append (by norm_num) r_98873
private theorem s_99001 : RangeOk getRow 2051521 98681 99001 :=
  s_98937.append (by norm_num) r_98937
private theorem s_99065 : RangeOk getRow 2051521 98681 99065 :=
  s_99001.append (by norm_num) r_99001
private theorem s_99129 : RangeOk getRow 2051521 98681 99129 :=
  s_99065.append (by norm_num) r_99065
private theorem s_99193 : RangeOk getRow 2051521 98681 99193 :=
  s_99129.append (by norm_num) r_99129
private theorem s_99257 : RangeOk getRow 2051521 98681 99257 :=
  s_99193.append (by norm_num) r_99193
private theorem s_99321 : RangeOk getRow 2051521 98681 99321 :=
  s_99257.append (by norm_num) r_99257
private theorem s_99385 : RangeOk getRow 2051521 98681 99385 :=
  s_99321.append (by norm_num) r_99321
private theorem s_99445 : RangeOk getRow 2051521 98681 99445 :=
  s_99385.append (by norm_num) r_99385
private theorem s_99509 : RangeOk getRow 2051521 98681 99509 :=
  s_99445.append (by norm_num) r_99445
private theorem s_99573 : RangeOk getRow 2051521 98681 99573 :=
  s_99509.append (by norm_num) r_99509
private theorem s_99637 : RangeOk getRow 2051521 98681 99637 :=
  s_99573.append (by norm_num) r_99573
private theorem s_99701 : RangeOk getRow 2051521 98681 99701 :=
  s_99637.append (by norm_num) r_99637
private theorem s_99765 : RangeOk getRow 2051521 98681 99765 :=
  s_99701.append (by norm_num) r_99701
private theorem s_99829 : RangeOk getRow 2051521 98681 99829 :=
  s_99765.append (by norm_num) r_99765
private theorem s_99895 : RangeOk getRow 2051521 98681 99895 :=
  s_99829.append (by norm_num) r_99829
private theorem s_99960 : RangeOk getRow 2051521 98681 99960 :=
  s_99895.append (by norm_num) r_99895
private theorem s_100024 : RangeOk getRow 2051521 98681 100024 :=
  s_99960.append (by norm_num) r_99960
private theorem s_100088 : RangeOk getRow 2051521 98681 100088 :=
  s_100024.append (by norm_num) r_100024
private theorem s_100152 : RangeOk getRow 2051521 98681 100152 :=
  s_100088.append (by norm_num) r_100088
private theorem s_100217 : RangeOk getRow 2051521 98681 100217 :=
  s_100152.append (by norm_num) r_100152
private theorem s_100281 : RangeOk getRow 2051521 98681 100281 :=
  s_100217.append (by norm_num) r_100217
private theorem s_100346 : RangeOk getRow 2051521 98681 100346 :=
  s_100281.append (by norm_num) r_100281
private theorem s_100411 : RangeOk getRow 2051521 98681 100411 :=
  s_100346.append (by norm_num) r_100346

/-- Rows `[98681, 100411)` are valid. -/
theorem rangeOk_98681_100411 : RangeOk getRow 2051521 98681 100411 := s_100411

end Noperthedron.Solution
