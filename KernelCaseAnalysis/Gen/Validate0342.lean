import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[823077, 825442). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_823077 : RangeOk getRow 2051521 823077 823143 := by
  decide +kernel

private theorem r_823143 : RangeOk getRow 2051521 823143 823213 := by
  decide +kernel

private theorem r_823213 : RangeOk getRow 2051521 823213 823281 := by
  decide +kernel

private theorem r_823281 : RangeOk getRow 2051521 823281 823349 := by
  decide +kernel

private theorem r_823349 : RangeOk getRow 2051521 823349 823416 := by
  decide +kernel

private theorem r_823416 : RangeOk getRow 2051521 823416 823483 := by
  decide +kernel

private theorem r_823483 : RangeOk getRow 2051521 823483 823550 := by
  decide +kernel

private theorem r_823550 : RangeOk getRow 2051521 823550 823617 := by
  decide +kernel

private theorem r_823617 : RangeOk getRow 2051521 823617 823684 := by
  decide +kernel

private theorem r_823684 : RangeOk getRow 2051521 823684 823751 := by
  decide +kernel

private theorem r_823751 : RangeOk getRow 2051521 823751 823817 := by
  decide +kernel

private theorem r_823817 : RangeOk getRow 2051521 823817 823885 := by
  decide +kernel

private theorem r_823885 : RangeOk getRow 2051521 823885 823954 := by
  decide +kernel

private theorem r_823954 : RangeOk getRow 2051521 823954 824021 := by
  decide +kernel

private theorem r_824021 : RangeOk getRow 2051521 824021 824090 := by
  decide +kernel

private theorem r_824090 : RangeOk getRow 2051521 824090 824157 := by
  decide +kernel

private theorem r_824157 : RangeOk getRow 2051521 824157 824223 := by
  decide +kernel

private theorem r_824223 : RangeOk getRow 2051521 824223 824290 := by
  decide +kernel

private theorem r_824290 : RangeOk getRow 2051521 824290 824360 := by
  decide +kernel

private theorem r_824360 : RangeOk getRow 2051521 824360 824429 := by
  decide +kernel

private theorem r_824429 : RangeOk getRow 2051521 824429 824498 := by
  decide +kernel

private theorem r_824498 : RangeOk getRow 2051521 824498 824567 := by
  decide +kernel

private theorem r_824567 : RangeOk getRow 2051521 824567 824635 := by
  decide +kernel

private theorem r_824635 : RangeOk getRow 2051521 824635 824702 := by
  decide +kernel

private theorem r_824702 : RangeOk getRow 2051521 824702 824767 := by
  decide +kernel

private theorem r_824767 : RangeOk getRow 2051521 824767 824832 := by
  decide +kernel

private theorem r_824832 : RangeOk getRow 2051521 824832 824898 := by
  decide +kernel

private theorem r_824898 : RangeOk getRow 2051521 824898 824966 := by
  decide +kernel

private theorem r_824966 : RangeOk getRow 2051521 824966 825032 := by
  decide +kernel

private theorem r_825032 : RangeOk getRow 2051521 825032 825101 := by
  decide +kernel

private theorem r_825101 : RangeOk getRow 2051521 825101 825172 := by
  decide +kernel

private theorem r_825172 : RangeOk getRow 2051521 825172 825241 := by
  decide +kernel

private theorem r_825241 : RangeOk getRow 2051521 825241 825309 := by
  decide +kernel

private theorem r_825309 : RangeOk getRow 2051521 825309 825375 := by
  decide +kernel

private theorem r_825375 : RangeOk getRow 2051521 825375 825442 := by
  decide +kernel

private theorem s_823143 : RangeOk getRow 2051521 823077 823143 := r_823077
private theorem s_823213 : RangeOk getRow 2051521 823077 823213 :=
  s_823143.append (by norm_num) r_823143
private theorem s_823281 : RangeOk getRow 2051521 823077 823281 :=
  s_823213.append (by norm_num) r_823213
private theorem s_823349 : RangeOk getRow 2051521 823077 823349 :=
  s_823281.append (by norm_num) r_823281
private theorem s_823416 : RangeOk getRow 2051521 823077 823416 :=
  s_823349.append (by norm_num) r_823349
private theorem s_823483 : RangeOk getRow 2051521 823077 823483 :=
  s_823416.append (by norm_num) r_823416
private theorem s_823550 : RangeOk getRow 2051521 823077 823550 :=
  s_823483.append (by norm_num) r_823483
private theorem s_823617 : RangeOk getRow 2051521 823077 823617 :=
  s_823550.append (by norm_num) r_823550
private theorem s_823684 : RangeOk getRow 2051521 823077 823684 :=
  s_823617.append (by norm_num) r_823617
private theorem s_823751 : RangeOk getRow 2051521 823077 823751 :=
  s_823684.append (by norm_num) r_823684
private theorem s_823817 : RangeOk getRow 2051521 823077 823817 :=
  s_823751.append (by norm_num) r_823751
private theorem s_823885 : RangeOk getRow 2051521 823077 823885 :=
  s_823817.append (by norm_num) r_823817
private theorem s_823954 : RangeOk getRow 2051521 823077 823954 :=
  s_823885.append (by norm_num) r_823885
private theorem s_824021 : RangeOk getRow 2051521 823077 824021 :=
  s_823954.append (by norm_num) r_823954
private theorem s_824090 : RangeOk getRow 2051521 823077 824090 :=
  s_824021.append (by norm_num) r_824021
private theorem s_824157 : RangeOk getRow 2051521 823077 824157 :=
  s_824090.append (by norm_num) r_824090
private theorem s_824223 : RangeOk getRow 2051521 823077 824223 :=
  s_824157.append (by norm_num) r_824157
private theorem s_824290 : RangeOk getRow 2051521 823077 824290 :=
  s_824223.append (by norm_num) r_824223
private theorem s_824360 : RangeOk getRow 2051521 823077 824360 :=
  s_824290.append (by norm_num) r_824290
private theorem s_824429 : RangeOk getRow 2051521 823077 824429 :=
  s_824360.append (by norm_num) r_824360
private theorem s_824498 : RangeOk getRow 2051521 823077 824498 :=
  s_824429.append (by norm_num) r_824429
private theorem s_824567 : RangeOk getRow 2051521 823077 824567 :=
  s_824498.append (by norm_num) r_824498
private theorem s_824635 : RangeOk getRow 2051521 823077 824635 :=
  s_824567.append (by norm_num) r_824567
private theorem s_824702 : RangeOk getRow 2051521 823077 824702 :=
  s_824635.append (by norm_num) r_824635
private theorem s_824767 : RangeOk getRow 2051521 823077 824767 :=
  s_824702.append (by norm_num) r_824702
private theorem s_824832 : RangeOk getRow 2051521 823077 824832 :=
  s_824767.append (by norm_num) r_824767
private theorem s_824898 : RangeOk getRow 2051521 823077 824898 :=
  s_824832.append (by norm_num) r_824832
private theorem s_824966 : RangeOk getRow 2051521 823077 824966 :=
  s_824898.append (by norm_num) r_824898
private theorem s_825032 : RangeOk getRow 2051521 823077 825032 :=
  s_824966.append (by norm_num) r_824966
private theorem s_825101 : RangeOk getRow 2051521 823077 825101 :=
  s_825032.append (by norm_num) r_825032
private theorem s_825172 : RangeOk getRow 2051521 823077 825172 :=
  s_825101.append (by norm_num) r_825101
private theorem s_825241 : RangeOk getRow 2051521 823077 825241 :=
  s_825172.append (by norm_num) r_825172
private theorem s_825309 : RangeOk getRow 2051521 823077 825309 :=
  s_825241.append (by norm_num) r_825241
private theorem s_825375 : RangeOk getRow 2051521 823077 825375 :=
  s_825309.append (by norm_num) r_825309
private theorem s_825442 : RangeOk getRow 2051521 823077 825442 :=
  s_825375.append (by norm_num) r_825375

/-- Rows `[823077, 825442)` are valid. -/
theorem rangeOk_823077_825442 : RangeOk getRow 2051521 823077 825442 := s_825442

end Noperthedron.Solution
