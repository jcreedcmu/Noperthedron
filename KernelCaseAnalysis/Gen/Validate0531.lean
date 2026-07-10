import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1289024, 1292046). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1289024 : RangeOk getRow 2051521 1289024 1289088 := by
  decide +kernel

private theorem r_1289088 : RangeOk getRow 2051521 1289088 1289160 := by
  decide +kernel

private theorem r_1289160 : RangeOk getRow 2051521 1289160 1289232 := by
  decide +kernel

private theorem r_1289232 : RangeOk getRow 2051521 1289232 1289304 := by
  decide +kernel

private theorem r_1289304 : RangeOk getRow 2051521 1289304 1289375 := by
  decide +kernel

private theorem r_1289375 : RangeOk getRow 2051521 1289375 1289444 := by
  decide +kernel

private theorem r_1289444 : RangeOk getRow 2051521 1289444 1289513 := by
  decide +kernel

private theorem r_1289513 : RangeOk getRow 2051521 1289513 1289582 := by
  decide +kernel

private theorem r_1289582 : RangeOk getRow 2051521 1289582 1289651 := by
  decide +kernel

private theorem r_1289651 : RangeOk getRow 2051521 1289651 1289720 := by
  decide +kernel

private theorem r_1289720 : RangeOk getRow 2051521 1289720 1289789 := by
  decide +kernel

private theorem r_1289789 : RangeOk getRow 2051521 1289789 1289859 := by
  decide +kernel

private theorem r_1289859 : RangeOk getRow 2051521 1289859 1289931 := by
  decide +kernel

private theorem r_1289931 : RangeOk getRow 2051521 1289931 1290000 := by
  decide +kernel

private theorem r_1290000 : RangeOk getRow 2051521 1290000 1290069 := by
  decide +kernel

private theorem r_1290069 : RangeOk getRow 2051521 1290069 1290140 := by
  decide +kernel

private theorem r_1290140 : RangeOk getRow 2051521 1290140 1290211 := by
  decide +kernel

private theorem r_1290211 : RangeOk getRow 2051521 1290211 1290281 := by
  decide +kernel

private theorem r_1290281 : RangeOk getRow 2051521 1290281 1290352 := by
  decide +kernel

private theorem r_1290352 : RangeOk getRow 2051521 1290352 1290423 := by
  decide +kernel

private theorem r_1290423 : RangeOk getRow 2051521 1290423 1290494 := by
  decide +kernel

private theorem r_1290494 : RangeOk getRow 2051521 1290494 1290566 := by
  decide +kernel

private theorem r_1290566 : RangeOk getRow 2051521 1290566 1290637 := by
  decide +kernel

private theorem r_1290637 : RangeOk getRow 2051521 1290637 1290706 := by
  decide +kernel

private theorem r_1290706 : RangeOk getRow 2051521 1290706 1290775 := by
  decide +kernel

private theorem r_1290775 : RangeOk getRow 2051521 1290775 1290847 := by
  decide +kernel

private theorem r_1290847 : RangeOk getRow 2051521 1290847 1290918 := by
  decide +kernel

private theorem r_1290918 : RangeOk getRow 2051521 1290918 1290987 := by
  decide +kernel

private theorem r_1290987 : RangeOk getRow 2051521 1290987 1291056 := by
  decide +kernel

private theorem r_1291056 : RangeOk getRow 2051521 1291056 1291125 := by
  decide +kernel

private theorem r_1291125 : RangeOk getRow 2051521 1291125 1291194 := by
  decide +kernel

private theorem r_1291194 : RangeOk getRow 2051521 1291194 1291263 := by
  decide +kernel

private theorem r_1291263 : RangeOk getRow 2051521 1291263 1291332 := by
  decide +kernel

private theorem r_1291332 : RangeOk getRow 2051521 1291332 1291401 := by
  decide +kernel

private theorem r_1291401 : RangeOk getRow 2051521 1291401 1291471 := by
  decide +kernel

private theorem r_1291471 : RangeOk getRow 2051521 1291471 1291543 := by
  decide +kernel

private theorem r_1291543 : RangeOk getRow 2051521 1291543 1291615 := by
  decide +kernel

private theorem r_1291615 : RangeOk getRow 2051521 1291615 1291687 := by
  decide +kernel

private theorem r_1291687 : RangeOk getRow 2051521 1291687 1291759 := by
  decide +kernel

private theorem r_1291759 : RangeOk getRow 2051521 1291759 1291832 := by
  decide +kernel

private theorem r_1291832 : RangeOk getRow 2051521 1291832 1291904 := by
  decide +kernel

private theorem r_1291904 : RangeOk getRow 2051521 1291904 1291975 := by
  decide +kernel

private theorem r_1291975 : RangeOk getRow 2051521 1291975 1292046 := by
  decide +kernel

private theorem s_1289088 : RangeOk getRow 2051521 1289024 1289088 := r_1289024
private theorem s_1289160 : RangeOk getRow 2051521 1289024 1289160 :=
  s_1289088.append (by norm_num) r_1289088
private theorem s_1289232 : RangeOk getRow 2051521 1289024 1289232 :=
  s_1289160.append (by norm_num) r_1289160
private theorem s_1289304 : RangeOk getRow 2051521 1289024 1289304 :=
  s_1289232.append (by norm_num) r_1289232
private theorem s_1289375 : RangeOk getRow 2051521 1289024 1289375 :=
  s_1289304.append (by norm_num) r_1289304
private theorem s_1289444 : RangeOk getRow 2051521 1289024 1289444 :=
  s_1289375.append (by norm_num) r_1289375
private theorem s_1289513 : RangeOk getRow 2051521 1289024 1289513 :=
  s_1289444.append (by norm_num) r_1289444
private theorem s_1289582 : RangeOk getRow 2051521 1289024 1289582 :=
  s_1289513.append (by norm_num) r_1289513
private theorem s_1289651 : RangeOk getRow 2051521 1289024 1289651 :=
  s_1289582.append (by norm_num) r_1289582
private theorem s_1289720 : RangeOk getRow 2051521 1289024 1289720 :=
  s_1289651.append (by norm_num) r_1289651
private theorem s_1289789 : RangeOk getRow 2051521 1289024 1289789 :=
  s_1289720.append (by norm_num) r_1289720
private theorem s_1289859 : RangeOk getRow 2051521 1289024 1289859 :=
  s_1289789.append (by norm_num) r_1289789
private theorem s_1289931 : RangeOk getRow 2051521 1289024 1289931 :=
  s_1289859.append (by norm_num) r_1289859
private theorem s_1290000 : RangeOk getRow 2051521 1289024 1290000 :=
  s_1289931.append (by norm_num) r_1289931
private theorem s_1290069 : RangeOk getRow 2051521 1289024 1290069 :=
  s_1290000.append (by norm_num) r_1290000
private theorem s_1290140 : RangeOk getRow 2051521 1289024 1290140 :=
  s_1290069.append (by norm_num) r_1290069
private theorem s_1290211 : RangeOk getRow 2051521 1289024 1290211 :=
  s_1290140.append (by norm_num) r_1290140
private theorem s_1290281 : RangeOk getRow 2051521 1289024 1290281 :=
  s_1290211.append (by norm_num) r_1290211
private theorem s_1290352 : RangeOk getRow 2051521 1289024 1290352 :=
  s_1290281.append (by norm_num) r_1290281
private theorem s_1290423 : RangeOk getRow 2051521 1289024 1290423 :=
  s_1290352.append (by norm_num) r_1290352
private theorem s_1290494 : RangeOk getRow 2051521 1289024 1290494 :=
  s_1290423.append (by norm_num) r_1290423
private theorem s_1290566 : RangeOk getRow 2051521 1289024 1290566 :=
  s_1290494.append (by norm_num) r_1290494
private theorem s_1290637 : RangeOk getRow 2051521 1289024 1290637 :=
  s_1290566.append (by norm_num) r_1290566
private theorem s_1290706 : RangeOk getRow 2051521 1289024 1290706 :=
  s_1290637.append (by norm_num) r_1290637
private theorem s_1290775 : RangeOk getRow 2051521 1289024 1290775 :=
  s_1290706.append (by norm_num) r_1290706
private theorem s_1290847 : RangeOk getRow 2051521 1289024 1290847 :=
  s_1290775.append (by norm_num) r_1290775
private theorem s_1290918 : RangeOk getRow 2051521 1289024 1290918 :=
  s_1290847.append (by norm_num) r_1290847
private theorem s_1290987 : RangeOk getRow 2051521 1289024 1290987 :=
  s_1290918.append (by norm_num) r_1290918
private theorem s_1291056 : RangeOk getRow 2051521 1289024 1291056 :=
  s_1290987.append (by norm_num) r_1290987
private theorem s_1291125 : RangeOk getRow 2051521 1289024 1291125 :=
  s_1291056.append (by norm_num) r_1291056
private theorem s_1291194 : RangeOk getRow 2051521 1289024 1291194 :=
  s_1291125.append (by norm_num) r_1291125
private theorem s_1291263 : RangeOk getRow 2051521 1289024 1291263 :=
  s_1291194.append (by norm_num) r_1291194
private theorem s_1291332 : RangeOk getRow 2051521 1289024 1291332 :=
  s_1291263.append (by norm_num) r_1291263
private theorem s_1291401 : RangeOk getRow 2051521 1289024 1291401 :=
  s_1291332.append (by norm_num) r_1291332
private theorem s_1291471 : RangeOk getRow 2051521 1289024 1291471 :=
  s_1291401.append (by norm_num) r_1291401
private theorem s_1291543 : RangeOk getRow 2051521 1289024 1291543 :=
  s_1291471.append (by norm_num) r_1291471
private theorem s_1291615 : RangeOk getRow 2051521 1289024 1291615 :=
  s_1291543.append (by norm_num) r_1291543
private theorem s_1291687 : RangeOk getRow 2051521 1289024 1291687 :=
  s_1291615.append (by norm_num) r_1291615
private theorem s_1291759 : RangeOk getRow 2051521 1289024 1291759 :=
  s_1291687.append (by norm_num) r_1291687
private theorem s_1291832 : RangeOk getRow 2051521 1289024 1291832 :=
  s_1291759.append (by norm_num) r_1291759
private theorem s_1291904 : RangeOk getRow 2051521 1289024 1291904 :=
  s_1291832.append (by norm_num) r_1291832
private theorem s_1291975 : RangeOk getRow 2051521 1289024 1291975 :=
  s_1291904.append (by norm_num) r_1291904
private theorem s_1292046 : RangeOk getRow 2051521 1289024 1292046 :=
  s_1291975.append (by norm_num) r_1291975

/-- Rows `[1289024, 1292046)` are valid. -/
theorem rangeOk_1289024_1292046 : RangeOk getRow 2051521 1289024 1292046 := s_1292046

end Noperthedron.Solution
