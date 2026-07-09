import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1396171, 1399598). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1396171 : RangeOk getRow 2051521 1396171 1396201 := by
  decide +kernel

private theorem r_1396201 : RangeOk getRow 2051521 1396201 1396273 := by
  decide +kernel

private theorem r_1396273 : RangeOk getRow 2051521 1396273 1396343 := by
  decide +kernel

private theorem r_1396343 : RangeOk getRow 2051521 1396343 1396379 := by
  decide +kernel

private theorem r_1396379 : RangeOk getRow 2051521 1396379 1396415 := by
  decide +kernel

private theorem r_1396415 : RangeOk getRow 2051521 1396415 1396459 := by
  decide +kernel

private theorem r_1396459 : RangeOk getRow 2051521 1396459 1396511 := by
  decide +kernel

private theorem r_1396511 : RangeOk getRow 2051521 1396511 1396574 := by
  decide +kernel

private theorem r_1396574 : RangeOk getRow 2051521 1396574 1396643 := by
  decide +kernel

private theorem r_1396643 : RangeOk getRow 2051521 1396643 1396712 := by
  decide +kernel

private theorem r_1396712 : RangeOk getRow 2051521 1396712 1396784 := by
  decide +kernel

private theorem r_1396784 : RangeOk getRow 2051521 1396784 1396858 := by
  decide +kernel

private theorem r_1396858 : RangeOk getRow 2051521 1396858 1396929 := by
  decide +kernel

private theorem r_1396929 : RangeOk getRow 2051521 1396929 1397000 := by
  decide +kernel

private theorem r_1397000 : RangeOk getRow 2051521 1397000 1397072 := by
  decide +kernel

private theorem r_1397072 : RangeOk getRow 2051521 1397072 1397142 := by
  decide +kernel

private theorem r_1397142 : RangeOk getRow 2051521 1397142 1397212 := by
  decide +kernel

private theorem r_1397212 : RangeOk getRow 2051521 1397212 1397283 := by
  decide +kernel

private theorem r_1397283 : RangeOk getRow 2051521 1397283 1397354 := by
  decide +kernel

private theorem r_1397354 : RangeOk getRow 2051521 1397354 1397428 := by
  decide +kernel

private theorem r_1397428 : RangeOk getRow 2051521 1397428 1397501 := by
  decide +kernel

private theorem r_1397501 : RangeOk getRow 2051521 1397501 1397577 := by
  decide +kernel

private theorem r_1397577 : RangeOk getRow 2051521 1397577 1397652 := by
  decide +kernel

private theorem r_1397652 : RangeOk getRow 2051521 1397652 1397728 := by
  decide +kernel

private theorem r_1397728 : RangeOk getRow 2051521 1397728 1397804 := by
  decide +kernel

private theorem r_1397804 : RangeOk getRow 2051521 1397804 1397880 := by
  decide +kernel

private theorem r_1397880 : RangeOk getRow 2051521 1397880 1397954 := by
  decide +kernel

private theorem r_1397954 : RangeOk getRow 2051521 1397954 1398025 := by
  decide +kernel

private theorem r_1398025 : RangeOk getRow 2051521 1398025 1398097 := by
  decide +kernel

private theorem r_1398097 : RangeOk getRow 2051521 1398097 1398168 := by
  decide +kernel

private theorem r_1398168 : RangeOk getRow 2051521 1398168 1398238 := by
  decide +kernel

private theorem r_1398238 : RangeOk getRow 2051521 1398238 1398310 := by
  decide +kernel

private theorem r_1398310 : RangeOk getRow 2051521 1398310 1398381 := by
  decide +kernel

private theorem r_1398381 : RangeOk getRow 2051521 1398381 1398451 := by
  decide +kernel

private theorem r_1398451 : RangeOk getRow 2051521 1398451 1398521 := by
  decide +kernel

private theorem r_1398521 : RangeOk getRow 2051521 1398521 1398591 := by
  decide +kernel

private theorem r_1398591 : RangeOk getRow 2051521 1398591 1398661 := by
  decide +kernel

private theorem r_1398661 : RangeOk getRow 2051521 1398661 1398733 := by
  decide +kernel

private theorem r_1398733 : RangeOk getRow 2051521 1398733 1398806 := by
  decide +kernel

private theorem r_1398806 : RangeOk getRow 2051521 1398806 1398877 := by
  decide +kernel

private theorem r_1398877 : RangeOk getRow 2051521 1398877 1398947 := by
  decide +kernel

private theorem r_1398947 : RangeOk getRow 2051521 1398947 1399018 := by
  decide +kernel

private theorem r_1399018 : RangeOk getRow 2051521 1399018 1399091 := by
  decide +kernel

private theorem r_1399091 : RangeOk getRow 2051521 1399091 1399163 := by
  decide +kernel

private theorem r_1399163 : RangeOk getRow 2051521 1399163 1399236 := by
  decide +kernel

private theorem r_1399236 : RangeOk getRow 2051521 1399236 1399309 := by
  decide +kernel

private theorem r_1399309 : RangeOk getRow 2051521 1399309 1399383 := by
  decide +kernel

private theorem r_1399383 : RangeOk getRow 2051521 1399383 1399455 := by
  decide +kernel

private theorem r_1399455 : RangeOk getRow 2051521 1399455 1399526 := by
  decide +kernel

private theorem r_1399526 : RangeOk getRow 2051521 1399526 1399598 := by
  decide +kernel

private theorem s_1396201 : RangeOk getRow 2051521 1396171 1396201 := r_1396171
private theorem s_1396273 : RangeOk getRow 2051521 1396171 1396273 :=
  s_1396201.append (by norm_num) r_1396201
private theorem s_1396343 : RangeOk getRow 2051521 1396171 1396343 :=
  s_1396273.append (by norm_num) r_1396273
private theorem s_1396379 : RangeOk getRow 2051521 1396171 1396379 :=
  s_1396343.append (by norm_num) r_1396343
private theorem s_1396415 : RangeOk getRow 2051521 1396171 1396415 :=
  s_1396379.append (by norm_num) r_1396379
private theorem s_1396459 : RangeOk getRow 2051521 1396171 1396459 :=
  s_1396415.append (by norm_num) r_1396415
private theorem s_1396511 : RangeOk getRow 2051521 1396171 1396511 :=
  s_1396459.append (by norm_num) r_1396459
private theorem s_1396574 : RangeOk getRow 2051521 1396171 1396574 :=
  s_1396511.append (by norm_num) r_1396511
private theorem s_1396643 : RangeOk getRow 2051521 1396171 1396643 :=
  s_1396574.append (by norm_num) r_1396574
private theorem s_1396712 : RangeOk getRow 2051521 1396171 1396712 :=
  s_1396643.append (by norm_num) r_1396643
private theorem s_1396784 : RangeOk getRow 2051521 1396171 1396784 :=
  s_1396712.append (by norm_num) r_1396712
private theorem s_1396858 : RangeOk getRow 2051521 1396171 1396858 :=
  s_1396784.append (by norm_num) r_1396784
private theorem s_1396929 : RangeOk getRow 2051521 1396171 1396929 :=
  s_1396858.append (by norm_num) r_1396858
private theorem s_1397000 : RangeOk getRow 2051521 1396171 1397000 :=
  s_1396929.append (by norm_num) r_1396929
private theorem s_1397072 : RangeOk getRow 2051521 1396171 1397072 :=
  s_1397000.append (by norm_num) r_1397000
private theorem s_1397142 : RangeOk getRow 2051521 1396171 1397142 :=
  s_1397072.append (by norm_num) r_1397072
private theorem s_1397212 : RangeOk getRow 2051521 1396171 1397212 :=
  s_1397142.append (by norm_num) r_1397142
private theorem s_1397283 : RangeOk getRow 2051521 1396171 1397283 :=
  s_1397212.append (by norm_num) r_1397212
private theorem s_1397354 : RangeOk getRow 2051521 1396171 1397354 :=
  s_1397283.append (by norm_num) r_1397283
private theorem s_1397428 : RangeOk getRow 2051521 1396171 1397428 :=
  s_1397354.append (by norm_num) r_1397354
private theorem s_1397501 : RangeOk getRow 2051521 1396171 1397501 :=
  s_1397428.append (by norm_num) r_1397428
private theorem s_1397577 : RangeOk getRow 2051521 1396171 1397577 :=
  s_1397501.append (by norm_num) r_1397501
private theorem s_1397652 : RangeOk getRow 2051521 1396171 1397652 :=
  s_1397577.append (by norm_num) r_1397577
private theorem s_1397728 : RangeOk getRow 2051521 1396171 1397728 :=
  s_1397652.append (by norm_num) r_1397652
private theorem s_1397804 : RangeOk getRow 2051521 1396171 1397804 :=
  s_1397728.append (by norm_num) r_1397728
private theorem s_1397880 : RangeOk getRow 2051521 1396171 1397880 :=
  s_1397804.append (by norm_num) r_1397804
private theorem s_1397954 : RangeOk getRow 2051521 1396171 1397954 :=
  s_1397880.append (by norm_num) r_1397880
private theorem s_1398025 : RangeOk getRow 2051521 1396171 1398025 :=
  s_1397954.append (by norm_num) r_1397954
private theorem s_1398097 : RangeOk getRow 2051521 1396171 1398097 :=
  s_1398025.append (by norm_num) r_1398025
private theorem s_1398168 : RangeOk getRow 2051521 1396171 1398168 :=
  s_1398097.append (by norm_num) r_1398097
private theorem s_1398238 : RangeOk getRow 2051521 1396171 1398238 :=
  s_1398168.append (by norm_num) r_1398168
private theorem s_1398310 : RangeOk getRow 2051521 1396171 1398310 :=
  s_1398238.append (by norm_num) r_1398238
private theorem s_1398381 : RangeOk getRow 2051521 1396171 1398381 :=
  s_1398310.append (by norm_num) r_1398310
private theorem s_1398451 : RangeOk getRow 2051521 1396171 1398451 :=
  s_1398381.append (by norm_num) r_1398381
private theorem s_1398521 : RangeOk getRow 2051521 1396171 1398521 :=
  s_1398451.append (by norm_num) r_1398451
private theorem s_1398591 : RangeOk getRow 2051521 1396171 1398591 :=
  s_1398521.append (by norm_num) r_1398521
private theorem s_1398661 : RangeOk getRow 2051521 1396171 1398661 :=
  s_1398591.append (by norm_num) r_1398591
private theorem s_1398733 : RangeOk getRow 2051521 1396171 1398733 :=
  s_1398661.append (by norm_num) r_1398661
private theorem s_1398806 : RangeOk getRow 2051521 1396171 1398806 :=
  s_1398733.append (by norm_num) r_1398733
private theorem s_1398877 : RangeOk getRow 2051521 1396171 1398877 :=
  s_1398806.append (by norm_num) r_1398806
private theorem s_1398947 : RangeOk getRow 2051521 1396171 1398947 :=
  s_1398877.append (by norm_num) r_1398877
private theorem s_1399018 : RangeOk getRow 2051521 1396171 1399018 :=
  s_1398947.append (by norm_num) r_1398947
private theorem s_1399091 : RangeOk getRow 2051521 1396171 1399091 :=
  s_1399018.append (by norm_num) r_1399018
private theorem s_1399163 : RangeOk getRow 2051521 1396171 1399163 :=
  s_1399091.append (by norm_num) r_1399091
private theorem s_1399236 : RangeOk getRow 2051521 1396171 1399236 :=
  s_1399163.append (by norm_num) r_1399163
private theorem s_1399309 : RangeOk getRow 2051521 1396171 1399309 :=
  s_1399236.append (by norm_num) r_1399236
private theorem s_1399383 : RangeOk getRow 2051521 1396171 1399383 :=
  s_1399309.append (by norm_num) r_1399309
private theorem s_1399455 : RangeOk getRow 2051521 1396171 1399455 :=
  s_1399383.append (by norm_num) r_1399383
private theorem s_1399526 : RangeOk getRow 2051521 1396171 1399526 :=
  s_1399455.append (by norm_num) r_1399455
private theorem s_1399598 : RangeOk getRow 2051521 1396171 1399598 :=
  s_1399526.append (by norm_num) r_1399526

/-- Rows `[1396171, 1399598)` are valid. -/
theorem rangeOk_1396171_1399598 : RangeOk getRow 2051521 1396171 1399598 := s_1399598

end Noperthedron.Solution
