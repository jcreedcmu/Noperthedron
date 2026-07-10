import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[903012, 905546). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_903012 : RangeOk getRow 2051521 903012 903077 := by
  decide +kernel

private theorem r_903077 : RangeOk getRow 2051521 903077 903144 := by
  decide +kernel

private theorem r_903144 : RangeOk getRow 2051521 903144 903210 := by
  decide +kernel

private theorem r_903210 : RangeOk getRow 2051521 903210 903278 := by
  decide +kernel

private theorem r_903278 : RangeOk getRow 2051521 903278 903349 := by
  decide +kernel

private theorem r_903349 : RangeOk getRow 2051521 903349 903419 := by
  decide +kernel

private theorem r_903419 : RangeOk getRow 2051521 903419 903492 := by
  decide +kernel

private theorem r_903492 : RangeOk getRow 2051521 903492 903560 := by
  decide +kernel

private theorem r_903560 : RangeOk getRow 2051521 903560 903630 := by
  decide +kernel

private theorem r_903630 : RangeOk getRow 2051521 903630 903698 := by
  decide +kernel

private theorem r_903698 : RangeOk getRow 2051521 903698 903768 := by
  decide +kernel

private theorem r_903768 : RangeOk getRow 2051521 903768 903838 := by
  decide +kernel

private theorem r_903838 : RangeOk getRow 2051521 903838 903908 := by
  decide +kernel

private theorem r_903908 : RangeOk getRow 2051521 903908 903979 := by
  decide +kernel

private theorem r_903979 : RangeOk getRow 2051521 903979 904047 := by
  decide +kernel

private theorem r_904047 : RangeOk getRow 2051521 904047 904119 := by
  decide +kernel

private theorem r_904119 : RangeOk getRow 2051521 904119 904187 := by
  decide +kernel

private theorem r_904187 : RangeOk getRow 2051521 904187 904256 := by
  decide +kernel

private theorem r_904256 : RangeOk getRow 2051521 904256 904326 := by
  decide +kernel

private theorem r_904326 : RangeOk getRow 2051521 904326 904396 := by
  decide +kernel

private theorem r_904396 : RangeOk getRow 2051521 904396 904464 := by
  decide +kernel

private theorem r_904464 : RangeOk getRow 2051521 904464 904530 := by
  decide +kernel

private theorem r_904530 : RangeOk getRow 2051521 904530 904597 := by
  decide +kernel

private theorem r_904597 : RangeOk getRow 2051521 904597 904666 := by
  decide +kernel

private theorem r_904666 : RangeOk getRow 2051521 904666 904733 := by
  decide +kernel

private theorem r_904733 : RangeOk getRow 2051521 904733 904800 := by
  decide +kernel

private theorem r_904800 : RangeOk getRow 2051521 904800 904865 := by
  decide +kernel

private theorem r_904865 : RangeOk getRow 2051521 904865 904931 := by
  decide +kernel

private theorem r_904931 : RangeOk getRow 2051521 904931 904997 := by
  decide +kernel

private theorem r_904997 : RangeOk getRow 2051521 904997 905062 := by
  decide +kernel

private theorem r_905062 : RangeOk getRow 2051521 905062 905126 := by
  decide +kernel

private theorem r_905126 : RangeOk getRow 2051521 905126 905197 := by
  decide +kernel

private theorem r_905197 : RangeOk getRow 2051521 905197 905267 := by
  decide +kernel

private theorem r_905267 : RangeOk getRow 2051521 905267 905336 := by
  decide +kernel

private theorem r_905336 : RangeOk getRow 2051521 905336 905404 := by
  decide +kernel

private theorem r_905404 : RangeOk getRow 2051521 905404 905476 := by
  decide +kernel

private theorem r_905476 : RangeOk getRow 2051521 905476 905546 := by
  decide +kernel

private theorem s_903077 : RangeOk getRow 2051521 903012 903077 := r_903012
private theorem s_903144 : RangeOk getRow 2051521 903012 903144 :=
  s_903077.append (by norm_num) r_903077
private theorem s_903210 : RangeOk getRow 2051521 903012 903210 :=
  s_903144.append (by norm_num) r_903144
private theorem s_903278 : RangeOk getRow 2051521 903012 903278 :=
  s_903210.append (by norm_num) r_903210
private theorem s_903349 : RangeOk getRow 2051521 903012 903349 :=
  s_903278.append (by norm_num) r_903278
private theorem s_903419 : RangeOk getRow 2051521 903012 903419 :=
  s_903349.append (by norm_num) r_903349
private theorem s_903492 : RangeOk getRow 2051521 903012 903492 :=
  s_903419.append (by norm_num) r_903419
private theorem s_903560 : RangeOk getRow 2051521 903012 903560 :=
  s_903492.append (by norm_num) r_903492
private theorem s_903630 : RangeOk getRow 2051521 903012 903630 :=
  s_903560.append (by norm_num) r_903560
private theorem s_903698 : RangeOk getRow 2051521 903012 903698 :=
  s_903630.append (by norm_num) r_903630
private theorem s_903768 : RangeOk getRow 2051521 903012 903768 :=
  s_903698.append (by norm_num) r_903698
private theorem s_903838 : RangeOk getRow 2051521 903012 903838 :=
  s_903768.append (by norm_num) r_903768
private theorem s_903908 : RangeOk getRow 2051521 903012 903908 :=
  s_903838.append (by norm_num) r_903838
private theorem s_903979 : RangeOk getRow 2051521 903012 903979 :=
  s_903908.append (by norm_num) r_903908
private theorem s_904047 : RangeOk getRow 2051521 903012 904047 :=
  s_903979.append (by norm_num) r_903979
private theorem s_904119 : RangeOk getRow 2051521 903012 904119 :=
  s_904047.append (by norm_num) r_904047
private theorem s_904187 : RangeOk getRow 2051521 903012 904187 :=
  s_904119.append (by norm_num) r_904119
private theorem s_904256 : RangeOk getRow 2051521 903012 904256 :=
  s_904187.append (by norm_num) r_904187
private theorem s_904326 : RangeOk getRow 2051521 903012 904326 :=
  s_904256.append (by norm_num) r_904256
private theorem s_904396 : RangeOk getRow 2051521 903012 904396 :=
  s_904326.append (by norm_num) r_904326
private theorem s_904464 : RangeOk getRow 2051521 903012 904464 :=
  s_904396.append (by norm_num) r_904396
private theorem s_904530 : RangeOk getRow 2051521 903012 904530 :=
  s_904464.append (by norm_num) r_904464
private theorem s_904597 : RangeOk getRow 2051521 903012 904597 :=
  s_904530.append (by norm_num) r_904530
private theorem s_904666 : RangeOk getRow 2051521 903012 904666 :=
  s_904597.append (by norm_num) r_904597
private theorem s_904733 : RangeOk getRow 2051521 903012 904733 :=
  s_904666.append (by norm_num) r_904666
private theorem s_904800 : RangeOk getRow 2051521 903012 904800 :=
  s_904733.append (by norm_num) r_904733
private theorem s_904865 : RangeOk getRow 2051521 903012 904865 :=
  s_904800.append (by norm_num) r_904800
private theorem s_904931 : RangeOk getRow 2051521 903012 904931 :=
  s_904865.append (by norm_num) r_904865
private theorem s_904997 : RangeOk getRow 2051521 903012 904997 :=
  s_904931.append (by norm_num) r_904931
private theorem s_905062 : RangeOk getRow 2051521 903012 905062 :=
  s_904997.append (by norm_num) r_904997
private theorem s_905126 : RangeOk getRow 2051521 903012 905126 :=
  s_905062.append (by norm_num) r_905062
private theorem s_905197 : RangeOk getRow 2051521 903012 905197 :=
  s_905126.append (by norm_num) r_905126
private theorem s_905267 : RangeOk getRow 2051521 903012 905267 :=
  s_905197.append (by norm_num) r_905197
private theorem s_905336 : RangeOk getRow 2051521 903012 905336 :=
  s_905267.append (by norm_num) r_905267
private theorem s_905404 : RangeOk getRow 2051521 903012 905404 :=
  s_905336.append (by norm_num) r_905336
private theorem s_905476 : RangeOk getRow 2051521 903012 905476 :=
  s_905404.append (by norm_num) r_905404
private theorem s_905546 : RangeOk getRow 2051521 903012 905546 :=
  s_905476.append (by norm_num) r_905476

/-- Rows `[903012, 905546)` are valid. -/
theorem rangeOk_903012_905546 : RangeOk getRow 2051521 903012 905546 := s_905546

end Noperthedron.Solution
