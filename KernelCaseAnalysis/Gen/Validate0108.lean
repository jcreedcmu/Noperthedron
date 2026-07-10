import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[243004, 245376). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_243004 : RangeOk getRow 2051521 243004 243069 := by
  decide +kernel

private theorem r_243069 : RangeOk getRow 2051521 243069 243137 := by
  decide +kernel

private theorem r_243137 : RangeOk getRow 2051521 243137 243204 := by
  decide +kernel

private theorem r_243204 : RangeOk getRow 2051521 243204 243271 := by
  decide +kernel

private theorem r_243271 : RangeOk getRow 2051521 243271 243337 := by
  decide +kernel

private theorem r_243337 : RangeOk getRow 2051521 243337 243401 := by
  decide +kernel

private theorem r_243401 : RangeOk getRow 2051521 243401 243466 := by
  decide +kernel

private theorem r_243466 : RangeOk getRow 2051521 243466 243531 := by
  decide +kernel

private theorem r_243531 : RangeOk getRow 2051521 243531 243597 := by
  decide +kernel

private theorem r_243597 : RangeOk getRow 2051521 243597 243663 := by
  decide +kernel

private theorem r_243663 : RangeOk getRow 2051521 243663 243730 := by
  decide +kernel

private theorem r_243730 : RangeOk getRow 2051521 243730 243796 := by
  decide +kernel

private theorem r_243796 : RangeOk getRow 2051521 243796 243865 := by
  decide +kernel

private theorem r_243865 : RangeOk getRow 2051521 243865 243935 := by
  decide +kernel

private theorem r_243935 : RangeOk getRow 2051521 243935 244003 := by
  decide +kernel

private theorem r_244003 : RangeOk getRow 2051521 244003 244071 := by
  decide +kernel

private theorem r_244071 : RangeOk getRow 2051521 244071 244140 := by
  decide +kernel

private theorem r_244140 : RangeOk getRow 2051521 244140 244209 := by
  decide +kernel

private theorem r_244209 : RangeOk getRow 2051521 244209 244278 := by
  decide +kernel

private theorem r_244278 : RangeOk getRow 2051521 244278 244347 := by
  decide +kernel

private theorem r_244347 : RangeOk getRow 2051521 244347 244417 := by
  decide +kernel

private theorem r_244417 : RangeOk getRow 2051521 244417 244488 := by
  decide +kernel

private theorem r_244488 : RangeOk getRow 2051521 244488 244556 := by
  decide +kernel

private theorem r_244556 : RangeOk getRow 2051521 244556 244624 := by
  decide +kernel

private theorem r_244624 : RangeOk getRow 2051521 244624 244694 := by
  decide +kernel

private theorem r_244694 : RangeOk getRow 2051521 244694 244763 := by
  decide +kernel

private theorem r_244763 : RangeOk getRow 2051521 244763 244830 := by
  decide +kernel

private theorem r_244830 : RangeOk getRow 2051521 244830 244897 := by
  decide +kernel

private theorem r_244897 : RangeOk getRow 2051521 244897 244964 := by
  decide +kernel

private theorem r_244964 : RangeOk getRow 2051521 244964 245035 := by
  decide +kernel

private theorem r_245035 : RangeOk getRow 2051521 245035 245104 := by
  decide +kernel

private theorem r_245104 : RangeOk getRow 2051521 245104 245169 := by
  decide +kernel

private theorem r_245169 : RangeOk getRow 2051521 245169 245237 := by
  decide +kernel

private theorem r_245237 : RangeOk getRow 2051521 245237 245307 := by
  decide +kernel

private theorem r_245307 : RangeOk getRow 2051521 245307 245376 := by
  decide +kernel

private theorem s_243069 : RangeOk getRow 2051521 243004 243069 := r_243004
private theorem s_243137 : RangeOk getRow 2051521 243004 243137 :=
  s_243069.append (by norm_num) r_243069
private theorem s_243204 : RangeOk getRow 2051521 243004 243204 :=
  s_243137.append (by norm_num) r_243137
private theorem s_243271 : RangeOk getRow 2051521 243004 243271 :=
  s_243204.append (by norm_num) r_243204
private theorem s_243337 : RangeOk getRow 2051521 243004 243337 :=
  s_243271.append (by norm_num) r_243271
private theorem s_243401 : RangeOk getRow 2051521 243004 243401 :=
  s_243337.append (by norm_num) r_243337
private theorem s_243466 : RangeOk getRow 2051521 243004 243466 :=
  s_243401.append (by norm_num) r_243401
private theorem s_243531 : RangeOk getRow 2051521 243004 243531 :=
  s_243466.append (by norm_num) r_243466
private theorem s_243597 : RangeOk getRow 2051521 243004 243597 :=
  s_243531.append (by norm_num) r_243531
private theorem s_243663 : RangeOk getRow 2051521 243004 243663 :=
  s_243597.append (by norm_num) r_243597
private theorem s_243730 : RangeOk getRow 2051521 243004 243730 :=
  s_243663.append (by norm_num) r_243663
private theorem s_243796 : RangeOk getRow 2051521 243004 243796 :=
  s_243730.append (by norm_num) r_243730
private theorem s_243865 : RangeOk getRow 2051521 243004 243865 :=
  s_243796.append (by norm_num) r_243796
private theorem s_243935 : RangeOk getRow 2051521 243004 243935 :=
  s_243865.append (by norm_num) r_243865
private theorem s_244003 : RangeOk getRow 2051521 243004 244003 :=
  s_243935.append (by norm_num) r_243935
private theorem s_244071 : RangeOk getRow 2051521 243004 244071 :=
  s_244003.append (by norm_num) r_244003
private theorem s_244140 : RangeOk getRow 2051521 243004 244140 :=
  s_244071.append (by norm_num) r_244071
private theorem s_244209 : RangeOk getRow 2051521 243004 244209 :=
  s_244140.append (by norm_num) r_244140
private theorem s_244278 : RangeOk getRow 2051521 243004 244278 :=
  s_244209.append (by norm_num) r_244209
private theorem s_244347 : RangeOk getRow 2051521 243004 244347 :=
  s_244278.append (by norm_num) r_244278
private theorem s_244417 : RangeOk getRow 2051521 243004 244417 :=
  s_244347.append (by norm_num) r_244347
private theorem s_244488 : RangeOk getRow 2051521 243004 244488 :=
  s_244417.append (by norm_num) r_244417
private theorem s_244556 : RangeOk getRow 2051521 243004 244556 :=
  s_244488.append (by norm_num) r_244488
private theorem s_244624 : RangeOk getRow 2051521 243004 244624 :=
  s_244556.append (by norm_num) r_244556
private theorem s_244694 : RangeOk getRow 2051521 243004 244694 :=
  s_244624.append (by norm_num) r_244624
private theorem s_244763 : RangeOk getRow 2051521 243004 244763 :=
  s_244694.append (by norm_num) r_244694
private theorem s_244830 : RangeOk getRow 2051521 243004 244830 :=
  s_244763.append (by norm_num) r_244763
private theorem s_244897 : RangeOk getRow 2051521 243004 244897 :=
  s_244830.append (by norm_num) r_244830
private theorem s_244964 : RangeOk getRow 2051521 243004 244964 :=
  s_244897.append (by norm_num) r_244897
private theorem s_245035 : RangeOk getRow 2051521 243004 245035 :=
  s_244964.append (by norm_num) r_244964
private theorem s_245104 : RangeOk getRow 2051521 243004 245104 :=
  s_245035.append (by norm_num) r_245035
private theorem s_245169 : RangeOk getRow 2051521 243004 245169 :=
  s_245104.append (by norm_num) r_245104
private theorem s_245237 : RangeOk getRow 2051521 243004 245237 :=
  s_245169.append (by norm_num) r_245169
private theorem s_245307 : RangeOk getRow 2051521 243004 245307 :=
  s_245237.append (by norm_num) r_245237
private theorem s_245376 : RangeOk getRow 2051521 243004 245376 :=
  s_245307.append (by norm_num) r_245307

/-- Rows `[243004, 245376)` are valid. -/
theorem rangeOk_243004_245376 : RangeOk getRow 2051521 243004 245376 := s_245376

end Noperthedron.Solution
