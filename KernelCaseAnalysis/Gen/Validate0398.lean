import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[960761, 963382). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_960761 : RangeOk getRow 2051521 960761 960827 := by
  decide +kernel

private theorem r_960827 : RangeOk getRow 2051521 960827 960894 := by
  decide +kernel

private theorem r_960894 : RangeOk getRow 2051521 960894 960961 := by
  decide +kernel

private theorem r_960961 : RangeOk getRow 2051521 960961 961028 := by
  decide +kernel

private theorem r_961028 : RangeOk getRow 2051521 961028 961097 := by
  decide +kernel

private theorem r_961097 : RangeOk getRow 2051521 961097 961169 := by
  decide +kernel

private theorem r_961169 : RangeOk getRow 2051521 961169 961238 := by
  decide +kernel

private theorem r_961238 : RangeOk getRow 2051521 961238 961308 := by
  decide +kernel

private theorem r_961308 : RangeOk getRow 2051521 961308 961381 := by
  decide +kernel

private theorem r_961381 : RangeOk getRow 2051521 961381 961451 := by
  decide +kernel

private theorem r_961451 : RangeOk getRow 2051521 961451 961520 := by
  decide +kernel

private theorem r_961520 : RangeOk getRow 2051521 961520 961589 := by
  decide +kernel

private theorem r_961589 : RangeOk getRow 2051521 961589 961659 := by
  decide +kernel

private theorem r_961659 : RangeOk getRow 2051521 961659 961728 := by
  decide +kernel

private theorem r_961728 : RangeOk getRow 2051521 961728 961797 := by
  decide +kernel

private theorem r_961797 : RangeOk getRow 2051521 961797 961867 := by
  decide +kernel

private theorem r_961867 : RangeOk getRow 2051521 961867 961939 := by
  decide +kernel

private theorem r_961939 : RangeOk getRow 2051521 961939 962011 := by
  decide +kernel

private theorem r_962011 : RangeOk getRow 2051521 962011 962082 := by
  decide +kernel

private theorem r_962082 : RangeOk getRow 2051521 962082 962152 := by
  decide +kernel

private theorem r_962152 : RangeOk getRow 2051521 962152 962220 := by
  decide +kernel

private theorem r_962220 : RangeOk getRow 2051521 962220 962289 := by
  decide +kernel

private theorem r_962289 : RangeOk getRow 2051521 962289 962357 := by
  decide +kernel

private theorem r_962357 : RangeOk getRow 2051521 962357 962423 := by
  decide +kernel

private theorem r_962423 : RangeOk getRow 2051521 962423 962490 := by
  decide +kernel

private theorem r_962490 : RangeOk getRow 2051521 962490 962556 := by
  decide +kernel

private theorem r_962556 : RangeOk getRow 2051521 962556 962622 := by
  decide +kernel

private theorem r_962622 : RangeOk getRow 2051521 962622 962686 := by
  decide +kernel

private theorem r_962686 : RangeOk getRow 2051521 962686 962750 := by
  decide +kernel

private theorem r_962750 : RangeOk getRow 2051521 962750 962820 := by
  decide +kernel

private theorem r_962820 : RangeOk getRow 2051521 962820 962890 := by
  decide +kernel

private theorem r_962890 : RangeOk getRow 2051521 962890 962960 := by
  decide +kernel

private theorem r_962960 : RangeOk getRow 2051521 962960 963030 := by
  decide +kernel

private theorem r_963030 : RangeOk getRow 2051521 963030 963101 := by
  decide +kernel

private theorem r_963101 : RangeOk getRow 2051521 963101 963173 := by
  decide +kernel

private theorem r_963173 : RangeOk getRow 2051521 963173 963243 := by
  decide +kernel

private theorem r_963243 : RangeOk getRow 2051521 963243 963312 := by
  decide +kernel

private theorem r_963312 : RangeOk getRow 2051521 963312 963382 := by
  decide +kernel

private theorem s_960827 : RangeOk getRow 2051521 960761 960827 := r_960761
private theorem s_960894 : RangeOk getRow 2051521 960761 960894 :=
  s_960827.append (by norm_num) r_960827
private theorem s_960961 : RangeOk getRow 2051521 960761 960961 :=
  s_960894.append (by norm_num) r_960894
private theorem s_961028 : RangeOk getRow 2051521 960761 961028 :=
  s_960961.append (by norm_num) r_960961
private theorem s_961097 : RangeOk getRow 2051521 960761 961097 :=
  s_961028.append (by norm_num) r_961028
private theorem s_961169 : RangeOk getRow 2051521 960761 961169 :=
  s_961097.append (by norm_num) r_961097
private theorem s_961238 : RangeOk getRow 2051521 960761 961238 :=
  s_961169.append (by norm_num) r_961169
private theorem s_961308 : RangeOk getRow 2051521 960761 961308 :=
  s_961238.append (by norm_num) r_961238
private theorem s_961381 : RangeOk getRow 2051521 960761 961381 :=
  s_961308.append (by norm_num) r_961308
private theorem s_961451 : RangeOk getRow 2051521 960761 961451 :=
  s_961381.append (by norm_num) r_961381
private theorem s_961520 : RangeOk getRow 2051521 960761 961520 :=
  s_961451.append (by norm_num) r_961451
private theorem s_961589 : RangeOk getRow 2051521 960761 961589 :=
  s_961520.append (by norm_num) r_961520
private theorem s_961659 : RangeOk getRow 2051521 960761 961659 :=
  s_961589.append (by norm_num) r_961589
private theorem s_961728 : RangeOk getRow 2051521 960761 961728 :=
  s_961659.append (by norm_num) r_961659
private theorem s_961797 : RangeOk getRow 2051521 960761 961797 :=
  s_961728.append (by norm_num) r_961728
private theorem s_961867 : RangeOk getRow 2051521 960761 961867 :=
  s_961797.append (by norm_num) r_961797
private theorem s_961939 : RangeOk getRow 2051521 960761 961939 :=
  s_961867.append (by norm_num) r_961867
private theorem s_962011 : RangeOk getRow 2051521 960761 962011 :=
  s_961939.append (by norm_num) r_961939
private theorem s_962082 : RangeOk getRow 2051521 960761 962082 :=
  s_962011.append (by norm_num) r_962011
private theorem s_962152 : RangeOk getRow 2051521 960761 962152 :=
  s_962082.append (by norm_num) r_962082
private theorem s_962220 : RangeOk getRow 2051521 960761 962220 :=
  s_962152.append (by norm_num) r_962152
private theorem s_962289 : RangeOk getRow 2051521 960761 962289 :=
  s_962220.append (by norm_num) r_962220
private theorem s_962357 : RangeOk getRow 2051521 960761 962357 :=
  s_962289.append (by norm_num) r_962289
private theorem s_962423 : RangeOk getRow 2051521 960761 962423 :=
  s_962357.append (by norm_num) r_962357
private theorem s_962490 : RangeOk getRow 2051521 960761 962490 :=
  s_962423.append (by norm_num) r_962423
private theorem s_962556 : RangeOk getRow 2051521 960761 962556 :=
  s_962490.append (by norm_num) r_962490
private theorem s_962622 : RangeOk getRow 2051521 960761 962622 :=
  s_962556.append (by norm_num) r_962556
private theorem s_962686 : RangeOk getRow 2051521 960761 962686 :=
  s_962622.append (by norm_num) r_962622
private theorem s_962750 : RangeOk getRow 2051521 960761 962750 :=
  s_962686.append (by norm_num) r_962686
private theorem s_962820 : RangeOk getRow 2051521 960761 962820 :=
  s_962750.append (by norm_num) r_962750
private theorem s_962890 : RangeOk getRow 2051521 960761 962890 :=
  s_962820.append (by norm_num) r_962820
private theorem s_962960 : RangeOk getRow 2051521 960761 962960 :=
  s_962890.append (by norm_num) r_962890
private theorem s_963030 : RangeOk getRow 2051521 960761 963030 :=
  s_962960.append (by norm_num) r_962960
private theorem s_963101 : RangeOk getRow 2051521 960761 963101 :=
  s_963030.append (by norm_num) r_963030
private theorem s_963173 : RangeOk getRow 2051521 960761 963173 :=
  s_963101.append (by norm_num) r_963101
private theorem s_963243 : RangeOk getRow 2051521 960761 963243 :=
  s_963173.append (by norm_num) r_963173
private theorem s_963312 : RangeOk getRow 2051521 960761 963312 :=
  s_963243.append (by norm_num) r_963243
private theorem s_963382 : RangeOk getRow 2051521 960761 963382 :=
  s_963312.append (by norm_num) r_963312

/-- Rows `[960761, 963382)` are valid. -/
theorem rangeOk_960761_963382 : RangeOk getRow 2051521 960761 963382 := s_963382

end Noperthedron.Solution
