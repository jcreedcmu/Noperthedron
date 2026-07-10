import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[307429, 310210). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_307429 : RangeOk getRow 2051521 307429 307501 := by
  decide +kernel

private theorem r_307501 : RangeOk getRow 2051521 307501 307572 := by
  decide +kernel

private theorem r_307572 : RangeOk getRow 2051521 307572 307640 := by
  decide +kernel

private theorem r_307640 : RangeOk getRow 2051521 307640 307708 := by
  decide +kernel

private theorem r_307708 : RangeOk getRow 2051521 307708 307774 := by
  decide +kernel

private theorem r_307774 : RangeOk getRow 2051521 307774 307845 := by
  decide +kernel

private theorem r_307845 : RangeOk getRow 2051521 307845 307919 := by
  decide +kernel

private theorem r_307919 : RangeOk getRow 2051521 307919 307990 := by
  decide +kernel

private theorem r_307990 : RangeOk getRow 2051521 307990 308062 := by
  decide +kernel

private theorem r_308062 : RangeOk getRow 2051521 308062 308134 := by
  decide +kernel

private theorem r_308134 : RangeOk getRow 2051521 308134 308205 := by
  decide +kernel

private theorem r_308205 : RangeOk getRow 2051521 308205 308271 := by
  decide +kernel

private theorem r_308271 : RangeOk getRow 2051521 308271 308338 := by
  decide +kernel

private theorem r_308338 : RangeOk getRow 2051521 308338 308408 := by
  decide +kernel

private theorem r_308408 : RangeOk getRow 2051521 308408 308479 := by
  decide +kernel

private theorem r_308479 : RangeOk getRow 2051521 308479 308552 := by
  decide +kernel

private theorem r_308552 : RangeOk getRow 2051521 308552 308622 := by
  decide +kernel

private theorem r_308622 : RangeOk getRow 2051521 308622 308693 := by
  decide +kernel

private theorem r_308693 : RangeOk getRow 2051521 308693 308764 := by
  decide +kernel

private theorem r_308764 : RangeOk getRow 2051521 308764 308836 := by
  decide +kernel

private theorem r_308836 : RangeOk getRow 2051521 308836 308903 := by
  decide +kernel

private theorem r_308903 : RangeOk getRow 2051521 308903 308970 := by
  decide +kernel

private theorem r_308970 : RangeOk getRow 2051521 308970 309036 := by
  decide +kernel

private theorem r_309036 : RangeOk getRow 2051521 309036 309105 := by
  decide +kernel

private theorem r_309105 : RangeOk getRow 2051521 309105 309177 := by
  decide +kernel

private theorem r_309177 : RangeOk getRow 2051521 309177 309247 := by
  decide +kernel

private theorem r_309247 : RangeOk getRow 2051521 309247 309318 := by
  decide +kernel

private theorem r_309318 : RangeOk getRow 2051521 309318 309389 := by
  decide +kernel

private theorem r_309389 : RangeOk getRow 2051521 309389 309459 := by
  decide +kernel

private theorem r_309459 : RangeOk getRow 2051521 309459 309526 := by
  decide +kernel

private theorem r_309526 : RangeOk getRow 2051521 309526 309594 := by
  decide +kernel

private theorem r_309594 : RangeOk getRow 2051521 309594 309663 := by
  decide +kernel

private theorem r_309663 : RangeOk getRow 2051521 309663 309732 := by
  decide +kernel

private theorem r_309732 : RangeOk getRow 2051521 309732 309803 := by
  decide +kernel

private theorem r_309803 : RangeOk getRow 2051521 309803 309873 := by
  decide +kernel

private theorem r_309873 : RangeOk getRow 2051521 309873 309944 := by
  decide +kernel

private theorem r_309944 : RangeOk getRow 2051521 309944 310015 := by
  decide +kernel

private theorem r_310015 : RangeOk getRow 2051521 310015 310083 := by
  decide +kernel

private theorem r_310083 : RangeOk getRow 2051521 310083 310144 := by
  decide +kernel

private theorem r_310144 : RangeOk getRow 2051521 310144 310210 := by
  decide +kernel

private theorem s_307501 : RangeOk getRow 2051521 307429 307501 := r_307429
private theorem s_307572 : RangeOk getRow 2051521 307429 307572 :=
  s_307501.append (by norm_num) r_307501
private theorem s_307640 : RangeOk getRow 2051521 307429 307640 :=
  s_307572.append (by norm_num) r_307572
private theorem s_307708 : RangeOk getRow 2051521 307429 307708 :=
  s_307640.append (by norm_num) r_307640
private theorem s_307774 : RangeOk getRow 2051521 307429 307774 :=
  s_307708.append (by norm_num) r_307708
private theorem s_307845 : RangeOk getRow 2051521 307429 307845 :=
  s_307774.append (by norm_num) r_307774
private theorem s_307919 : RangeOk getRow 2051521 307429 307919 :=
  s_307845.append (by norm_num) r_307845
private theorem s_307990 : RangeOk getRow 2051521 307429 307990 :=
  s_307919.append (by norm_num) r_307919
private theorem s_308062 : RangeOk getRow 2051521 307429 308062 :=
  s_307990.append (by norm_num) r_307990
private theorem s_308134 : RangeOk getRow 2051521 307429 308134 :=
  s_308062.append (by norm_num) r_308062
private theorem s_308205 : RangeOk getRow 2051521 307429 308205 :=
  s_308134.append (by norm_num) r_308134
private theorem s_308271 : RangeOk getRow 2051521 307429 308271 :=
  s_308205.append (by norm_num) r_308205
private theorem s_308338 : RangeOk getRow 2051521 307429 308338 :=
  s_308271.append (by norm_num) r_308271
private theorem s_308408 : RangeOk getRow 2051521 307429 308408 :=
  s_308338.append (by norm_num) r_308338
private theorem s_308479 : RangeOk getRow 2051521 307429 308479 :=
  s_308408.append (by norm_num) r_308408
private theorem s_308552 : RangeOk getRow 2051521 307429 308552 :=
  s_308479.append (by norm_num) r_308479
private theorem s_308622 : RangeOk getRow 2051521 307429 308622 :=
  s_308552.append (by norm_num) r_308552
private theorem s_308693 : RangeOk getRow 2051521 307429 308693 :=
  s_308622.append (by norm_num) r_308622
private theorem s_308764 : RangeOk getRow 2051521 307429 308764 :=
  s_308693.append (by norm_num) r_308693
private theorem s_308836 : RangeOk getRow 2051521 307429 308836 :=
  s_308764.append (by norm_num) r_308764
private theorem s_308903 : RangeOk getRow 2051521 307429 308903 :=
  s_308836.append (by norm_num) r_308836
private theorem s_308970 : RangeOk getRow 2051521 307429 308970 :=
  s_308903.append (by norm_num) r_308903
private theorem s_309036 : RangeOk getRow 2051521 307429 309036 :=
  s_308970.append (by norm_num) r_308970
private theorem s_309105 : RangeOk getRow 2051521 307429 309105 :=
  s_309036.append (by norm_num) r_309036
private theorem s_309177 : RangeOk getRow 2051521 307429 309177 :=
  s_309105.append (by norm_num) r_309105
private theorem s_309247 : RangeOk getRow 2051521 307429 309247 :=
  s_309177.append (by norm_num) r_309177
private theorem s_309318 : RangeOk getRow 2051521 307429 309318 :=
  s_309247.append (by norm_num) r_309247
private theorem s_309389 : RangeOk getRow 2051521 307429 309389 :=
  s_309318.append (by norm_num) r_309318
private theorem s_309459 : RangeOk getRow 2051521 307429 309459 :=
  s_309389.append (by norm_num) r_309389
private theorem s_309526 : RangeOk getRow 2051521 307429 309526 :=
  s_309459.append (by norm_num) r_309459
private theorem s_309594 : RangeOk getRow 2051521 307429 309594 :=
  s_309526.append (by norm_num) r_309526
private theorem s_309663 : RangeOk getRow 2051521 307429 309663 :=
  s_309594.append (by norm_num) r_309594
private theorem s_309732 : RangeOk getRow 2051521 307429 309732 :=
  s_309663.append (by norm_num) r_309663
private theorem s_309803 : RangeOk getRow 2051521 307429 309803 :=
  s_309732.append (by norm_num) r_309732
private theorem s_309873 : RangeOk getRow 2051521 307429 309873 :=
  s_309803.append (by norm_num) r_309803
private theorem s_309944 : RangeOk getRow 2051521 307429 309944 :=
  s_309873.append (by norm_num) r_309873
private theorem s_310015 : RangeOk getRow 2051521 307429 310015 :=
  s_309944.append (by norm_num) r_309944
private theorem s_310083 : RangeOk getRow 2051521 307429 310083 :=
  s_310015.append (by norm_num) r_310015
private theorem s_310144 : RangeOk getRow 2051521 307429 310144 :=
  s_310083.append (by norm_num) r_310083
private theorem s_310210 : RangeOk getRow 2051521 307429 310210 :=
  s_310144.append (by norm_num) r_310144

/-- Rows `[307429, 310210)` are valid. -/
theorem rangeOk_307429_310210 : RangeOk getRow 2051521 307429 310210 := s_310210

end Noperthedron.Solution
