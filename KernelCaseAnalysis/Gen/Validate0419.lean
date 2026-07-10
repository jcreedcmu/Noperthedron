import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1015713, 1018492). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1015713 : RangeOk getRow 2051521 1015713 1015782 := by
  decide +kernel

private theorem r_1015782 : RangeOk getRow 2051521 1015782 1015852 := by
  decide +kernel

private theorem r_1015852 : RangeOk getRow 2051521 1015852 1015925 := by
  decide +kernel

private theorem r_1015925 : RangeOk getRow 2051521 1015925 1015996 := by
  decide +kernel

private theorem r_1015996 : RangeOk getRow 2051521 1015996 1016065 := by
  decide +kernel

private theorem r_1016065 : RangeOk getRow 2051521 1016065 1016135 := by
  decide +kernel

private theorem r_1016135 : RangeOk getRow 2051521 1016135 1016205 := by
  decide +kernel

private theorem r_1016205 : RangeOk getRow 2051521 1016205 1016275 := by
  decide +kernel

private theorem r_1016275 : RangeOk getRow 2051521 1016275 1016346 := by
  decide +kernel

private theorem r_1016346 : RangeOk getRow 2051521 1016346 1016414 := by
  decide +kernel

private theorem r_1016414 : RangeOk getRow 2051521 1016414 1016480 := by
  decide +kernel

private theorem r_1016480 : RangeOk getRow 2051521 1016480 1016544 := by
  decide +kernel

private theorem r_1016544 : RangeOk getRow 2051521 1016544 1016609 := by
  decide +kernel

private theorem r_1016609 : RangeOk getRow 2051521 1016609 1016679 := by
  decide +kernel

private theorem r_1016679 : RangeOk getRow 2051521 1016679 1016750 := by
  decide +kernel

private theorem r_1016750 : RangeOk getRow 2051521 1016750 1016819 := by
  decide +kernel

private theorem r_1016819 : RangeOk getRow 2051521 1016819 1016888 := by
  decide +kernel

private theorem r_1016888 : RangeOk getRow 2051521 1016888 1016959 := by
  decide +kernel

private theorem r_1016959 : RangeOk getRow 2051521 1016959 1017030 := by
  decide +kernel

private theorem r_1017030 : RangeOk getRow 2051521 1017030 1017099 := by
  decide +kernel

private theorem r_1017099 : RangeOk getRow 2051521 1017099 1017169 := by
  decide +kernel

private theorem r_1017169 : RangeOk getRow 2051521 1017169 1017239 := by
  decide +kernel

private theorem r_1017239 : RangeOk getRow 2051521 1017239 1017308 := by
  decide +kernel

private theorem r_1017308 : RangeOk getRow 2051521 1017308 1017378 := by
  decide +kernel

private theorem r_1017378 : RangeOk getRow 2051521 1017378 1017450 := by
  decide +kernel

private theorem r_1017450 : RangeOk getRow 2051521 1017450 1017519 := by
  decide +kernel

private theorem r_1017519 : RangeOk getRow 2051521 1017519 1017585 := by
  decide +kernel

private theorem r_1017585 : RangeOk getRow 2051521 1017585 1017650 := by
  decide +kernel

private theorem r_1017650 : RangeOk getRow 2051521 1017650 1017717 := by
  decide +kernel

private theorem r_1017717 : RangeOk getRow 2051521 1017717 1017786 := by
  decide +kernel

private theorem r_1017786 : RangeOk getRow 2051521 1017786 1017856 := by
  decide +kernel

private theorem r_1017856 : RangeOk getRow 2051521 1017856 1017926 := by
  decide +kernel

private theorem r_1017926 : RangeOk getRow 2051521 1017926 1017995 := by
  decide +kernel

private theorem r_1017995 : RangeOk getRow 2051521 1017995 1018065 := by
  decide +kernel

private theorem r_1018065 : RangeOk getRow 2051521 1018065 1018135 := by
  decide +kernel

private theorem r_1018135 : RangeOk getRow 2051521 1018135 1018209 := by
  decide +kernel

private theorem r_1018209 : RangeOk getRow 2051521 1018209 1018281 := by
  decide +kernel

private theorem r_1018281 : RangeOk getRow 2051521 1018281 1018351 := by
  decide +kernel

private theorem r_1018351 : RangeOk getRow 2051521 1018351 1018421 := by
  decide +kernel

private theorem r_1018421 : RangeOk getRow 2051521 1018421 1018492 := by
  decide +kernel

private theorem s_1015782 : RangeOk getRow 2051521 1015713 1015782 := r_1015713
private theorem s_1015852 : RangeOk getRow 2051521 1015713 1015852 :=
  s_1015782.append (by norm_num) r_1015782
private theorem s_1015925 : RangeOk getRow 2051521 1015713 1015925 :=
  s_1015852.append (by norm_num) r_1015852
private theorem s_1015996 : RangeOk getRow 2051521 1015713 1015996 :=
  s_1015925.append (by norm_num) r_1015925
private theorem s_1016065 : RangeOk getRow 2051521 1015713 1016065 :=
  s_1015996.append (by norm_num) r_1015996
private theorem s_1016135 : RangeOk getRow 2051521 1015713 1016135 :=
  s_1016065.append (by norm_num) r_1016065
private theorem s_1016205 : RangeOk getRow 2051521 1015713 1016205 :=
  s_1016135.append (by norm_num) r_1016135
private theorem s_1016275 : RangeOk getRow 2051521 1015713 1016275 :=
  s_1016205.append (by norm_num) r_1016205
private theorem s_1016346 : RangeOk getRow 2051521 1015713 1016346 :=
  s_1016275.append (by norm_num) r_1016275
private theorem s_1016414 : RangeOk getRow 2051521 1015713 1016414 :=
  s_1016346.append (by norm_num) r_1016346
private theorem s_1016480 : RangeOk getRow 2051521 1015713 1016480 :=
  s_1016414.append (by norm_num) r_1016414
private theorem s_1016544 : RangeOk getRow 2051521 1015713 1016544 :=
  s_1016480.append (by norm_num) r_1016480
private theorem s_1016609 : RangeOk getRow 2051521 1015713 1016609 :=
  s_1016544.append (by norm_num) r_1016544
private theorem s_1016679 : RangeOk getRow 2051521 1015713 1016679 :=
  s_1016609.append (by norm_num) r_1016609
private theorem s_1016750 : RangeOk getRow 2051521 1015713 1016750 :=
  s_1016679.append (by norm_num) r_1016679
private theorem s_1016819 : RangeOk getRow 2051521 1015713 1016819 :=
  s_1016750.append (by norm_num) r_1016750
private theorem s_1016888 : RangeOk getRow 2051521 1015713 1016888 :=
  s_1016819.append (by norm_num) r_1016819
private theorem s_1016959 : RangeOk getRow 2051521 1015713 1016959 :=
  s_1016888.append (by norm_num) r_1016888
private theorem s_1017030 : RangeOk getRow 2051521 1015713 1017030 :=
  s_1016959.append (by norm_num) r_1016959
private theorem s_1017099 : RangeOk getRow 2051521 1015713 1017099 :=
  s_1017030.append (by norm_num) r_1017030
private theorem s_1017169 : RangeOk getRow 2051521 1015713 1017169 :=
  s_1017099.append (by norm_num) r_1017099
private theorem s_1017239 : RangeOk getRow 2051521 1015713 1017239 :=
  s_1017169.append (by norm_num) r_1017169
private theorem s_1017308 : RangeOk getRow 2051521 1015713 1017308 :=
  s_1017239.append (by norm_num) r_1017239
private theorem s_1017378 : RangeOk getRow 2051521 1015713 1017378 :=
  s_1017308.append (by norm_num) r_1017308
private theorem s_1017450 : RangeOk getRow 2051521 1015713 1017450 :=
  s_1017378.append (by norm_num) r_1017378
private theorem s_1017519 : RangeOk getRow 2051521 1015713 1017519 :=
  s_1017450.append (by norm_num) r_1017450
private theorem s_1017585 : RangeOk getRow 2051521 1015713 1017585 :=
  s_1017519.append (by norm_num) r_1017519
private theorem s_1017650 : RangeOk getRow 2051521 1015713 1017650 :=
  s_1017585.append (by norm_num) r_1017585
private theorem s_1017717 : RangeOk getRow 2051521 1015713 1017717 :=
  s_1017650.append (by norm_num) r_1017650
private theorem s_1017786 : RangeOk getRow 2051521 1015713 1017786 :=
  s_1017717.append (by norm_num) r_1017717
private theorem s_1017856 : RangeOk getRow 2051521 1015713 1017856 :=
  s_1017786.append (by norm_num) r_1017786
private theorem s_1017926 : RangeOk getRow 2051521 1015713 1017926 :=
  s_1017856.append (by norm_num) r_1017856
private theorem s_1017995 : RangeOk getRow 2051521 1015713 1017995 :=
  s_1017926.append (by norm_num) r_1017926
private theorem s_1018065 : RangeOk getRow 2051521 1015713 1018065 :=
  s_1017995.append (by norm_num) r_1017995
private theorem s_1018135 : RangeOk getRow 2051521 1015713 1018135 :=
  s_1018065.append (by norm_num) r_1018065
private theorem s_1018209 : RangeOk getRow 2051521 1015713 1018209 :=
  s_1018135.append (by norm_num) r_1018135
private theorem s_1018281 : RangeOk getRow 2051521 1015713 1018281 :=
  s_1018209.append (by norm_num) r_1018209
private theorem s_1018351 : RangeOk getRow 2051521 1015713 1018351 :=
  s_1018281.append (by norm_num) r_1018281
private theorem s_1018421 : RangeOk getRow 2051521 1015713 1018421 :=
  s_1018351.append (by norm_num) r_1018351
private theorem s_1018492 : RangeOk getRow 2051521 1015713 1018492 :=
  s_1018421.append (by norm_num) r_1018421

/-- Rows `[1015713, 1018492)` are valid. -/
theorem rangeOk_1015713_1018492 : RangeOk getRow 2051521 1015713 1018492 := s_1018492

end Noperthedron.Solution
