import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[29069, 30800). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_29069 : RangeOk getRow 2051521 29069 29133 := by
  decide +kernel

private theorem r_29133 : RangeOk getRow 2051521 29133 29197 := by
  decide +kernel

private theorem r_29197 : RangeOk getRow 2051521 29197 29261 := by
  decide +kernel

private theorem r_29261 : RangeOk getRow 2051521 29261 29325 := by
  decide +kernel

private theorem r_29325 : RangeOk getRow 2051521 29325 29389 := by
  decide +kernel

private theorem r_29389 : RangeOk getRow 2051521 29389 29453 := by
  decide +kernel

private theorem r_29453 : RangeOk getRow 2051521 29453 29517 := by
  decide +kernel

private theorem r_29517 : RangeOk getRow 2051521 29517 29581 := by
  decide +kernel

private theorem r_29581 : RangeOk getRow 2051521 29581 29645 := by
  decide +kernel

private theorem r_29645 : RangeOk getRow 2051521 29645 29709 := by
  decide +kernel

private theorem r_29709 : RangeOk getRow 2051521 29709 29773 := by
  decide +kernel

private theorem r_29773 : RangeOk getRow 2051521 29773 29837 := by
  decide +kernel

private theorem r_29837 : RangeOk getRow 2051521 29837 29901 := by
  decide +kernel

private theorem r_29901 : RangeOk getRow 2051521 29901 29965 := by
  decide +kernel

private theorem r_29965 : RangeOk getRow 2051521 29965 30030 := by
  decide +kernel

private theorem r_30030 : RangeOk getRow 2051521 30030 30094 := by
  decide +kernel

private theorem r_30094 : RangeOk getRow 2051521 30094 30158 := by
  decide +kernel

private theorem r_30158 : RangeOk getRow 2051521 30158 30223 := by
  decide +kernel

private theorem r_30223 : RangeOk getRow 2051521 30223 30287 := by
  decide +kernel

private theorem r_30287 : RangeOk getRow 2051521 30287 30351 := by
  decide +kernel

private theorem r_30351 : RangeOk getRow 2051521 30351 30415 := by
  decide +kernel

private theorem r_30415 : RangeOk getRow 2051521 30415 30479 := by
  decide +kernel

private theorem r_30479 : RangeOk getRow 2051521 30479 30543 := by
  decide +kernel

private theorem r_30543 : RangeOk getRow 2051521 30543 30608 := by
  decide +kernel

private theorem r_30608 : RangeOk getRow 2051521 30608 30672 := by
  decide +kernel

private theorem r_30672 : RangeOk getRow 2051521 30672 30736 := by
  decide +kernel

private theorem r_30736 : RangeOk getRow 2051521 30736 30800 := by
  decide +kernel

private theorem s_29133 : RangeOk getRow 2051521 29069 29133 := r_29069
private theorem s_29197 : RangeOk getRow 2051521 29069 29197 :=
  s_29133.append (by norm_num) r_29133
private theorem s_29261 : RangeOk getRow 2051521 29069 29261 :=
  s_29197.append (by norm_num) r_29197
private theorem s_29325 : RangeOk getRow 2051521 29069 29325 :=
  s_29261.append (by norm_num) r_29261
private theorem s_29389 : RangeOk getRow 2051521 29069 29389 :=
  s_29325.append (by norm_num) r_29325
private theorem s_29453 : RangeOk getRow 2051521 29069 29453 :=
  s_29389.append (by norm_num) r_29389
private theorem s_29517 : RangeOk getRow 2051521 29069 29517 :=
  s_29453.append (by norm_num) r_29453
private theorem s_29581 : RangeOk getRow 2051521 29069 29581 :=
  s_29517.append (by norm_num) r_29517
private theorem s_29645 : RangeOk getRow 2051521 29069 29645 :=
  s_29581.append (by norm_num) r_29581
private theorem s_29709 : RangeOk getRow 2051521 29069 29709 :=
  s_29645.append (by norm_num) r_29645
private theorem s_29773 : RangeOk getRow 2051521 29069 29773 :=
  s_29709.append (by norm_num) r_29709
private theorem s_29837 : RangeOk getRow 2051521 29069 29837 :=
  s_29773.append (by norm_num) r_29773
private theorem s_29901 : RangeOk getRow 2051521 29069 29901 :=
  s_29837.append (by norm_num) r_29837
private theorem s_29965 : RangeOk getRow 2051521 29069 29965 :=
  s_29901.append (by norm_num) r_29901
private theorem s_30030 : RangeOk getRow 2051521 29069 30030 :=
  s_29965.append (by norm_num) r_29965
private theorem s_30094 : RangeOk getRow 2051521 29069 30094 :=
  s_30030.append (by norm_num) r_30030
private theorem s_30158 : RangeOk getRow 2051521 29069 30158 :=
  s_30094.append (by norm_num) r_30094
private theorem s_30223 : RangeOk getRow 2051521 29069 30223 :=
  s_30158.append (by norm_num) r_30158
private theorem s_30287 : RangeOk getRow 2051521 29069 30287 :=
  s_30223.append (by norm_num) r_30223
private theorem s_30351 : RangeOk getRow 2051521 29069 30351 :=
  s_30287.append (by norm_num) r_30287
private theorem s_30415 : RangeOk getRow 2051521 29069 30415 :=
  s_30351.append (by norm_num) r_30351
private theorem s_30479 : RangeOk getRow 2051521 29069 30479 :=
  s_30415.append (by norm_num) r_30415
private theorem s_30543 : RangeOk getRow 2051521 29069 30543 :=
  s_30479.append (by norm_num) r_30479
private theorem s_30608 : RangeOk getRow 2051521 29069 30608 :=
  s_30543.append (by norm_num) r_30543
private theorem s_30672 : RangeOk getRow 2051521 29069 30672 :=
  s_30608.append (by norm_num) r_30608
private theorem s_30736 : RangeOk getRow 2051521 29069 30736 :=
  s_30672.append (by norm_num) r_30672
private theorem s_30800 : RangeOk getRow 2051521 29069 30800 :=
  s_30736.append (by norm_num) r_30736

/-- Rows `[29069, 30800)` are valid. -/
theorem rangeOk_29069_30800 : RangeOk getRow 2051521 29069 30800 := s_30800

end Noperthedron.Solution
