import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[607089, 609304). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_607089 : RangeOk getRow 2051521 607089 607157 := by
  decide +kernel

private theorem r_607157 : RangeOk getRow 2051521 607157 607224 := by
  decide +kernel

private theorem r_607224 : RangeOk getRow 2051521 607224 607290 := by
  decide +kernel

private theorem r_607290 : RangeOk getRow 2051521 607290 607357 := by
  decide +kernel

private theorem r_607357 : RangeOk getRow 2051521 607357 607425 := by
  decide +kernel

private theorem r_607425 : RangeOk getRow 2051521 607425 607493 := by
  decide +kernel

private theorem r_607493 : RangeOk getRow 2051521 607493 607560 := by
  decide +kernel

private theorem r_607560 : RangeOk getRow 2051521 607560 607628 := by
  decide +kernel

private theorem r_607628 : RangeOk getRow 2051521 607628 607696 := by
  decide +kernel

private theorem r_607696 : RangeOk getRow 2051521 607696 607762 := by
  decide +kernel

private theorem r_607762 : RangeOk getRow 2051521 607762 607829 := by
  decide +kernel

private theorem r_607829 : RangeOk getRow 2051521 607829 607895 := by
  decide +kernel

private theorem r_607895 : RangeOk getRow 2051521 607895 607962 := by
  decide +kernel

private theorem r_607962 : RangeOk getRow 2051521 607962 608030 := by
  decide +kernel

private theorem r_608030 : RangeOk getRow 2051521 608030 608099 := by
  decide +kernel

private theorem r_608099 : RangeOk getRow 2051521 608099 608166 := by
  decide +kernel

private theorem r_608166 : RangeOk getRow 2051521 608166 608232 := by
  decide +kernel

private theorem r_608232 : RangeOk getRow 2051521 608232 608298 := by
  decide +kernel

private theorem r_608298 : RangeOk getRow 2051521 608298 608362 := by
  decide +kernel

private theorem r_608362 : RangeOk getRow 2051521 608362 608428 := by
  decide +kernel

private theorem r_608428 : RangeOk getRow 2051521 608428 608495 := by
  decide +kernel

private theorem r_608495 : RangeOk getRow 2051521 608495 608564 := by
  decide +kernel

private theorem r_608564 : RangeOk getRow 2051521 608564 608631 := by
  decide +kernel

private theorem r_608631 : RangeOk getRow 2051521 608631 608699 := by
  decide +kernel

private theorem r_608699 : RangeOk getRow 2051521 608699 608767 := by
  decide +kernel

private theorem r_608767 : RangeOk getRow 2051521 608767 608834 := by
  decide +kernel

private theorem r_608834 : RangeOk getRow 2051521 608834 608901 := by
  decide +kernel

private theorem r_608901 : RangeOk getRow 2051521 608901 608967 := by
  decide +kernel

private theorem r_608967 : RangeOk getRow 2051521 608967 609033 := by
  decide +kernel

private theorem r_609033 : RangeOk getRow 2051521 609033 609099 := by
  decide +kernel

private theorem r_609099 : RangeOk getRow 2051521 609099 609166 := by
  decide +kernel

private theorem r_609166 : RangeOk getRow 2051521 609166 609235 := by
  decide +kernel

private theorem r_609235 : RangeOk getRow 2051521 609235 609304 := by
  decide +kernel

private theorem s_607157 : RangeOk getRow 2051521 607089 607157 := r_607089
private theorem s_607224 : RangeOk getRow 2051521 607089 607224 :=
  s_607157.append (by norm_num) r_607157
private theorem s_607290 : RangeOk getRow 2051521 607089 607290 :=
  s_607224.append (by norm_num) r_607224
private theorem s_607357 : RangeOk getRow 2051521 607089 607357 :=
  s_607290.append (by norm_num) r_607290
private theorem s_607425 : RangeOk getRow 2051521 607089 607425 :=
  s_607357.append (by norm_num) r_607357
private theorem s_607493 : RangeOk getRow 2051521 607089 607493 :=
  s_607425.append (by norm_num) r_607425
private theorem s_607560 : RangeOk getRow 2051521 607089 607560 :=
  s_607493.append (by norm_num) r_607493
private theorem s_607628 : RangeOk getRow 2051521 607089 607628 :=
  s_607560.append (by norm_num) r_607560
private theorem s_607696 : RangeOk getRow 2051521 607089 607696 :=
  s_607628.append (by norm_num) r_607628
private theorem s_607762 : RangeOk getRow 2051521 607089 607762 :=
  s_607696.append (by norm_num) r_607696
private theorem s_607829 : RangeOk getRow 2051521 607089 607829 :=
  s_607762.append (by norm_num) r_607762
private theorem s_607895 : RangeOk getRow 2051521 607089 607895 :=
  s_607829.append (by norm_num) r_607829
private theorem s_607962 : RangeOk getRow 2051521 607089 607962 :=
  s_607895.append (by norm_num) r_607895
private theorem s_608030 : RangeOk getRow 2051521 607089 608030 :=
  s_607962.append (by norm_num) r_607962
private theorem s_608099 : RangeOk getRow 2051521 607089 608099 :=
  s_608030.append (by norm_num) r_608030
private theorem s_608166 : RangeOk getRow 2051521 607089 608166 :=
  s_608099.append (by norm_num) r_608099
private theorem s_608232 : RangeOk getRow 2051521 607089 608232 :=
  s_608166.append (by norm_num) r_608166
private theorem s_608298 : RangeOk getRow 2051521 607089 608298 :=
  s_608232.append (by norm_num) r_608232
private theorem s_608362 : RangeOk getRow 2051521 607089 608362 :=
  s_608298.append (by norm_num) r_608298
private theorem s_608428 : RangeOk getRow 2051521 607089 608428 :=
  s_608362.append (by norm_num) r_608362
private theorem s_608495 : RangeOk getRow 2051521 607089 608495 :=
  s_608428.append (by norm_num) r_608428
private theorem s_608564 : RangeOk getRow 2051521 607089 608564 :=
  s_608495.append (by norm_num) r_608495
private theorem s_608631 : RangeOk getRow 2051521 607089 608631 :=
  s_608564.append (by norm_num) r_608564
private theorem s_608699 : RangeOk getRow 2051521 607089 608699 :=
  s_608631.append (by norm_num) r_608631
private theorem s_608767 : RangeOk getRow 2051521 607089 608767 :=
  s_608699.append (by norm_num) r_608699
private theorem s_608834 : RangeOk getRow 2051521 607089 608834 :=
  s_608767.append (by norm_num) r_608767
private theorem s_608901 : RangeOk getRow 2051521 607089 608901 :=
  s_608834.append (by norm_num) r_608834
private theorem s_608967 : RangeOk getRow 2051521 607089 608967 :=
  s_608901.append (by norm_num) r_608901
private theorem s_609033 : RangeOk getRow 2051521 607089 609033 :=
  s_608967.append (by norm_num) r_608967
private theorem s_609099 : RangeOk getRow 2051521 607089 609099 :=
  s_609033.append (by norm_num) r_609033
private theorem s_609166 : RangeOk getRow 2051521 607089 609166 :=
  s_609099.append (by norm_num) r_609099
private theorem s_609235 : RangeOk getRow 2051521 607089 609235 :=
  s_609166.append (by norm_num) r_609166
private theorem s_609304 : RangeOk getRow 2051521 607089 609304 :=
  s_609235.append (by norm_num) r_609235

/-- Rows `[607089, 609304)` are valid. -/
theorem rangeOk_607089_609304 : RangeOk getRow 2051521 607089 609304 := s_609304

end Noperthedron.Solution
