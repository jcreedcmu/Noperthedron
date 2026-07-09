import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[93505, 95223). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_93505 : RangeOk getRow 2051521 93505 93569 := by
  decide +kernel

private theorem r_93569 : RangeOk getRow 2051521 93569 93634 := by
  decide +kernel

private theorem r_93634 : RangeOk getRow 2051521 93634 93689 := by
  decide +kernel

private theorem r_93689 : RangeOk getRow 2051521 93689 93753 := by
  decide +kernel

private theorem r_93753 : RangeOk getRow 2051521 93753 93817 := by
  decide +kernel

private theorem r_93817 : RangeOk getRow 2051521 93817 93881 := by
  decide +kernel

private theorem r_93881 : RangeOk getRow 2051521 93881 93945 := by
  decide +kernel

private theorem r_93945 : RangeOk getRow 2051521 93945 94009 := by
  decide +kernel

private theorem r_94009 : RangeOk getRow 2051521 94009 94073 := by
  decide +kernel

private theorem r_94073 : RangeOk getRow 2051521 94073 94133 := by
  decide +kernel

private theorem r_94133 : RangeOk getRow 2051521 94133 94197 := by
  decide +kernel

private theorem r_94197 : RangeOk getRow 2051521 94197 94261 := by
  decide +kernel

private theorem r_94261 : RangeOk getRow 2051521 94261 94325 := by
  decide +kernel

private theorem r_94325 : RangeOk getRow 2051521 94325 94389 := by
  decide +kernel

private theorem r_94389 : RangeOk getRow 2051521 94389 94453 := by
  decide +kernel

private theorem r_94453 : RangeOk getRow 2051521 94453 94517 := by
  decide +kernel

private theorem r_94517 : RangeOk getRow 2051521 94517 94582 := by
  decide +kernel

private theorem r_94582 : RangeOk getRow 2051521 94582 94646 := by
  decide +kernel

private theorem r_94646 : RangeOk getRow 2051521 94646 94710 := by
  decide +kernel

private theorem r_94710 : RangeOk getRow 2051521 94710 94774 := by
  decide +kernel

private theorem r_94774 : RangeOk getRow 2051521 94774 94838 := by
  decide +kernel

private theorem r_94838 : RangeOk getRow 2051521 94838 94902 := by
  decide +kernel

private theorem r_94902 : RangeOk getRow 2051521 94902 94966 := by
  decide +kernel

private theorem r_94966 : RangeOk getRow 2051521 94966 95031 := by
  decide +kernel

private theorem r_95031 : RangeOk getRow 2051521 95031 95095 := by
  decide +kernel

private theorem r_95095 : RangeOk getRow 2051521 95095 95159 := by
  decide +kernel

private theorem r_95159 : RangeOk getRow 2051521 95159 95223 := by
  decide +kernel

private theorem s_93569 : RangeOk getRow 2051521 93505 93569 := r_93505
private theorem s_93634 : RangeOk getRow 2051521 93505 93634 :=
  s_93569.append (by norm_num) r_93569
private theorem s_93689 : RangeOk getRow 2051521 93505 93689 :=
  s_93634.append (by norm_num) r_93634
private theorem s_93753 : RangeOk getRow 2051521 93505 93753 :=
  s_93689.append (by norm_num) r_93689
private theorem s_93817 : RangeOk getRow 2051521 93505 93817 :=
  s_93753.append (by norm_num) r_93753
private theorem s_93881 : RangeOk getRow 2051521 93505 93881 :=
  s_93817.append (by norm_num) r_93817
private theorem s_93945 : RangeOk getRow 2051521 93505 93945 :=
  s_93881.append (by norm_num) r_93881
private theorem s_94009 : RangeOk getRow 2051521 93505 94009 :=
  s_93945.append (by norm_num) r_93945
private theorem s_94073 : RangeOk getRow 2051521 93505 94073 :=
  s_94009.append (by norm_num) r_94009
private theorem s_94133 : RangeOk getRow 2051521 93505 94133 :=
  s_94073.append (by norm_num) r_94073
private theorem s_94197 : RangeOk getRow 2051521 93505 94197 :=
  s_94133.append (by norm_num) r_94133
private theorem s_94261 : RangeOk getRow 2051521 93505 94261 :=
  s_94197.append (by norm_num) r_94197
private theorem s_94325 : RangeOk getRow 2051521 93505 94325 :=
  s_94261.append (by norm_num) r_94261
private theorem s_94389 : RangeOk getRow 2051521 93505 94389 :=
  s_94325.append (by norm_num) r_94325
private theorem s_94453 : RangeOk getRow 2051521 93505 94453 :=
  s_94389.append (by norm_num) r_94389
private theorem s_94517 : RangeOk getRow 2051521 93505 94517 :=
  s_94453.append (by norm_num) r_94453
private theorem s_94582 : RangeOk getRow 2051521 93505 94582 :=
  s_94517.append (by norm_num) r_94517
private theorem s_94646 : RangeOk getRow 2051521 93505 94646 :=
  s_94582.append (by norm_num) r_94582
private theorem s_94710 : RangeOk getRow 2051521 93505 94710 :=
  s_94646.append (by norm_num) r_94646
private theorem s_94774 : RangeOk getRow 2051521 93505 94774 :=
  s_94710.append (by norm_num) r_94710
private theorem s_94838 : RangeOk getRow 2051521 93505 94838 :=
  s_94774.append (by norm_num) r_94774
private theorem s_94902 : RangeOk getRow 2051521 93505 94902 :=
  s_94838.append (by norm_num) r_94838
private theorem s_94966 : RangeOk getRow 2051521 93505 94966 :=
  s_94902.append (by norm_num) r_94902
private theorem s_95031 : RangeOk getRow 2051521 93505 95031 :=
  s_94966.append (by norm_num) r_94966
private theorem s_95095 : RangeOk getRow 2051521 93505 95095 :=
  s_95031.append (by norm_num) r_95031
private theorem s_95159 : RangeOk getRow 2051521 93505 95159 :=
  s_95095.append (by norm_num) r_95095
private theorem s_95223 : RangeOk getRow 2051521 93505 95223 :=
  s_95159.append (by norm_num) r_95159

/-- Rows `[93505, 95223)` are valid. -/
theorem rangeOk_93505_95223 : RangeOk getRow 2051521 93505 95223 := s_95223

end Noperthedron.Solution
