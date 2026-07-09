import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[597846, 600140). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_597846 : RangeOk getRow 2051521 597846 597914 := by
  decide +kernel

private theorem r_597914 : RangeOk getRow 2051521 597914 597982 := by
  decide +kernel

private theorem r_597982 : RangeOk getRow 2051521 597982 598049 := by
  decide +kernel

private theorem r_598049 : RangeOk getRow 2051521 598049 598118 := by
  decide +kernel

private theorem r_598118 : RangeOk getRow 2051521 598118 598186 := by
  decide +kernel

private theorem r_598186 : RangeOk getRow 2051521 598186 598252 := by
  decide +kernel

private theorem r_598252 : RangeOk getRow 2051521 598252 598317 := by
  decide +kernel

private theorem r_598317 : RangeOk getRow 2051521 598317 598385 := by
  decide +kernel

private theorem r_598385 : RangeOk getRow 2051521 598385 598453 := by
  decide +kernel

private theorem r_598453 : RangeOk getRow 2051521 598453 598522 := by
  decide +kernel

private theorem r_598522 : RangeOk getRow 2051521 598522 598590 := by
  decide +kernel

private theorem r_598590 : RangeOk getRow 2051521 598590 598658 := by
  decide +kernel

private theorem r_598658 : RangeOk getRow 2051521 598658 598725 := by
  decide +kernel

private theorem r_598725 : RangeOk getRow 2051521 598725 598794 := by
  decide +kernel

private theorem r_598794 : RangeOk getRow 2051521 598794 598861 := by
  decide +kernel

private theorem r_598861 : RangeOk getRow 2051521 598861 598926 := by
  decide +kernel

private theorem r_598926 : RangeOk getRow 2051521 598926 598993 := by
  decide +kernel

private theorem r_598993 : RangeOk getRow 2051521 598993 599061 := by
  decide +kernel

private theorem r_599061 : RangeOk getRow 2051521 599061 599129 := by
  decide +kernel

private theorem r_599129 : RangeOk getRow 2051521 599129 599196 := by
  decide +kernel

private theorem r_599196 : RangeOk getRow 2051521 599196 599264 := by
  decide +kernel

private theorem r_599264 : RangeOk getRow 2051521 599264 599333 := by
  decide +kernel

private theorem r_599333 : RangeOk getRow 2051521 599333 599400 := by
  decide +kernel

private theorem r_599400 : RangeOk getRow 2051521 599400 599465 := by
  decide +kernel

private theorem r_599465 : RangeOk getRow 2051521 599465 599533 := by
  decide +kernel

private theorem r_599533 : RangeOk getRow 2051521 599533 599601 := by
  decide +kernel

private theorem r_599601 : RangeOk getRow 2051521 599601 599670 := by
  decide +kernel

private theorem r_599670 : RangeOk getRow 2051521 599670 599738 := by
  decide +kernel

private theorem r_599738 : RangeOk getRow 2051521 599738 599805 := by
  decide +kernel

private theorem r_599805 : RangeOk getRow 2051521 599805 599871 := by
  decide +kernel

private theorem r_599871 : RangeOk getRow 2051521 599871 599937 := by
  decide +kernel

private theorem r_599937 : RangeOk getRow 2051521 599937 600006 := by
  decide +kernel

private theorem r_600006 : RangeOk getRow 2051521 600006 600073 := by
  decide +kernel

private theorem r_600073 : RangeOk getRow 2051521 600073 600140 := by
  decide +kernel

private theorem s_597914 : RangeOk getRow 2051521 597846 597914 := r_597846
private theorem s_597982 : RangeOk getRow 2051521 597846 597982 :=
  s_597914.append (by norm_num) r_597914
private theorem s_598049 : RangeOk getRow 2051521 597846 598049 :=
  s_597982.append (by norm_num) r_597982
private theorem s_598118 : RangeOk getRow 2051521 597846 598118 :=
  s_598049.append (by norm_num) r_598049
private theorem s_598186 : RangeOk getRow 2051521 597846 598186 :=
  s_598118.append (by norm_num) r_598118
private theorem s_598252 : RangeOk getRow 2051521 597846 598252 :=
  s_598186.append (by norm_num) r_598186
private theorem s_598317 : RangeOk getRow 2051521 597846 598317 :=
  s_598252.append (by norm_num) r_598252
private theorem s_598385 : RangeOk getRow 2051521 597846 598385 :=
  s_598317.append (by norm_num) r_598317
private theorem s_598453 : RangeOk getRow 2051521 597846 598453 :=
  s_598385.append (by norm_num) r_598385
private theorem s_598522 : RangeOk getRow 2051521 597846 598522 :=
  s_598453.append (by norm_num) r_598453
private theorem s_598590 : RangeOk getRow 2051521 597846 598590 :=
  s_598522.append (by norm_num) r_598522
private theorem s_598658 : RangeOk getRow 2051521 597846 598658 :=
  s_598590.append (by norm_num) r_598590
private theorem s_598725 : RangeOk getRow 2051521 597846 598725 :=
  s_598658.append (by norm_num) r_598658
private theorem s_598794 : RangeOk getRow 2051521 597846 598794 :=
  s_598725.append (by norm_num) r_598725
private theorem s_598861 : RangeOk getRow 2051521 597846 598861 :=
  s_598794.append (by norm_num) r_598794
private theorem s_598926 : RangeOk getRow 2051521 597846 598926 :=
  s_598861.append (by norm_num) r_598861
private theorem s_598993 : RangeOk getRow 2051521 597846 598993 :=
  s_598926.append (by norm_num) r_598926
private theorem s_599061 : RangeOk getRow 2051521 597846 599061 :=
  s_598993.append (by norm_num) r_598993
private theorem s_599129 : RangeOk getRow 2051521 597846 599129 :=
  s_599061.append (by norm_num) r_599061
private theorem s_599196 : RangeOk getRow 2051521 597846 599196 :=
  s_599129.append (by norm_num) r_599129
private theorem s_599264 : RangeOk getRow 2051521 597846 599264 :=
  s_599196.append (by norm_num) r_599196
private theorem s_599333 : RangeOk getRow 2051521 597846 599333 :=
  s_599264.append (by norm_num) r_599264
private theorem s_599400 : RangeOk getRow 2051521 597846 599400 :=
  s_599333.append (by norm_num) r_599333
private theorem s_599465 : RangeOk getRow 2051521 597846 599465 :=
  s_599400.append (by norm_num) r_599400
private theorem s_599533 : RangeOk getRow 2051521 597846 599533 :=
  s_599465.append (by norm_num) r_599465
private theorem s_599601 : RangeOk getRow 2051521 597846 599601 :=
  s_599533.append (by norm_num) r_599533
private theorem s_599670 : RangeOk getRow 2051521 597846 599670 :=
  s_599601.append (by norm_num) r_599601
private theorem s_599738 : RangeOk getRow 2051521 597846 599738 :=
  s_599670.append (by norm_num) r_599670
private theorem s_599805 : RangeOk getRow 2051521 597846 599805 :=
  s_599738.append (by norm_num) r_599738
private theorem s_599871 : RangeOk getRow 2051521 597846 599871 :=
  s_599805.append (by norm_num) r_599805
private theorem s_599937 : RangeOk getRow 2051521 597846 599937 :=
  s_599871.append (by norm_num) r_599871
private theorem s_600006 : RangeOk getRow 2051521 597846 600006 :=
  s_599937.append (by norm_num) r_599937
private theorem s_600073 : RangeOk getRow 2051521 597846 600073 :=
  s_600006.append (by norm_num) r_600006
private theorem s_600140 : RangeOk getRow 2051521 597846 600140 :=
  s_600073.append (by norm_num) r_600073

/-- Rows `[597846, 600140)` are valid. -/
theorem rangeOk_597846_600140 : RangeOk getRow 2051521 597846 600140 := s_600140

end Noperthedron.Solution
