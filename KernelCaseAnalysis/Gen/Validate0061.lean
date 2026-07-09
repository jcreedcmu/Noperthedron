import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[135492, 137220). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_135492 : RangeOk getRow 2051521 135492 135556 := by
  decide +kernel

private theorem r_135556 : RangeOk getRow 2051521 135556 135620 := by
  decide +kernel

private theorem r_135620 : RangeOk getRow 2051521 135620 135684 := by
  decide +kernel

private theorem r_135684 : RangeOk getRow 2051521 135684 135748 := by
  decide +kernel

private theorem r_135748 : RangeOk getRow 2051521 135748 135812 := by
  decide +kernel

private theorem r_135812 : RangeOk getRow 2051521 135812 135876 := by
  decide +kernel

private theorem r_135876 : RangeOk getRow 2051521 135876 135940 := by
  decide +kernel

private theorem r_135940 : RangeOk getRow 2051521 135940 136004 := by
  decide +kernel

private theorem r_136004 : RangeOk getRow 2051521 136004 136068 := by
  decide +kernel

private theorem r_136068 : RangeOk getRow 2051521 136068 136132 := by
  decide +kernel

private theorem r_136132 : RangeOk getRow 2051521 136132 136196 := by
  decide +kernel

private theorem r_136196 : RangeOk getRow 2051521 136196 136260 := by
  decide +kernel

private theorem r_136260 : RangeOk getRow 2051521 136260 136324 := by
  decide +kernel

private theorem r_136324 : RangeOk getRow 2051521 136324 136388 := by
  decide +kernel

private theorem r_136388 : RangeOk getRow 2051521 136388 136452 := by
  decide +kernel

private theorem r_136452 : RangeOk getRow 2051521 136452 136516 := by
  decide +kernel

private theorem r_136516 : RangeOk getRow 2051521 136516 136580 := by
  decide +kernel

private theorem r_136580 : RangeOk getRow 2051521 136580 136644 := by
  decide +kernel

private theorem r_136644 : RangeOk getRow 2051521 136644 136708 := by
  decide +kernel

private theorem r_136708 : RangeOk getRow 2051521 136708 136772 := by
  decide +kernel

private theorem r_136772 : RangeOk getRow 2051521 136772 136836 := by
  decide +kernel

private theorem r_136836 : RangeOk getRow 2051521 136836 136900 := by
  decide +kernel

private theorem r_136900 : RangeOk getRow 2051521 136900 136964 := by
  decide +kernel

private theorem r_136964 : RangeOk getRow 2051521 136964 137028 := by
  decide +kernel

private theorem r_137028 : RangeOk getRow 2051521 137028 137092 := by
  decide +kernel

private theorem r_137092 : RangeOk getRow 2051521 137092 137156 := by
  decide +kernel

private theorem r_137156 : RangeOk getRow 2051521 137156 137220 := by
  decide +kernel

private theorem s_135556 : RangeOk getRow 2051521 135492 135556 := r_135492
private theorem s_135620 : RangeOk getRow 2051521 135492 135620 :=
  s_135556.append (by norm_num) r_135556
private theorem s_135684 : RangeOk getRow 2051521 135492 135684 :=
  s_135620.append (by norm_num) r_135620
private theorem s_135748 : RangeOk getRow 2051521 135492 135748 :=
  s_135684.append (by norm_num) r_135684
private theorem s_135812 : RangeOk getRow 2051521 135492 135812 :=
  s_135748.append (by norm_num) r_135748
private theorem s_135876 : RangeOk getRow 2051521 135492 135876 :=
  s_135812.append (by norm_num) r_135812
private theorem s_135940 : RangeOk getRow 2051521 135492 135940 :=
  s_135876.append (by norm_num) r_135876
private theorem s_136004 : RangeOk getRow 2051521 135492 136004 :=
  s_135940.append (by norm_num) r_135940
private theorem s_136068 : RangeOk getRow 2051521 135492 136068 :=
  s_136004.append (by norm_num) r_136004
private theorem s_136132 : RangeOk getRow 2051521 135492 136132 :=
  s_136068.append (by norm_num) r_136068
private theorem s_136196 : RangeOk getRow 2051521 135492 136196 :=
  s_136132.append (by norm_num) r_136132
private theorem s_136260 : RangeOk getRow 2051521 135492 136260 :=
  s_136196.append (by norm_num) r_136196
private theorem s_136324 : RangeOk getRow 2051521 135492 136324 :=
  s_136260.append (by norm_num) r_136260
private theorem s_136388 : RangeOk getRow 2051521 135492 136388 :=
  s_136324.append (by norm_num) r_136324
private theorem s_136452 : RangeOk getRow 2051521 135492 136452 :=
  s_136388.append (by norm_num) r_136388
private theorem s_136516 : RangeOk getRow 2051521 135492 136516 :=
  s_136452.append (by norm_num) r_136452
private theorem s_136580 : RangeOk getRow 2051521 135492 136580 :=
  s_136516.append (by norm_num) r_136516
private theorem s_136644 : RangeOk getRow 2051521 135492 136644 :=
  s_136580.append (by norm_num) r_136580
private theorem s_136708 : RangeOk getRow 2051521 135492 136708 :=
  s_136644.append (by norm_num) r_136644
private theorem s_136772 : RangeOk getRow 2051521 135492 136772 :=
  s_136708.append (by norm_num) r_136708
private theorem s_136836 : RangeOk getRow 2051521 135492 136836 :=
  s_136772.append (by norm_num) r_136772
private theorem s_136900 : RangeOk getRow 2051521 135492 136900 :=
  s_136836.append (by norm_num) r_136836
private theorem s_136964 : RangeOk getRow 2051521 135492 136964 :=
  s_136900.append (by norm_num) r_136900
private theorem s_137028 : RangeOk getRow 2051521 135492 137028 :=
  s_136964.append (by norm_num) r_136964
private theorem s_137092 : RangeOk getRow 2051521 135492 137092 :=
  s_137028.append (by norm_num) r_137028
private theorem s_137156 : RangeOk getRow 2051521 135492 137156 :=
  s_137092.append (by norm_num) r_137092
private theorem s_137220 : RangeOk getRow 2051521 135492 137220 :=
  s_137156.append (by norm_num) r_137156

/-- Rows `[135492, 137220)` are valid. -/
theorem rangeOk_135492_137220 : RangeOk getRow 2051521 135492 137220 := s_137220

end Noperthedron.Solution
