import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[37786, 39514). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_37786 : RangeOk getRow 2051521 37786 37850 := by
  decide +kernel

private theorem r_37850 : RangeOk getRow 2051521 37850 37914 := by
  decide +kernel

private theorem r_37914 : RangeOk getRow 2051521 37914 37978 := by
  decide +kernel

private theorem r_37978 : RangeOk getRow 2051521 37978 38042 := by
  decide +kernel

private theorem r_38042 : RangeOk getRow 2051521 38042 38106 := by
  decide +kernel

private theorem r_38106 : RangeOk getRow 2051521 38106 38170 := by
  decide +kernel

private theorem r_38170 : RangeOk getRow 2051521 38170 38234 := by
  decide +kernel

private theorem r_38234 : RangeOk getRow 2051521 38234 38298 := by
  decide +kernel

private theorem r_38298 : RangeOk getRow 2051521 38298 38362 := by
  decide +kernel

private theorem r_38362 : RangeOk getRow 2051521 38362 38426 := by
  decide +kernel

private theorem r_38426 : RangeOk getRow 2051521 38426 38490 := by
  decide +kernel

private theorem r_38490 : RangeOk getRow 2051521 38490 38554 := by
  decide +kernel

private theorem r_38554 : RangeOk getRow 2051521 38554 38618 := by
  decide +kernel

private theorem r_38618 : RangeOk getRow 2051521 38618 38682 := by
  decide +kernel

private theorem r_38682 : RangeOk getRow 2051521 38682 38746 := by
  decide +kernel

private theorem r_38746 : RangeOk getRow 2051521 38746 38810 := by
  decide +kernel

private theorem r_38810 : RangeOk getRow 2051521 38810 38874 := by
  decide +kernel

private theorem r_38874 : RangeOk getRow 2051521 38874 38938 := by
  decide +kernel

private theorem r_38938 : RangeOk getRow 2051521 38938 39002 := by
  decide +kernel

private theorem r_39002 : RangeOk getRow 2051521 39002 39066 := by
  decide +kernel

private theorem r_39066 : RangeOk getRow 2051521 39066 39130 := by
  decide +kernel

private theorem r_39130 : RangeOk getRow 2051521 39130 39194 := by
  decide +kernel

private theorem r_39194 : RangeOk getRow 2051521 39194 39258 := by
  decide +kernel

private theorem r_39258 : RangeOk getRow 2051521 39258 39322 := by
  decide +kernel

private theorem r_39322 : RangeOk getRow 2051521 39322 39386 := by
  decide +kernel

private theorem r_39386 : RangeOk getRow 2051521 39386 39450 := by
  decide +kernel

private theorem r_39450 : RangeOk getRow 2051521 39450 39514 := by
  decide +kernel

private theorem s_37850 : RangeOk getRow 2051521 37786 37850 := r_37786
private theorem s_37914 : RangeOk getRow 2051521 37786 37914 :=
  s_37850.append (by norm_num) r_37850
private theorem s_37978 : RangeOk getRow 2051521 37786 37978 :=
  s_37914.append (by norm_num) r_37914
private theorem s_38042 : RangeOk getRow 2051521 37786 38042 :=
  s_37978.append (by norm_num) r_37978
private theorem s_38106 : RangeOk getRow 2051521 37786 38106 :=
  s_38042.append (by norm_num) r_38042
private theorem s_38170 : RangeOk getRow 2051521 37786 38170 :=
  s_38106.append (by norm_num) r_38106
private theorem s_38234 : RangeOk getRow 2051521 37786 38234 :=
  s_38170.append (by norm_num) r_38170
private theorem s_38298 : RangeOk getRow 2051521 37786 38298 :=
  s_38234.append (by norm_num) r_38234
private theorem s_38362 : RangeOk getRow 2051521 37786 38362 :=
  s_38298.append (by norm_num) r_38298
private theorem s_38426 : RangeOk getRow 2051521 37786 38426 :=
  s_38362.append (by norm_num) r_38362
private theorem s_38490 : RangeOk getRow 2051521 37786 38490 :=
  s_38426.append (by norm_num) r_38426
private theorem s_38554 : RangeOk getRow 2051521 37786 38554 :=
  s_38490.append (by norm_num) r_38490
private theorem s_38618 : RangeOk getRow 2051521 37786 38618 :=
  s_38554.append (by norm_num) r_38554
private theorem s_38682 : RangeOk getRow 2051521 37786 38682 :=
  s_38618.append (by norm_num) r_38618
private theorem s_38746 : RangeOk getRow 2051521 37786 38746 :=
  s_38682.append (by norm_num) r_38682
private theorem s_38810 : RangeOk getRow 2051521 37786 38810 :=
  s_38746.append (by norm_num) r_38746
private theorem s_38874 : RangeOk getRow 2051521 37786 38874 :=
  s_38810.append (by norm_num) r_38810
private theorem s_38938 : RangeOk getRow 2051521 37786 38938 :=
  s_38874.append (by norm_num) r_38874
private theorem s_39002 : RangeOk getRow 2051521 37786 39002 :=
  s_38938.append (by norm_num) r_38938
private theorem s_39066 : RangeOk getRow 2051521 37786 39066 :=
  s_39002.append (by norm_num) r_39002
private theorem s_39130 : RangeOk getRow 2051521 37786 39130 :=
  s_39066.append (by norm_num) r_39066
private theorem s_39194 : RangeOk getRow 2051521 37786 39194 :=
  s_39130.append (by norm_num) r_39130
private theorem s_39258 : RangeOk getRow 2051521 37786 39258 :=
  s_39194.append (by norm_num) r_39194
private theorem s_39322 : RangeOk getRow 2051521 37786 39322 :=
  s_39258.append (by norm_num) r_39258
private theorem s_39386 : RangeOk getRow 2051521 37786 39386 :=
  s_39322.append (by norm_num) r_39322
private theorem s_39450 : RangeOk getRow 2051521 37786 39450 :=
  s_39386.append (by norm_num) r_39386
private theorem s_39514 : RangeOk getRow 2051521 37786 39514 :=
  s_39450.append (by norm_num) r_39450

/-- Rows `[37786, 39514)` are valid. -/
theorem rangeOk_37786_39514 : RangeOk getRow 2051521 37786 39514 := s_39514

end Noperthedron.Solution
