import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[893518, 895886). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_893518 : RangeOk getRow 2051521 893518 893584 := by
  decide +kernel

private theorem r_893584 : RangeOk getRow 2051521 893584 893652 := by
  decide +kernel

private theorem r_893652 : RangeOk getRow 2051521 893652 893721 := by
  decide +kernel

private theorem r_893721 : RangeOk getRow 2051521 893721 893786 := by
  decide +kernel

private theorem r_893786 : RangeOk getRow 2051521 893786 893852 := by
  decide +kernel

private theorem r_893852 : RangeOk getRow 2051521 893852 893920 := by
  decide +kernel

private theorem r_893920 : RangeOk getRow 2051521 893920 893987 := by
  decide +kernel

private theorem r_893987 : RangeOk getRow 2051521 893987 894056 := by
  decide +kernel

private theorem r_894056 : RangeOk getRow 2051521 894056 894123 := by
  decide +kernel

private theorem r_894123 : RangeOk getRow 2051521 894123 894191 := by
  decide +kernel

private theorem r_894191 : RangeOk getRow 2051521 894191 894257 := by
  decide +kernel

private theorem r_894257 : RangeOk getRow 2051521 894257 894323 := by
  decide +kernel

private theorem r_894323 : RangeOk getRow 2051521 894323 894392 := by
  decide +kernel

private theorem r_894392 : RangeOk getRow 2051521 894392 894458 := by
  decide +kernel

private theorem r_894458 : RangeOk getRow 2051521 894458 894524 := by
  decide +kernel

private theorem r_894524 : RangeOk getRow 2051521 894524 894595 := by
  decide +kernel

private theorem r_894595 : RangeOk getRow 2051521 894595 894662 := by
  decide +kernel

private theorem r_894662 : RangeOk getRow 2051521 894662 894730 := by
  decide +kernel

private theorem r_894730 : RangeOk getRow 2051521 894730 894799 := by
  decide +kernel

private theorem r_894799 : RangeOk getRow 2051521 894799 894867 := by
  decide +kernel

private theorem r_894867 : RangeOk getRow 2051521 894867 894934 := by
  decide +kernel

private theorem r_894934 : RangeOk getRow 2051521 894934 895000 := by
  decide +kernel

private theorem r_895000 : RangeOk getRow 2051521 895000 895068 := by
  decide +kernel

private theorem r_895068 : RangeOk getRow 2051521 895068 895135 := by
  decide +kernel

private theorem r_895135 : RangeOk getRow 2051521 895135 895203 := by
  decide +kernel

private theorem r_895203 : RangeOk getRow 2051521 895203 895269 := by
  decide +kernel

private theorem r_895269 : RangeOk getRow 2051521 895269 895339 := by
  decide +kernel

private theorem r_895339 : RangeOk getRow 2051521 895339 895407 := by
  decide +kernel

private theorem r_895407 : RangeOk getRow 2051521 895407 895476 := by
  decide +kernel

private theorem r_895476 : RangeOk getRow 2051521 895476 895544 := by
  decide +kernel

private theorem r_895544 : RangeOk getRow 2051521 895544 895613 := by
  decide +kernel

private theorem r_895613 : RangeOk getRow 2051521 895613 895683 := by
  decide +kernel

private theorem r_895683 : RangeOk getRow 2051521 895683 895752 := by
  decide +kernel

private theorem r_895752 : RangeOk getRow 2051521 895752 895818 := by
  decide +kernel

private theorem r_895818 : RangeOk getRow 2051521 895818 895886 := by
  decide +kernel

private theorem s_893584 : RangeOk getRow 2051521 893518 893584 := r_893518
private theorem s_893652 : RangeOk getRow 2051521 893518 893652 :=
  s_893584.append (by norm_num) r_893584
private theorem s_893721 : RangeOk getRow 2051521 893518 893721 :=
  s_893652.append (by norm_num) r_893652
private theorem s_893786 : RangeOk getRow 2051521 893518 893786 :=
  s_893721.append (by norm_num) r_893721
private theorem s_893852 : RangeOk getRow 2051521 893518 893852 :=
  s_893786.append (by norm_num) r_893786
private theorem s_893920 : RangeOk getRow 2051521 893518 893920 :=
  s_893852.append (by norm_num) r_893852
private theorem s_893987 : RangeOk getRow 2051521 893518 893987 :=
  s_893920.append (by norm_num) r_893920
private theorem s_894056 : RangeOk getRow 2051521 893518 894056 :=
  s_893987.append (by norm_num) r_893987
private theorem s_894123 : RangeOk getRow 2051521 893518 894123 :=
  s_894056.append (by norm_num) r_894056
private theorem s_894191 : RangeOk getRow 2051521 893518 894191 :=
  s_894123.append (by norm_num) r_894123
private theorem s_894257 : RangeOk getRow 2051521 893518 894257 :=
  s_894191.append (by norm_num) r_894191
private theorem s_894323 : RangeOk getRow 2051521 893518 894323 :=
  s_894257.append (by norm_num) r_894257
private theorem s_894392 : RangeOk getRow 2051521 893518 894392 :=
  s_894323.append (by norm_num) r_894323
private theorem s_894458 : RangeOk getRow 2051521 893518 894458 :=
  s_894392.append (by norm_num) r_894392
private theorem s_894524 : RangeOk getRow 2051521 893518 894524 :=
  s_894458.append (by norm_num) r_894458
private theorem s_894595 : RangeOk getRow 2051521 893518 894595 :=
  s_894524.append (by norm_num) r_894524
private theorem s_894662 : RangeOk getRow 2051521 893518 894662 :=
  s_894595.append (by norm_num) r_894595
private theorem s_894730 : RangeOk getRow 2051521 893518 894730 :=
  s_894662.append (by norm_num) r_894662
private theorem s_894799 : RangeOk getRow 2051521 893518 894799 :=
  s_894730.append (by norm_num) r_894730
private theorem s_894867 : RangeOk getRow 2051521 893518 894867 :=
  s_894799.append (by norm_num) r_894799
private theorem s_894934 : RangeOk getRow 2051521 893518 894934 :=
  s_894867.append (by norm_num) r_894867
private theorem s_895000 : RangeOk getRow 2051521 893518 895000 :=
  s_894934.append (by norm_num) r_894934
private theorem s_895068 : RangeOk getRow 2051521 893518 895068 :=
  s_895000.append (by norm_num) r_895000
private theorem s_895135 : RangeOk getRow 2051521 893518 895135 :=
  s_895068.append (by norm_num) r_895068
private theorem s_895203 : RangeOk getRow 2051521 893518 895203 :=
  s_895135.append (by norm_num) r_895135
private theorem s_895269 : RangeOk getRow 2051521 893518 895269 :=
  s_895203.append (by norm_num) r_895203
private theorem s_895339 : RangeOk getRow 2051521 893518 895339 :=
  s_895269.append (by norm_num) r_895269
private theorem s_895407 : RangeOk getRow 2051521 893518 895407 :=
  s_895339.append (by norm_num) r_895339
private theorem s_895476 : RangeOk getRow 2051521 893518 895476 :=
  s_895407.append (by norm_num) r_895407
private theorem s_895544 : RangeOk getRow 2051521 893518 895544 :=
  s_895476.append (by norm_num) r_895476
private theorem s_895613 : RangeOk getRow 2051521 893518 895613 :=
  s_895544.append (by norm_num) r_895544
private theorem s_895683 : RangeOk getRow 2051521 893518 895683 :=
  s_895613.append (by norm_num) r_895613
private theorem s_895752 : RangeOk getRow 2051521 893518 895752 :=
  s_895683.append (by norm_num) r_895683
private theorem s_895818 : RangeOk getRow 2051521 893518 895818 :=
  s_895752.append (by norm_num) r_895752
private theorem s_895886 : RangeOk getRow 2051521 893518 895886 :=
  s_895818.append (by norm_num) r_895818

/-- Rows `[893518, 895886)` are valid. -/
theorem rangeOk_893518_895886 : RangeOk getRow 2051521 893518 895886 := s_895886

end Noperthedron.Solution
