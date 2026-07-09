import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1059453, 1061884). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1059453 : RangeOk getRow 2051521 1059453 1059519 := by
  decide +kernel

private theorem r_1059519 : RangeOk getRow 2051521 1059519 1059586 := by
  decide +kernel

private theorem r_1059586 : RangeOk getRow 2051521 1059586 1059655 := by
  decide +kernel

private theorem r_1059655 : RangeOk getRow 2051521 1059655 1059720 := by
  decide +kernel

private theorem r_1059720 : RangeOk getRow 2051521 1059720 1059786 := by
  decide +kernel

private theorem r_1059786 : RangeOk getRow 2051521 1059786 1059853 := by
  decide +kernel

private theorem r_1059853 : RangeOk getRow 2051521 1059853 1059920 := by
  decide +kernel

private theorem r_1059920 : RangeOk getRow 2051521 1059920 1059991 := by
  decide +kernel

private theorem r_1059991 : RangeOk getRow 2051521 1059991 1060063 := by
  decide +kernel

private theorem r_1060063 : RangeOk getRow 2051521 1060063 1060131 := by
  decide +kernel

private theorem r_1060131 : RangeOk getRow 2051521 1060131 1060199 := by
  decide +kernel

private theorem r_1060199 : RangeOk getRow 2051521 1060199 1060267 := by
  decide +kernel

private theorem r_1060267 : RangeOk getRow 2051521 1060267 1060335 := by
  decide +kernel

private theorem r_1060335 : RangeOk getRow 2051521 1060335 1060402 := by
  decide +kernel

private theorem r_1060402 : RangeOk getRow 2051521 1060402 1060471 := by
  decide +kernel

private theorem r_1060471 : RangeOk getRow 2051521 1060471 1060538 := by
  decide +kernel

private theorem r_1060538 : RangeOk getRow 2051521 1060538 1060594 := by
  decide +kernel

private theorem r_1060594 : RangeOk getRow 2051521 1060594 1060656 := by
  decide +kernel

private theorem r_1060656 : RangeOk getRow 2051521 1060656 1060724 := by
  decide +kernel

private theorem r_1060724 : RangeOk getRow 2051521 1060724 1060792 := by
  decide +kernel

private theorem r_1060792 : RangeOk getRow 2051521 1060792 1060862 := by
  decide +kernel

private theorem r_1060862 : RangeOk getRow 2051521 1060862 1060933 := by
  decide +kernel

private theorem r_1060933 : RangeOk getRow 2051521 1060933 1061003 := by
  decide +kernel

private theorem r_1061003 : RangeOk getRow 2051521 1061003 1061069 := by
  decide +kernel

private theorem r_1061069 : RangeOk getRow 2051521 1061069 1061138 := by
  decide +kernel

private theorem r_1061138 : RangeOk getRow 2051521 1061138 1061204 := by
  decide +kernel

private theorem r_1061204 : RangeOk getRow 2051521 1061204 1061270 := by
  decide +kernel

private theorem r_1061270 : RangeOk getRow 2051521 1061270 1061338 := by
  decide +kernel

private theorem r_1061338 : RangeOk getRow 2051521 1061338 1061410 := by
  decide +kernel

private theorem r_1061410 : RangeOk getRow 2051521 1061410 1061480 := by
  decide +kernel

private theorem r_1061480 : RangeOk getRow 2051521 1061480 1061547 := by
  decide +kernel

private theorem r_1061547 : RangeOk getRow 2051521 1061547 1061615 := by
  decide +kernel

private theorem r_1061615 : RangeOk getRow 2051521 1061615 1061685 := by
  decide +kernel

private theorem r_1061685 : RangeOk getRow 2051521 1061685 1061751 := by
  decide +kernel

private theorem r_1061751 : RangeOk getRow 2051521 1061751 1061818 := by
  decide +kernel

private theorem r_1061818 : RangeOk getRow 2051521 1061818 1061884 := by
  decide +kernel

private theorem s_1059519 : RangeOk getRow 2051521 1059453 1059519 := r_1059453
private theorem s_1059586 : RangeOk getRow 2051521 1059453 1059586 :=
  s_1059519.append (by norm_num) r_1059519
private theorem s_1059655 : RangeOk getRow 2051521 1059453 1059655 :=
  s_1059586.append (by norm_num) r_1059586
private theorem s_1059720 : RangeOk getRow 2051521 1059453 1059720 :=
  s_1059655.append (by norm_num) r_1059655
private theorem s_1059786 : RangeOk getRow 2051521 1059453 1059786 :=
  s_1059720.append (by norm_num) r_1059720
private theorem s_1059853 : RangeOk getRow 2051521 1059453 1059853 :=
  s_1059786.append (by norm_num) r_1059786
private theorem s_1059920 : RangeOk getRow 2051521 1059453 1059920 :=
  s_1059853.append (by norm_num) r_1059853
private theorem s_1059991 : RangeOk getRow 2051521 1059453 1059991 :=
  s_1059920.append (by norm_num) r_1059920
private theorem s_1060063 : RangeOk getRow 2051521 1059453 1060063 :=
  s_1059991.append (by norm_num) r_1059991
private theorem s_1060131 : RangeOk getRow 2051521 1059453 1060131 :=
  s_1060063.append (by norm_num) r_1060063
private theorem s_1060199 : RangeOk getRow 2051521 1059453 1060199 :=
  s_1060131.append (by norm_num) r_1060131
private theorem s_1060267 : RangeOk getRow 2051521 1059453 1060267 :=
  s_1060199.append (by norm_num) r_1060199
private theorem s_1060335 : RangeOk getRow 2051521 1059453 1060335 :=
  s_1060267.append (by norm_num) r_1060267
private theorem s_1060402 : RangeOk getRow 2051521 1059453 1060402 :=
  s_1060335.append (by norm_num) r_1060335
private theorem s_1060471 : RangeOk getRow 2051521 1059453 1060471 :=
  s_1060402.append (by norm_num) r_1060402
private theorem s_1060538 : RangeOk getRow 2051521 1059453 1060538 :=
  s_1060471.append (by norm_num) r_1060471
private theorem s_1060594 : RangeOk getRow 2051521 1059453 1060594 :=
  s_1060538.append (by norm_num) r_1060538
private theorem s_1060656 : RangeOk getRow 2051521 1059453 1060656 :=
  s_1060594.append (by norm_num) r_1060594
private theorem s_1060724 : RangeOk getRow 2051521 1059453 1060724 :=
  s_1060656.append (by norm_num) r_1060656
private theorem s_1060792 : RangeOk getRow 2051521 1059453 1060792 :=
  s_1060724.append (by norm_num) r_1060724
private theorem s_1060862 : RangeOk getRow 2051521 1059453 1060862 :=
  s_1060792.append (by norm_num) r_1060792
private theorem s_1060933 : RangeOk getRow 2051521 1059453 1060933 :=
  s_1060862.append (by norm_num) r_1060862
private theorem s_1061003 : RangeOk getRow 2051521 1059453 1061003 :=
  s_1060933.append (by norm_num) r_1060933
private theorem s_1061069 : RangeOk getRow 2051521 1059453 1061069 :=
  s_1061003.append (by norm_num) r_1061003
private theorem s_1061138 : RangeOk getRow 2051521 1059453 1061138 :=
  s_1061069.append (by norm_num) r_1061069
private theorem s_1061204 : RangeOk getRow 2051521 1059453 1061204 :=
  s_1061138.append (by norm_num) r_1061138
private theorem s_1061270 : RangeOk getRow 2051521 1059453 1061270 :=
  s_1061204.append (by norm_num) r_1061204
private theorem s_1061338 : RangeOk getRow 2051521 1059453 1061338 :=
  s_1061270.append (by norm_num) r_1061270
private theorem s_1061410 : RangeOk getRow 2051521 1059453 1061410 :=
  s_1061338.append (by norm_num) r_1061338
private theorem s_1061480 : RangeOk getRow 2051521 1059453 1061480 :=
  s_1061410.append (by norm_num) r_1061410
private theorem s_1061547 : RangeOk getRow 2051521 1059453 1061547 :=
  s_1061480.append (by norm_num) r_1061480
private theorem s_1061615 : RangeOk getRow 2051521 1059453 1061615 :=
  s_1061547.append (by norm_num) r_1061547
private theorem s_1061685 : RangeOk getRow 2051521 1059453 1061685 :=
  s_1061615.append (by norm_num) r_1061615
private theorem s_1061751 : RangeOk getRow 2051521 1059453 1061751 :=
  s_1061685.append (by norm_num) r_1061685
private theorem s_1061818 : RangeOk getRow 2051521 1059453 1061818 :=
  s_1061751.append (by norm_num) r_1061751
private theorem s_1061884 : RangeOk getRow 2051521 1059453 1061884 :=
  s_1061818.append (by norm_num) r_1061818

/-- Rows `[1059453, 1061884)` are valid. -/
theorem rangeOk_1059453_1061884 : RangeOk getRow 2051521 1059453 1061884 := s_1061884

end Noperthedron.Solution
