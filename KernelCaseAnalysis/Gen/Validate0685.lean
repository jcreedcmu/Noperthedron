import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1746882, 1749921). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1746882 : RangeOk getRow 2051521 1746882 1746951 := by
  decide +kernel

private theorem r_1746951 : RangeOk getRow 2051521 1746951 1747023 := by
  decide +kernel

private theorem r_1747023 : RangeOk getRow 2051521 1747023 1747094 := by
  decide +kernel

private theorem r_1747094 : RangeOk getRow 2051521 1747094 1747165 := by
  decide +kernel

private theorem r_1747165 : RangeOk getRow 2051521 1747165 1747234 := by
  decide +kernel

private theorem r_1747234 : RangeOk getRow 2051521 1747234 1747292 := by
  decide +kernel

private theorem r_1747292 : RangeOk getRow 2051521 1747292 1747327 := by
  decide +kernel

private theorem r_1747327 : RangeOk getRow 2051521 1747327 1747377 := by
  decide +kernel

private theorem r_1747377 : RangeOk getRow 2051521 1747377 1747425 := by
  decide +kernel

private theorem r_1747425 : RangeOk getRow 2051521 1747425 1747473 := by
  decide +kernel

private theorem r_1747473 : RangeOk getRow 2051521 1747473 1747507 := by
  decide +kernel

private theorem r_1747507 : RangeOk getRow 2051521 1747507 1747550 := by
  decide +kernel

private theorem r_1747550 : RangeOk getRow 2051521 1747550 1747606 := by
  decide +kernel

private theorem r_1747606 : RangeOk getRow 2051521 1747606 1747647 := by
  decide +kernel

private theorem r_1747647 : RangeOk getRow 2051521 1747647 1747683 := by
  decide +kernel

private theorem r_1747683 : RangeOk getRow 2051521 1747683 1747720 := by
  decide +kernel

private theorem r_1747720 : RangeOk getRow 2051521 1747720 1747792 := by
  decide +kernel

private theorem r_1747792 : RangeOk getRow 2051521 1747792 1747864 := by
  decide +kernel

private theorem r_1747864 : RangeOk getRow 2051521 1747864 1747937 := by
  decide +kernel

private theorem r_1747937 : RangeOk getRow 2051521 1747937 1748008 := by
  decide +kernel

private theorem r_1748008 : RangeOk getRow 2051521 1748008 1748081 := by
  decide +kernel

private theorem r_1748081 : RangeOk getRow 2051521 1748081 1748154 := by
  decide +kernel

private theorem r_1748154 : RangeOk getRow 2051521 1748154 1748226 := by
  decide +kernel

private theorem r_1748226 : RangeOk getRow 2051521 1748226 1748297 := by
  decide +kernel

private theorem r_1748297 : RangeOk getRow 2051521 1748297 1748369 := by
  decide +kernel

private theorem r_1748369 : RangeOk getRow 2051521 1748369 1748440 := by
  decide +kernel

private theorem r_1748440 : RangeOk getRow 2051521 1748440 1748511 := by
  decide +kernel

private theorem r_1748511 : RangeOk getRow 2051521 1748511 1748584 := by
  decide +kernel

private theorem r_1748584 : RangeOk getRow 2051521 1748584 1748657 := by
  decide +kernel

private theorem r_1748657 : RangeOk getRow 2051521 1748657 1748728 := by
  decide +kernel

private theorem r_1748728 : RangeOk getRow 2051521 1748728 1748796 := by
  decide +kernel

private theorem r_1748796 : RangeOk getRow 2051521 1748796 1748868 := by
  decide +kernel

private theorem r_1748868 : RangeOk getRow 2051521 1748868 1748940 := by
  decide +kernel

private theorem r_1748940 : RangeOk getRow 2051521 1748940 1749013 := by
  decide +kernel

private theorem r_1749013 : RangeOk getRow 2051521 1749013 1749083 := by
  decide +kernel

private theorem r_1749083 : RangeOk getRow 2051521 1749083 1749151 := by
  decide +kernel

private theorem r_1749151 : RangeOk getRow 2051521 1749151 1749224 := by
  decide +kernel

private theorem r_1749224 : RangeOk getRow 2051521 1749224 1749297 := by
  decide +kernel

private theorem r_1749297 : RangeOk getRow 2051521 1749297 1749368 := by
  decide +kernel

private theorem r_1749368 : RangeOk getRow 2051521 1749368 1749436 := by
  decide +kernel

private theorem r_1749436 : RangeOk getRow 2051521 1749436 1749507 := by
  decide +kernel

private theorem r_1749507 : RangeOk getRow 2051521 1749507 1749577 := by
  decide +kernel

private theorem r_1749577 : RangeOk getRow 2051521 1749577 1749646 := by
  decide +kernel

private theorem r_1749646 : RangeOk getRow 2051521 1749646 1749715 := by
  decide +kernel

private theorem r_1749715 : RangeOk getRow 2051521 1749715 1749784 := by
  decide +kernel

private theorem r_1749784 : RangeOk getRow 2051521 1749784 1749853 := by
  decide +kernel

private theorem r_1749853 : RangeOk getRow 2051521 1749853 1749921 := by
  decide +kernel

private theorem s_1746951 : RangeOk getRow 2051521 1746882 1746951 := r_1746882
private theorem s_1747023 : RangeOk getRow 2051521 1746882 1747023 :=
  s_1746951.append (by norm_num) r_1746951
private theorem s_1747094 : RangeOk getRow 2051521 1746882 1747094 :=
  s_1747023.append (by norm_num) r_1747023
private theorem s_1747165 : RangeOk getRow 2051521 1746882 1747165 :=
  s_1747094.append (by norm_num) r_1747094
private theorem s_1747234 : RangeOk getRow 2051521 1746882 1747234 :=
  s_1747165.append (by norm_num) r_1747165
private theorem s_1747292 : RangeOk getRow 2051521 1746882 1747292 :=
  s_1747234.append (by norm_num) r_1747234
private theorem s_1747327 : RangeOk getRow 2051521 1746882 1747327 :=
  s_1747292.append (by norm_num) r_1747292
private theorem s_1747377 : RangeOk getRow 2051521 1746882 1747377 :=
  s_1747327.append (by norm_num) r_1747327
private theorem s_1747425 : RangeOk getRow 2051521 1746882 1747425 :=
  s_1747377.append (by norm_num) r_1747377
private theorem s_1747473 : RangeOk getRow 2051521 1746882 1747473 :=
  s_1747425.append (by norm_num) r_1747425
private theorem s_1747507 : RangeOk getRow 2051521 1746882 1747507 :=
  s_1747473.append (by norm_num) r_1747473
private theorem s_1747550 : RangeOk getRow 2051521 1746882 1747550 :=
  s_1747507.append (by norm_num) r_1747507
private theorem s_1747606 : RangeOk getRow 2051521 1746882 1747606 :=
  s_1747550.append (by norm_num) r_1747550
private theorem s_1747647 : RangeOk getRow 2051521 1746882 1747647 :=
  s_1747606.append (by norm_num) r_1747606
private theorem s_1747683 : RangeOk getRow 2051521 1746882 1747683 :=
  s_1747647.append (by norm_num) r_1747647
private theorem s_1747720 : RangeOk getRow 2051521 1746882 1747720 :=
  s_1747683.append (by norm_num) r_1747683
private theorem s_1747792 : RangeOk getRow 2051521 1746882 1747792 :=
  s_1747720.append (by norm_num) r_1747720
private theorem s_1747864 : RangeOk getRow 2051521 1746882 1747864 :=
  s_1747792.append (by norm_num) r_1747792
private theorem s_1747937 : RangeOk getRow 2051521 1746882 1747937 :=
  s_1747864.append (by norm_num) r_1747864
private theorem s_1748008 : RangeOk getRow 2051521 1746882 1748008 :=
  s_1747937.append (by norm_num) r_1747937
private theorem s_1748081 : RangeOk getRow 2051521 1746882 1748081 :=
  s_1748008.append (by norm_num) r_1748008
private theorem s_1748154 : RangeOk getRow 2051521 1746882 1748154 :=
  s_1748081.append (by norm_num) r_1748081
private theorem s_1748226 : RangeOk getRow 2051521 1746882 1748226 :=
  s_1748154.append (by norm_num) r_1748154
private theorem s_1748297 : RangeOk getRow 2051521 1746882 1748297 :=
  s_1748226.append (by norm_num) r_1748226
private theorem s_1748369 : RangeOk getRow 2051521 1746882 1748369 :=
  s_1748297.append (by norm_num) r_1748297
private theorem s_1748440 : RangeOk getRow 2051521 1746882 1748440 :=
  s_1748369.append (by norm_num) r_1748369
private theorem s_1748511 : RangeOk getRow 2051521 1746882 1748511 :=
  s_1748440.append (by norm_num) r_1748440
private theorem s_1748584 : RangeOk getRow 2051521 1746882 1748584 :=
  s_1748511.append (by norm_num) r_1748511
private theorem s_1748657 : RangeOk getRow 2051521 1746882 1748657 :=
  s_1748584.append (by norm_num) r_1748584
private theorem s_1748728 : RangeOk getRow 2051521 1746882 1748728 :=
  s_1748657.append (by norm_num) r_1748657
private theorem s_1748796 : RangeOk getRow 2051521 1746882 1748796 :=
  s_1748728.append (by norm_num) r_1748728
private theorem s_1748868 : RangeOk getRow 2051521 1746882 1748868 :=
  s_1748796.append (by norm_num) r_1748796
private theorem s_1748940 : RangeOk getRow 2051521 1746882 1748940 :=
  s_1748868.append (by norm_num) r_1748868
private theorem s_1749013 : RangeOk getRow 2051521 1746882 1749013 :=
  s_1748940.append (by norm_num) r_1748940
private theorem s_1749083 : RangeOk getRow 2051521 1746882 1749083 :=
  s_1749013.append (by norm_num) r_1749013
private theorem s_1749151 : RangeOk getRow 2051521 1746882 1749151 :=
  s_1749083.append (by norm_num) r_1749083
private theorem s_1749224 : RangeOk getRow 2051521 1746882 1749224 :=
  s_1749151.append (by norm_num) r_1749151
private theorem s_1749297 : RangeOk getRow 2051521 1746882 1749297 :=
  s_1749224.append (by norm_num) r_1749224
private theorem s_1749368 : RangeOk getRow 2051521 1746882 1749368 :=
  s_1749297.append (by norm_num) r_1749297
private theorem s_1749436 : RangeOk getRow 2051521 1746882 1749436 :=
  s_1749368.append (by norm_num) r_1749368
private theorem s_1749507 : RangeOk getRow 2051521 1746882 1749507 :=
  s_1749436.append (by norm_num) r_1749436
private theorem s_1749577 : RangeOk getRow 2051521 1746882 1749577 :=
  s_1749507.append (by norm_num) r_1749507
private theorem s_1749646 : RangeOk getRow 2051521 1746882 1749646 :=
  s_1749577.append (by norm_num) r_1749577
private theorem s_1749715 : RangeOk getRow 2051521 1746882 1749715 :=
  s_1749646.append (by norm_num) r_1749646
private theorem s_1749784 : RangeOk getRow 2051521 1746882 1749784 :=
  s_1749715.append (by norm_num) r_1749715
private theorem s_1749853 : RangeOk getRow 2051521 1746882 1749853 :=
  s_1749784.append (by norm_num) r_1749784
private theorem s_1749921 : RangeOk getRow 2051521 1746882 1749921 :=
  s_1749853.append (by norm_num) r_1749853

/-- Rows `[1746882, 1749921)` are valid. -/
theorem rangeOk_1746882_1749921 : RangeOk getRow 2051521 1746882 1749921 := s_1749921

end Noperthedron.Solution
