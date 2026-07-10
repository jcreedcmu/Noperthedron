import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[635895, 638112). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_635895 : RangeOk getRow 2051521 635895 635960 := by
  decide +kernel

private theorem r_635960 : RangeOk getRow 2051521 635960 636028 := by
  decide +kernel

private theorem r_636028 : RangeOk getRow 2051521 636028 636095 := by
  decide +kernel

private theorem r_636095 : RangeOk getRow 2051521 636095 636165 := by
  decide +kernel

private theorem r_636165 : RangeOk getRow 2051521 636165 636232 := by
  decide +kernel

private theorem r_636232 : RangeOk getRow 2051521 636232 636297 := by
  decide +kernel

private theorem r_636297 : RangeOk getRow 2051521 636297 636363 := by
  decide +kernel

private theorem r_636363 : RangeOk getRow 2051521 636363 636430 := by
  decide +kernel

private theorem r_636430 : RangeOk getRow 2051521 636430 636497 := by
  decide +kernel

private theorem r_636497 : RangeOk getRow 2051521 636497 636564 := by
  decide +kernel

private theorem r_636564 : RangeOk getRow 2051521 636564 636632 := by
  decide +kernel

private theorem r_636632 : RangeOk getRow 2051521 636632 636700 := by
  decide +kernel

private theorem r_636700 : RangeOk getRow 2051521 636700 636767 := by
  decide +kernel

private theorem r_636767 : RangeOk getRow 2051521 636767 636833 := by
  decide +kernel

private theorem r_636833 : RangeOk getRow 2051521 636833 636899 := by
  decide +kernel

private theorem r_636899 : RangeOk getRow 2051521 636899 636967 := by
  decide +kernel

private theorem r_636967 : RangeOk getRow 2051521 636967 637036 := by
  decide +kernel

private theorem r_637036 : RangeOk getRow 2051521 637036 637104 := by
  decide +kernel

private theorem r_637104 : RangeOk getRow 2051521 637104 637172 := by
  decide +kernel

private theorem r_637172 : RangeOk getRow 2051521 637172 637240 := by
  decide +kernel

private theorem r_637240 : RangeOk getRow 2051521 637240 637308 := by
  decide +kernel

private theorem r_637308 : RangeOk getRow 2051521 637308 637374 := by
  decide +kernel

private theorem r_637374 : RangeOk getRow 2051521 637374 637440 := by
  decide +kernel

private theorem r_637440 : RangeOk getRow 2051521 637440 637507 := by
  decide +kernel

private theorem r_637507 : RangeOk getRow 2051521 637507 637575 := by
  decide +kernel

private theorem r_637575 : RangeOk getRow 2051521 637575 637643 := by
  decide +kernel

private theorem r_637643 : RangeOk getRow 2051521 637643 637711 := by
  decide +kernel

private theorem r_637711 : RangeOk getRow 2051521 637711 637778 := by
  decide +kernel

private theorem r_637778 : RangeOk getRow 2051521 637778 637844 := by
  decide +kernel

private theorem r_637844 : RangeOk getRow 2051521 637844 637910 := by
  decide +kernel

private theorem r_637910 : RangeOk getRow 2051521 637910 637977 := by
  decide +kernel

private theorem r_637977 : RangeOk getRow 2051521 637977 638044 := by
  decide +kernel

private theorem r_638044 : RangeOk getRow 2051521 638044 638112 := by
  decide +kernel

private theorem s_635960 : RangeOk getRow 2051521 635895 635960 := r_635895
private theorem s_636028 : RangeOk getRow 2051521 635895 636028 :=
  s_635960.append (by norm_num) r_635960
private theorem s_636095 : RangeOk getRow 2051521 635895 636095 :=
  s_636028.append (by norm_num) r_636028
private theorem s_636165 : RangeOk getRow 2051521 635895 636165 :=
  s_636095.append (by norm_num) r_636095
private theorem s_636232 : RangeOk getRow 2051521 635895 636232 :=
  s_636165.append (by norm_num) r_636165
private theorem s_636297 : RangeOk getRow 2051521 635895 636297 :=
  s_636232.append (by norm_num) r_636232
private theorem s_636363 : RangeOk getRow 2051521 635895 636363 :=
  s_636297.append (by norm_num) r_636297
private theorem s_636430 : RangeOk getRow 2051521 635895 636430 :=
  s_636363.append (by norm_num) r_636363
private theorem s_636497 : RangeOk getRow 2051521 635895 636497 :=
  s_636430.append (by norm_num) r_636430
private theorem s_636564 : RangeOk getRow 2051521 635895 636564 :=
  s_636497.append (by norm_num) r_636497
private theorem s_636632 : RangeOk getRow 2051521 635895 636632 :=
  s_636564.append (by norm_num) r_636564
private theorem s_636700 : RangeOk getRow 2051521 635895 636700 :=
  s_636632.append (by norm_num) r_636632
private theorem s_636767 : RangeOk getRow 2051521 635895 636767 :=
  s_636700.append (by norm_num) r_636700
private theorem s_636833 : RangeOk getRow 2051521 635895 636833 :=
  s_636767.append (by norm_num) r_636767
private theorem s_636899 : RangeOk getRow 2051521 635895 636899 :=
  s_636833.append (by norm_num) r_636833
private theorem s_636967 : RangeOk getRow 2051521 635895 636967 :=
  s_636899.append (by norm_num) r_636899
private theorem s_637036 : RangeOk getRow 2051521 635895 637036 :=
  s_636967.append (by norm_num) r_636967
private theorem s_637104 : RangeOk getRow 2051521 635895 637104 :=
  s_637036.append (by norm_num) r_637036
private theorem s_637172 : RangeOk getRow 2051521 635895 637172 :=
  s_637104.append (by norm_num) r_637104
private theorem s_637240 : RangeOk getRow 2051521 635895 637240 :=
  s_637172.append (by norm_num) r_637172
private theorem s_637308 : RangeOk getRow 2051521 635895 637308 :=
  s_637240.append (by norm_num) r_637240
private theorem s_637374 : RangeOk getRow 2051521 635895 637374 :=
  s_637308.append (by norm_num) r_637308
private theorem s_637440 : RangeOk getRow 2051521 635895 637440 :=
  s_637374.append (by norm_num) r_637374
private theorem s_637507 : RangeOk getRow 2051521 635895 637507 :=
  s_637440.append (by norm_num) r_637440
private theorem s_637575 : RangeOk getRow 2051521 635895 637575 :=
  s_637507.append (by norm_num) r_637507
private theorem s_637643 : RangeOk getRow 2051521 635895 637643 :=
  s_637575.append (by norm_num) r_637575
private theorem s_637711 : RangeOk getRow 2051521 635895 637711 :=
  s_637643.append (by norm_num) r_637643
private theorem s_637778 : RangeOk getRow 2051521 635895 637778 :=
  s_637711.append (by norm_num) r_637711
private theorem s_637844 : RangeOk getRow 2051521 635895 637844 :=
  s_637778.append (by norm_num) r_637778
private theorem s_637910 : RangeOk getRow 2051521 635895 637910 :=
  s_637844.append (by norm_num) r_637844
private theorem s_637977 : RangeOk getRow 2051521 635895 637977 :=
  s_637910.append (by norm_num) r_637910
private theorem s_638044 : RangeOk getRow 2051521 635895 638044 :=
  s_637977.append (by norm_num) r_637977
private theorem s_638112 : RangeOk getRow 2051521 635895 638112 :=
  s_638044.append (by norm_num) r_638044

/-- Rows `[635895, 638112)` are valid. -/
theorem rangeOk_635895_638112 : RangeOk getRow 2051521 635895 638112 := s_638112

end Noperthedron.Solution
