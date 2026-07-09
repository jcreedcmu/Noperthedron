import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[194968, 196696). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_194968 : RangeOk getRow 2051521 194968 195032 := by
  decide +kernel

private theorem r_195032 : RangeOk getRow 2051521 195032 195096 := by
  decide +kernel

private theorem r_195096 : RangeOk getRow 2051521 195096 195160 := by
  decide +kernel

private theorem r_195160 : RangeOk getRow 2051521 195160 195224 := by
  decide +kernel

private theorem r_195224 : RangeOk getRow 2051521 195224 195288 := by
  decide +kernel

private theorem r_195288 : RangeOk getRow 2051521 195288 195352 := by
  decide +kernel

private theorem r_195352 : RangeOk getRow 2051521 195352 195416 := by
  decide +kernel

private theorem r_195416 : RangeOk getRow 2051521 195416 195480 := by
  decide +kernel

private theorem r_195480 : RangeOk getRow 2051521 195480 195544 := by
  decide +kernel

private theorem r_195544 : RangeOk getRow 2051521 195544 195608 := by
  decide +kernel

private theorem r_195608 : RangeOk getRow 2051521 195608 195672 := by
  decide +kernel

private theorem r_195672 : RangeOk getRow 2051521 195672 195736 := by
  decide +kernel

private theorem r_195736 : RangeOk getRow 2051521 195736 195800 := by
  decide +kernel

private theorem r_195800 : RangeOk getRow 2051521 195800 195864 := by
  decide +kernel

private theorem r_195864 : RangeOk getRow 2051521 195864 195928 := by
  decide +kernel

private theorem r_195928 : RangeOk getRow 2051521 195928 195992 := by
  decide +kernel

private theorem r_195992 : RangeOk getRow 2051521 195992 196056 := by
  decide +kernel

private theorem r_196056 : RangeOk getRow 2051521 196056 196120 := by
  decide +kernel

private theorem r_196120 : RangeOk getRow 2051521 196120 196184 := by
  decide +kernel

private theorem r_196184 : RangeOk getRow 2051521 196184 196248 := by
  decide +kernel

private theorem r_196248 : RangeOk getRow 2051521 196248 196312 := by
  decide +kernel

private theorem r_196312 : RangeOk getRow 2051521 196312 196376 := by
  decide +kernel

private theorem r_196376 : RangeOk getRow 2051521 196376 196440 := by
  decide +kernel

private theorem r_196440 : RangeOk getRow 2051521 196440 196504 := by
  decide +kernel

private theorem r_196504 : RangeOk getRow 2051521 196504 196568 := by
  decide +kernel

private theorem r_196568 : RangeOk getRow 2051521 196568 196632 := by
  decide +kernel

private theorem r_196632 : RangeOk getRow 2051521 196632 196696 := by
  decide +kernel

private theorem s_195032 : RangeOk getRow 2051521 194968 195032 := r_194968
private theorem s_195096 : RangeOk getRow 2051521 194968 195096 :=
  s_195032.append (by norm_num) r_195032
private theorem s_195160 : RangeOk getRow 2051521 194968 195160 :=
  s_195096.append (by norm_num) r_195096
private theorem s_195224 : RangeOk getRow 2051521 194968 195224 :=
  s_195160.append (by norm_num) r_195160
private theorem s_195288 : RangeOk getRow 2051521 194968 195288 :=
  s_195224.append (by norm_num) r_195224
private theorem s_195352 : RangeOk getRow 2051521 194968 195352 :=
  s_195288.append (by norm_num) r_195288
private theorem s_195416 : RangeOk getRow 2051521 194968 195416 :=
  s_195352.append (by norm_num) r_195352
private theorem s_195480 : RangeOk getRow 2051521 194968 195480 :=
  s_195416.append (by norm_num) r_195416
private theorem s_195544 : RangeOk getRow 2051521 194968 195544 :=
  s_195480.append (by norm_num) r_195480
private theorem s_195608 : RangeOk getRow 2051521 194968 195608 :=
  s_195544.append (by norm_num) r_195544
private theorem s_195672 : RangeOk getRow 2051521 194968 195672 :=
  s_195608.append (by norm_num) r_195608
private theorem s_195736 : RangeOk getRow 2051521 194968 195736 :=
  s_195672.append (by norm_num) r_195672
private theorem s_195800 : RangeOk getRow 2051521 194968 195800 :=
  s_195736.append (by norm_num) r_195736
private theorem s_195864 : RangeOk getRow 2051521 194968 195864 :=
  s_195800.append (by norm_num) r_195800
private theorem s_195928 : RangeOk getRow 2051521 194968 195928 :=
  s_195864.append (by norm_num) r_195864
private theorem s_195992 : RangeOk getRow 2051521 194968 195992 :=
  s_195928.append (by norm_num) r_195928
private theorem s_196056 : RangeOk getRow 2051521 194968 196056 :=
  s_195992.append (by norm_num) r_195992
private theorem s_196120 : RangeOk getRow 2051521 194968 196120 :=
  s_196056.append (by norm_num) r_196056
private theorem s_196184 : RangeOk getRow 2051521 194968 196184 :=
  s_196120.append (by norm_num) r_196120
private theorem s_196248 : RangeOk getRow 2051521 194968 196248 :=
  s_196184.append (by norm_num) r_196184
private theorem s_196312 : RangeOk getRow 2051521 194968 196312 :=
  s_196248.append (by norm_num) r_196248
private theorem s_196376 : RangeOk getRow 2051521 194968 196376 :=
  s_196312.append (by norm_num) r_196312
private theorem s_196440 : RangeOk getRow 2051521 194968 196440 :=
  s_196376.append (by norm_num) r_196376
private theorem s_196504 : RangeOk getRow 2051521 194968 196504 :=
  s_196440.append (by norm_num) r_196440
private theorem s_196568 : RangeOk getRow 2051521 194968 196568 :=
  s_196504.append (by norm_num) r_196504
private theorem s_196632 : RangeOk getRow 2051521 194968 196632 :=
  s_196568.append (by norm_num) r_196568
private theorem s_196696 : RangeOk getRow 2051521 194968 196696 :=
  s_196632.append (by norm_num) r_196632

/-- Rows `[194968, 196696)` are valid. -/
theorem rangeOk_194968_196696 : RangeOk getRow 2051521 194968 196696 := s_196696

end Noperthedron.Solution
