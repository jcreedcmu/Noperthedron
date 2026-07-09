import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[806123, 808252). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_806123 : RangeOk getRow 2051521 806123 806188 := by
  decide +kernel

private theorem r_806188 : RangeOk getRow 2051521 806188 806254 := by
  decide +kernel

private theorem r_806254 : RangeOk getRow 2051521 806254 806321 := by
  decide +kernel

private theorem r_806321 : RangeOk getRow 2051521 806321 806387 := by
  decide +kernel

private theorem r_806387 : RangeOk getRow 2051521 806387 806454 := by
  decide +kernel

private theorem r_806454 : RangeOk getRow 2051521 806454 806518 := by
  decide +kernel

private theorem r_806518 : RangeOk getRow 2051521 806518 806585 := by
  decide +kernel

private theorem r_806585 : RangeOk getRow 2051521 806585 806652 := by
  decide +kernel

private theorem r_806652 : RangeOk getRow 2051521 806652 806718 := by
  decide +kernel

private theorem r_806718 : RangeOk getRow 2051521 806718 806783 := by
  decide +kernel

private theorem r_806783 : RangeOk getRow 2051521 806783 806848 := by
  decide +kernel

private theorem r_806848 : RangeOk getRow 2051521 806848 806913 := by
  decide +kernel

private theorem r_806913 : RangeOk getRow 2051521 806913 806977 := by
  decide +kernel

private theorem r_806977 : RangeOk getRow 2051521 806977 807045 := by
  decide +kernel

private theorem r_807045 : RangeOk getRow 2051521 807045 807113 := by
  decide +kernel

private theorem r_807113 : RangeOk getRow 2051521 807113 807181 := by
  decide +kernel

private theorem r_807181 : RangeOk getRow 2051521 807181 807248 := by
  decide +kernel

private theorem r_807248 : RangeOk getRow 2051521 807248 807315 := by
  decide +kernel

private theorem r_807315 : RangeOk getRow 2051521 807315 807381 := by
  decide +kernel

private theorem r_807381 : RangeOk getRow 2051521 807381 807446 := by
  decide +kernel

private theorem r_807446 : RangeOk getRow 2051521 807446 807510 := by
  decide +kernel

private theorem r_807510 : RangeOk getRow 2051521 807510 807578 := by
  decide +kernel

private theorem r_807578 : RangeOk getRow 2051521 807578 807645 := by
  decide +kernel

private theorem r_807645 : RangeOk getRow 2051521 807645 807714 := by
  decide +kernel

private theorem r_807714 : RangeOk getRow 2051521 807714 807783 := by
  decide +kernel

private theorem r_807783 : RangeOk getRow 2051521 807783 807852 := by
  decide +kernel

private theorem r_807852 : RangeOk getRow 2051521 807852 807919 := by
  decide +kernel

private theorem r_807919 : RangeOk getRow 2051521 807919 807985 := by
  decide +kernel

private theorem r_807985 : RangeOk getRow 2051521 807985 808053 := by
  decide +kernel

private theorem r_808053 : RangeOk getRow 2051521 808053 808119 := by
  decide +kernel

private theorem r_808119 : RangeOk getRow 2051521 808119 808184 := by
  decide +kernel

private theorem r_808184 : RangeOk getRow 2051521 808184 808252 := by
  decide +kernel

private theorem s_806188 : RangeOk getRow 2051521 806123 806188 := r_806123
private theorem s_806254 : RangeOk getRow 2051521 806123 806254 :=
  s_806188.append (by norm_num) r_806188
private theorem s_806321 : RangeOk getRow 2051521 806123 806321 :=
  s_806254.append (by norm_num) r_806254
private theorem s_806387 : RangeOk getRow 2051521 806123 806387 :=
  s_806321.append (by norm_num) r_806321
private theorem s_806454 : RangeOk getRow 2051521 806123 806454 :=
  s_806387.append (by norm_num) r_806387
private theorem s_806518 : RangeOk getRow 2051521 806123 806518 :=
  s_806454.append (by norm_num) r_806454
private theorem s_806585 : RangeOk getRow 2051521 806123 806585 :=
  s_806518.append (by norm_num) r_806518
private theorem s_806652 : RangeOk getRow 2051521 806123 806652 :=
  s_806585.append (by norm_num) r_806585
private theorem s_806718 : RangeOk getRow 2051521 806123 806718 :=
  s_806652.append (by norm_num) r_806652
private theorem s_806783 : RangeOk getRow 2051521 806123 806783 :=
  s_806718.append (by norm_num) r_806718
private theorem s_806848 : RangeOk getRow 2051521 806123 806848 :=
  s_806783.append (by norm_num) r_806783
private theorem s_806913 : RangeOk getRow 2051521 806123 806913 :=
  s_806848.append (by norm_num) r_806848
private theorem s_806977 : RangeOk getRow 2051521 806123 806977 :=
  s_806913.append (by norm_num) r_806913
private theorem s_807045 : RangeOk getRow 2051521 806123 807045 :=
  s_806977.append (by norm_num) r_806977
private theorem s_807113 : RangeOk getRow 2051521 806123 807113 :=
  s_807045.append (by norm_num) r_807045
private theorem s_807181 : RangeOk getRow 2051521 806123 807181 :=
  s_807113.append (by norm_num) r_807113
private theorem s_807248 : RangeOk getRow 2051521 806123 807248 :=
  s_807181.append (by norm_num) r_807181
private theorem s_807315 : RangeOk getRow 2051521 806123 807315 :=
  s_807248.append (by norm_num) r_807248
private theorem s_807381 : RangeOk getRow 2051521 806123 807381 :=
  s_807315.append (by norm_num) r_807315
private theorem s_807446 : RangeOk getRow 2051521 806123 807446 :=
  s_807381.append (by norm_num) r_807381
private theorem s_807510 : RangeOk getRow 2051521 806123 807510 :=
  s_807446.append (by norm_num) r_807446
private theorem s_807578 : RangeOk getRow 2051521 806123 807578 :=
  s_807510.append (by norm_num) r_807510
private theorem s_807645 : RangeOk getRow 2051521 806123 807645 :=
  s_807578.append (by norm_num) r_807578
private theorem s_807714 : RangeOk getRow 2051521 806123 807714 :=
  s_807645.append (by norm_num) r_807645
private theorem s_807783 : RangeOk getRow 2051521 806123 807783 :=
  s_807714.append (by norm_num) r_807714
private theorem s_807852 : RangeOk getRow 2051521 806123 807852 :=
  s_807783.append (by norm_num) r_807783
private theorem s_807919 : RangeOk getRow 2051521 806123 807919 :=
  s_807852.append (by norm_num) r_807852
private theorem s_807985 : RangeOk getRow 2051521 806123 807985 :=
  s_807919.append (by norm_num) r_807919
private theorem s_808053 : RangeOk getRow 2051521 806123 808053 :=
  s_807985.append (by norm_num) r_807985
private theorem s_808119 : RangeOk getRow 2051521 806123 808119 :=
  s_808053.append (by norm_num) r_808053
private theorem s_808184 : RangeOk getRow 2051521 806123 808184 :=
  s_808119.append (by norm_num) r_808119
private theorem s_808252 : RangeOk getRow 2051521 806123 808252 :=
  s_808184.append (by norm_num) r_808184

/-- Rows `[806123, 808252)` are valid. -/
theorem rangeOk_806123_808252 : RangeOk getRow 2051521 806123 808252 := s_808252

end Noperthedron.Solution
