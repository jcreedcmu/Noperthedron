import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[187987, 189715). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_187987 : RangeOk getRow 2051521 187987 188051 := by
  decide +kernel

private theorem r_188051 : RangeOk getRow 2051521 188051 188115 := by
  decide +kernel

private theorem r_188115 : RangeOk getRow 2051521 188115 188179 := by
  decide +kernel

private theorem r_188179 : RangeOk getRow 2051521 188179 188243 := by
  decide +kernel

private theorem r_188243 : RangeOk getRow 2051521 188243 188307 := by
  decide +kernel

private theorem r_188307 : RangeOk getRow 2051521 188307 188371 := by
  decide +kernel

private theorem r_188371 : RangeOk getRow 2051521 188371 188435 := by
  decide +kernel

private theorem r_188435 : RangeOk getRow 2051521 188435 188499 := by
  decide +kernel

private theorem r_188499 : RangeOk getRow 2051521 188499 188563 := by
  decide +kernel

private theorem r_188563 : RangeOk getRow 2051521 188563 188627 := by
  decide +kernel

private theorem r_188627 : RangeOk getRow 2051521 188627 188691 := by
  decide +kernel

private theorem r_188691 : RangeOk getRow 2051521 188691 188755 := by
  decide +kernel

private theorem r_188755 : RangeOk getRow 2051521 188755 188819 := by
  decide +kernel

private theorem r_188819 : RangeOk getRow 2051521 188819 188883 := by
  decide +kernel

private theorem r_188883 : RangeOk getRow 2051521 188883 188947 := by
  decide +kernel

private theorem r_188947 : RangeOk getRow 2051521 188947 189011 := by
  decide +kernel

private theorem r_189011 : RangeOk getRow 2051521 189011 189075 := by
  decide +kernel

private theorem r_189075 : RangeOk getRow 2051521 189075 189139 := by
  decide +kernel

private theorem r_189139 : RangeOk getRow 2051521 189139 189203 := by
  decide +kernel

private theorem r_189203 : RangeOk getRow 2051521 189203 189267 := by
  decide +kernel

private theorem r_189267 : RangeOk getRow 2051521 189267 189331 := by
  decide +kernel

private theorem r_189331 : RangeOk getRow 2051521 189331 189395 := by
  decide +kernel

private theorem r_189395 : RangeOk getRow 2051521 189395 189459 := by
  decide +kernel

private theorem r_189459 : RangeOk getRow 2051521 189459 189523 := by
  decide +kernel

private theorem r_189523 : RangeOk getRow 2051521 189523 189587 := by
  decide +kernel

private theorem r_189587 : RangeOk getRow 2051521 189587 189651 := by
  decide +kernel

private theorem r_189651 : RangeOk getRow 2051521 189651 189715 := by
  decide +kernel

private theorem s_188051 : RangeOk getRow 2051521 187987 188051 := r_187987
private theorem s_188115 : RangeOk getRow 2051521 187987 188115 :=
  s_188051.append (by norm_num) r_188051
private theorem s_188179 : RangeOk getRow 2051521 187987 188179 :=
  s_188115.append (by norm_num) r_188115
private theorem s_188243 : RangeOk getRow 2051521 187987 188243 :=
  s_188179.append (by norm_num) r_188179
private theorem s_188307 : RangeOk getRow 2051521 187987 188307 :=
  s_188243.append (by norm_num) r_188243
private theorem s_188371 : RangeOk getRow 2051521 187987 188371 :=
  s_188307.append (by norm_num) r_188307
private theorem s_188435 : RangeOk getRow 2051521 187987 188435 :=
  s_188371.append (by norm_num) r_188371
private theorem s_188499 : RangeOk getRow 2051521 187987 188499 :=
  s_188435.append (by norm_num) r_188435
private theorem s_188563 : RangeOk getRow 2051521 187987 188563 :=
  s_188499.append (by norm_num) r_188499
private theorem s_188627 : RangeOk getRow 2051521 187987 188627 :=
  s_188563.append (by norm_num) r_188563
private theorem s_188691 : RangeOk getRow 2051521 187987 188691 :=
  s_188627.append (by norm_num) r_188627
private theorem s_188755 : RangeOk getRow 2051521 187987 188755 :=
  s_188691.append (by norm_num) r_188691
private theorem s_188819 : RangeOk getRow 2051521 187987 188819 :=
  s_188755.append (by norm_num) r_188755
private theorem s_188883 : RangeOk getRow 2051521 187987 188883 :=
  s_188819.append (by norm_num) r_188819
private theorem s_188947 : RangeOk getRow 2051521 187987 188947 :=
  s_188883.append (by norm_num) r_188883
private theorem s_189011 : RangeOk getRow 2051521 187987 189011 :=
  s_188947.append (by norm_num) r_188947
private theorem s_189075 : RangeOk getRow 2051521 187987 189075 :=
  s_189011.append (by norm_num) r_189011
private theorem s_189139 : RangeOk getRow 2051521 187987 189139 :=
  s_189075.append (by norm_num) r_189075
private theorem s_189203 : RangeOk getRow 2051521 187987 189203 :=
  s_189139.append (by norm_num) r_189139
private theorem s_189267 : RangeOk getRow 2051521 187987 189267 :=
  s_189203.append (by norm_num) r_189203
private theorem s_189331 : RangeOk getRow 2051521 187987 189331 :=
  s_189267.append (by norm_num) r_189267
private theorem s_189395 : RangeOk getRow 2051521 187987 189395 :=
  s_189331.append (by norm_num) r_189331
private theorem s_189459 : RangeOk getRow 2051521 187987 189459 :=
  s_189395.append (by norm_num) r_189395
private theorem s_189523 : RangeOk getRow 2051521 187987 189523 :=
  s_189459.append (by norm_num) r_189459
private theorem s_189587 : RangeOk getRow 2051521 187987 189587 :=
  s_189523.append (by norm_num) r_189523
private theorem s_189651 : RangeOk getRow 2051521 187987 189651 :=
  s_189587.append (by norm_num) r_189587
private theorem s_189715 : RangeOk getRow 2051521 187987 189715 :=
  s_189651.append (by norm_num) r_189651

/-- Rows `[187987, 189715)` are valid. -/
theorem rangeOk_187987_189715 : RangeOk getRow 2051521 187987 189715 := s_189715

end Noperthedron.Solution
