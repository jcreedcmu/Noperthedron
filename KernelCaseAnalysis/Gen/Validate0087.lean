import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[193239, 194968). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_193239 : RangeOk getRow 2051521 193239 193303 := by
  decide +kernel

private theorem r_193303 : RangeOk getRow 2051521 193303 193367 := by
  decide +kernel

private theorem r_193367 : RangeOk getRow 2051521 193367 193431 := by
  decide +kernel

private theorem r_193431 : RangeOk getRow 2051521 193431 193495 := by
  decide +kernel

private theorem r_193495 : RangeOk getRow 2051521 193495 193559 := by
  decide +kernel

private theorem r_193559 : RangeOk getRow 2051521 193559 193623 := by
  decide +kernel

private theorem r_193623 : RangeOk getRow 2051521 193623 193687 := by
  decide +kernel

private theorem r_193687 : RangeOk getRow 2051521 193687 193751 := by
  decide +kernel

private theorem r_193751 : RangeOk getRow 2051521 193751 193815 := by
  decide +kernel

private theorem r_193815 : RangeOk getRow 2051521 193815 193879 := by
  decide +kernel

private theorem r_193879 : RangeOk getRow 2051521 193879 193943 := by
  decide +kernel

private theorem r_193943 : RangeOk getRow 2051521 193943 194007 := by
  decide +kernel

private theorem r_194007 : RangeOk getRow 2051521 194007 194071 := by
  decide +kernel

private theorem r_194071 : RangeOk getRow 2051521 194071 194135 := by
  decide +kernel

private theorem r_194135 : RangeOk getRow 2051521 194135 194199 := by
  decide +kernel

private theorem r_194199 : RangeOk getRow 2051521 194199 194263 := by
  decide +kernel

private theorem r_194263 : RangeOk getRow 2051521 194263 194327 := by
  decide +kernel

private theorem r_194327 : RangeOk getRow 2051521 194327 194391 := by
  decide +kernel

private theorem r_194391 : RangeOk getRow 2051521 194391 194456 := by
  decide +kernel

private theorem r_194456 : RangeOk getRow 2051521 194456 194520 := by
  decide +kernel

private theorem r_194520 : RangeOk getRow 2051521 194520 194584 := by
  decide +kernel

private theorem r_194584 : RangeOk getRow 2051521 194584 194648 := by
  decide +kernel

private theorem r_194648 : RangeOk getRow 2051521 194648 194712 := by
  decide +kernel

private theorem r_194712 : RangeOk getRow 2051521 194712 194776 := by
  decide +kernel

private theorem r_194776 : RangeOk getRow 2051521 194776 194840 := by
  decide +kernel

private theorem r_194840 : RangeOk getRow 2051521 194840 194904 := by
  decide +kernel

private theorem r_194904 : RangeOk getRow 2051521 194904 194968 := by
  decide +kernel

private theorem s_193303 : RangeOk getRow 2051521 193239 193303 := r_193239
private theorem s_193367 : RangeOk getRow 2051521 193239 193367 :=
  s_193303.append (by norm_num) r_193303
private theorem s_193431 : RangeOk getRow 2051521 193239 193431 :=
  s_193367.append (by norm_num) r_193367
private theorem s_193495 : RangeOk getRow 2051521 193239 193495 :=
  s_193431.append (by norm_num) r_193431
private theorem s_193559 : RangeOk getRow 2051521 193239 193559 :=
  s_193495.append (by norm_num) r_193495
private theorem s_193623 : RangeOk getRow 2051521 193239 193623 :=
  s_193559.append (by norm_num) r_193559
private theorem s_193687 : RangeOk getRow 2051521 193239 193687 :=
  s_193623.append (by norm_num) r_193623
private theorem s_193751 : RangeOk getRow 2051521 193239 193751 :=
  s_193687.append (by norm_num) r_193687
private theorem s_193815 : RangeOk getRow 2051521 193239 193815 :=
  s_193751.append (by norm_num) r_193751
private theorem s_193879 : RangeOk getRow 2051521 193239 193879 :=
  s_193815.append (by norm_num) r_193815
private theorem s_193943 : RangeOk getRow 2051521 193239 193943 :=
  s_193879.append (by norm_num) r_193879
private theorem s_194007 : RangeOk getRow 2051521 193239 194007 :=
  s_193943.append (by norm_num) r_193943
private theorem s_194071 : RangeOk getRow 2051521 193239 194071 :=
  s_194007.append (by norm_num) r_194007
private theorem s_194135 : RangeOk getRow 2051521 193239 194135 :=
  s_194071.append (by norm_num) r_194071
private theorem s_194199 : RangeOk getRow 2051521 193239 194199 :=
  s_194135.append (by norm_num) r_194135
private theorem s_194263 : RangeOk getRow 2051521 193239 194263 :=
  s_194199.append (by norm_num) r_194199
private theorem s_194327 : RangeOk getRow 2051521 193239 194327 :=
  s_194263.append (by norm_num) r_194263
private theorem s_194391 : RangeOk getRow 2051521 193239 194391 :=
  s_194327.append (by norm_num) r_194327
private theorem s_194456 : RangeOk getRow 2051521 193239 194456 :=
  s_194391.append (by norm_num) r_194391
private theorem s_194520 : RangeOk getRow 2051521 193239 194520 :=
  s_194456.append (by norm_num) r_194456
private theorem s_194584 : RangeOk getRow 2051521 193239 194584 :=
  s_194520.append (by norm_num) r_194520
private theorem s_194648 : RangeOk getRow 2051521 193239 194648 :=
  s_194584.append (by norm_num) r_194584
private theorem s_194712 : RangeOk getRow 2051521 193239 194712 :=
  s_194648.append (by norm_num) r_194648
private theorem s_194776 : RangeOk getRow 2051521 193239 194776 :=
  s_194712.append (by norm_num) r_194712
private theorem s_194840 : RangeOk getRow 2051521 193239 194840 :=
  s_194776.append (by norm_num) r_194776
private theorem s_194904 : RangeOk getRow 2051521 193239 194904 :=
  s_194840.append (by norm_num) r_194840
private theorem s_194968 : RangeOk getRow 2051521 193239 194968 :=
  s_194904.append (by norm_num) r_194904

/-- Rows `[193239, 194968)` are valid. -/
theorem rangeOk_193239_194968 : RangeOk getRow 2051521 193239 194968 := s_194968

end Noperthedron.Solution
