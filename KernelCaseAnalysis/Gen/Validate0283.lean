import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[683118, 685335). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_683118 : RangeOk getRow 2051521 683118 683187 := by
  decide +kernel

private theorem r_683187 : RangeOk getRow 2051521 683187 683255 := by
  decide +kernel

private theorem r_683255 : RangeOk getRow 2051521 683255 683320 := by
  decide +kernel

private theorem r_683320 : RangeOk getRow 2051521 683320 683387 := by
  decide +kernel

private theorem r_683387 : RangeOk getRow 2051521 683387 683454 := by
  decide +kernel

private theorem r_683454 : RangeOk getRow 2051521 683454 683522 := by
  decide +kernel

private theorem r_683522 : RangeOk getRow 2051521 683522 683591 := by
  decide +kernel

private theorem r_683591 : RangeOk getRow 2051521 683591 683659 := by
  decide +kernel

private theorem r_683659 : RangeOk getRow 2051521 683659 683727 := by
  decide +kernel

private theorem r_683727 : RangeOk getRow 2051521 683727 683795 := by
  decide +kernel

private theorem r_683795 : RangeOk getRow 2051521 683795 683860 := by
  decide +kernel

private theorem r_683860 : RangeOk getRow 2051521 683860 683926 := by
  decide +kernel

private theorem r_683926 : RangeOk getRow 2051521 683926 683995 := by
  decide +kernel

private theorem r_683995 : RangeOk getRow 2051521 683995 684064 := by
  decide +kernel

private theorem r_684064 : RangeOk getRow 2051521 684064 684131 := by
  decide +kernel

private theorem r_684131 : RangeOk getRow 2051521 684131 684198 := by
  decide +kernel

private theorem r_684198 : RangeOk getRow 2051521 684198 684264 := by
  decide +kernel

private theorem r_684264 : RangeOk getRow 2051521 684264 684331 := by
  decide +kernel

private theorem r_684331 : RangeOk getRow 2051521 684331 684398 := by
  decide +kernel

private theorem r_684398 : RangeOk getRow 2051521 684398 684465 := by
  decide +kernel

private theorem r_684465 : RangeOk getRow 2051521 684465 684531 := by
  decide +kernel

private theorem r_684531 : RangeOk getRow 2051521 684531 684596 := by
  decide +kernel

private theorem r_684596 : RangeOk getRow 2051521 684596 684663 := by
  decide +kernel

private theorem r_684663 : RangeOk getRow 2051521 684663 684731 := by
  decide +kernel

private theorem r_684731 : RangeOk getRow 2051521 684731 684799 := by
  decide +kernel

private theorem r_684799 : RangeOk getRow 2051521 684799 684867 := by
  decide +kernel

private theorem r_684867 : RangeOk getRow 2051521 684867 684934 := by
  decide +kernel

private theorem r_684934 : RangeOk getRow 2051521 684934 685002 := by
  decide +kernel

private theorem r_685002 : RangeOk getRow 2051521 685002 685068 := by
  decide +kernel

private theorem r_685068 : RangeOk getRow 2051521 685068 685135 := by
  decide +kernel

private theorem r_685135 : RangeOk getRow 2051521 685135 685200 := by
  decide +kernel

private theorem r_685200 : RangeOk getRow 2051521 685200 685268 := by
  decide +kernel

private theorem r_685268 : RangeOk getRow 2051521 685268 685335 := by
  decide +kernel

private theorem s_683187 : RangeOk getRow 2051521 683118 683187 := r_683118
private theorem s_683255 : RangeOk getRow 2051521 683118 683255 :=
  s_683187.append (by norm_num) r_683187
private theorem s_683320 : RangeOk getRow 2051521 683118 683320 :=
  s_683255.append (by norm_num) r_683255
private theorem s_683387 : RangeOk getRow 2051521 683118 683387 :=
  s_683320.append (by norm_num) r_683320
private theorem s_683454 : RangeOk getRow 2051521 683118 683454 :=
  s_683387.append (by norm_num) r_683387
private theorem s_683522 : RangeOk getRow 2051521 683118 683522 :=
  s_683454.append (by norm_num) r_683454
private theorem s_683591 : RangeOk getRow 2051521 683118 683591 :=
  s_683522.append (by norm_num) r_683522
private theorem s_683659 : RangeOk getRow 2051521 683118 683659 :=
  s_683591.append (by norm_num) r_683591
private theorem s_683727 : RangeOk getRow 2051521 683118 683727 :=
  s_683659.append (by norm_num) r_683659
private theorem s_683795 : RangeOk getRow 2051521 683118 683795 :=
  s_683727.append (by norm_num) r_683727
private theorem s_683860 : RangeOk getRow 2051521 683118 683860 :=
  s_683795.append (by norm_num) r_683795
private theorem s_683926 : RangeOk getRow 2051521 683118 683926 :=
  s_683860.append (by norm_num) r_683860
private theorem s_683995 : RangeOk getRow 2051521 683118 683995 :=
  s_683926.append (by norm_num) r_683926
private theorem s_684064 : RangeOk getRow 2051521 683118 684064 :=
  s_683995.append (by norm_num) r_683995
private theorem s_684131 : RangeOk getRow 2051521 683118 684131 :=
  s_684064.append (by norm_num) r_684064
private theorem s_684198 : RangeOk getRow 2051521 683118 684198 :=
  s_684131.append (by norm_num) r_684131
private theorem s_684264 : RangeOk getRow 2051521 683118 684264 :=
  s_684198.append (by norm_num) r_684198
private theorem s_684331 : RangeOk getRow 2051521 683118 684331 :=
  s_684264.append (by norm_num) r_684264
private theorem s_684398 : RangeOk getRow 2051521 683118 684398 :=
  s_684331.append (by norm_num) r_684331
private theorem s_684465 : RangeOk getRow 2051521 683118 684465 :=
  s_684398.append (by norm_num) r_684398
private theorem s_684531 : RangeOk getRow 2051521 683118 684531 :=
  s_684465.append (by norm_num) r_684465
private theorem s_684596 : RangeOk getRow 2051521 683118 684596 :=
  s_684531.append (by norm_num) r_684531
private theorem s_684663 : RangeOk getRow 2051521 683118 684663 :=
  s_684596.append (by norm_num) r_684596
private theorem s_684731 : RangeOk getRow 2051521 683118 684731 :=
  s_684663.append (by norm_num) r_684663
private theorem s_684799 : RangeOk getRow 2051521 683118 684799 :=
  s_684731.append (by norm_num) r_684731
private theorem s_684867 : RangeOk getRow 2051521 683118 684867 :=
  s_684799.append (by norm_num) r_684799
private theorem s_684934 : RangeOk getRow 2051521 683118 684934 :=
  s_684867.append (by norm_num) r_684867
private theorem s_685002 : RangeOk getRow 2051521 683118 685002 :=
  s_684934.append (by norm_num) r_684934
private theorem s_685068 : RangeOk getRow 2051521 683118 685068 :=
  s_685002.append (by norm_num) r_685002
private theorem s_685135 : RangeOk getRow 2051521 683118 685135 :=
  s_685068.append (by norm_num) r_685068
private theorem s_685200 : RangeOk getRow 2051521 683118 685200 :=
  s_685135.append (by norm_num) r_685135
private theorem s_685268 : RangeOk getRow 2051521 683118 685268 :=
  s_685200.append (by norm_num) r_685200
private theorem s_685335 : RangeOk getRow 2051521 683118 685335 :=
  s_685268.append (by norm_num) r_685268

/-- Rows `[683118, 685335)` are valid. -/
theorem rangeOk_683118_685335 : RangeOk getRow 2051521 683118 685335 := s_685335

end Noperthedron.Solution
