import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[235084, 237533). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_235084 : RangeOk getRow 2051521 235084 235152 := by
  decide +kernel

private theorem r_235152 : RangeOk getRow 2051521 235152 235219 := by
  decide +kernel

private theorem r_235219 : RangeOk getRow 2051521 235219 235288 := by
  decide +kernel

private theorem r_235288 : RangeOk getRow 2051521 235288 235356 := by
  decide +kernel

private theorem r_235356 : RangeOk getRow 2051521 235356 235421 := by
  decide +kernel

private theorem r_235421 : RangeOk getRow 2051521 235421 235487 := by
  decide +kernel

private theorem r_235487 : RangeOk getRow 2051521 235487 235553 := by
  decide +kernel

private theorem r_235553 : RangeOk getRow 2051521 235553 235621 := by
  decide +kernel

private theorem r_235621 : RangeOk getRow 2051521 235621 235690 := by
  decide +kernel

private theorem r_235690 : RangeOk getRow 2051521 235690 235760 := by
  decide +kernel

private theorem r_235760 : RangeOk getRow 2051521 235760 235829 := by
  decide +kernel

private theorem r_235829 : RangeOk getRow 2051521 235829 235897 := by
  decide +kernel

private theorem r_235897 : RangeOk getRow 2051521 235897 235964 := by
  decide +kernel

private theorem r_235964 : RangeOk getRow 2051521 235964 236032 := by
  decide +kernel

private theorem r_236032 : RangeOk getRow 2051521 236032 236098 := by
  decide +kernel

private theorem r_236098 : RangeOk getRow 2051521 236098 236165 := by
  decide +kernel

private theorem r_236165 : RangeOk getRow 2051521 236165 236234 := by
  decide +kernel

private theorem r_236234 : RangeOk getRow 2051521 236234 236304 := by
  decide +kernel

private theorem r_236304 : RangeOk getRow 2051521 236304 236374 := by
  decide +kernel

private theorem r_236374 : RangeOk getRow 2051521 236374 236442 := by
  decide +kernel

private theorem r_236442 : RangeOk getRow 2051521 236442 236511 := by
  decide +kernel

private theorem r_236511 : RangeOk getRow 2051521 236511 236580 := by
  decide +kernel

private theorem r_236580 : RangeOk getRow 2051521 236580 236648 := by
  decide +kernel

private theorem r_236648 : RangeOk getRow 2051521 236648 236716 := by
  decide +kernel

private theorem r_236716 : RangeOk getRow 2051521 236716 236785 := by
  decide +kernel

private theorem r_236785 : RangeOk getRow 2051521 236785 236855 := by
  decide +kernel

private theorem r_236855 : RangeOk getRow 2051521 236855 236923 := by
  decide +kernel

private theorem r_236923 : RangeOk getRow 2051521 236923 236990 := by
  decide +kernel

private theorem r_236990 : RangeOk getRow 2051521 236990 237058 := by
  decide +kernel

private theorem r_237058 : RangeOk getRow 2051521 237058 237126 := by
  decide +kernel

private theorem r_237126 : RangeOk getRow 2051521 237126 237193 := by
  decide +kernel

private theorem r_237193 : RangeOk getRow 2051521 237193 237262 := by
  decide +kernel

private theorem r_237262 : RangeOk getRow 2051521 237262 237332 := by
  decide +kernel

private theorem r_237332 : RangeOk getRow 2051521 237332 237400 := by
  decide +kernel

private theorem r_237400 : RangeOk getRow 2051521 237400 237466 := by
  decide +kernel

private theorem r_237466 : RangeOk getRow 2051521 237466 237533 := by
  decide +kernel

private theorem s_235152 : RangeOk getRow 2051521 235084 235152 := r_235084
private theorem s_235219 : RangeOk getRow 2051521 235084 235219 :=
  s_235152.append (by norm_num) r_235152
private theorem s_235288 : RangeOk getRow 2051521 235084 235288 :=
  s_235219.append (by norm_num) r_235219
private theorem s_235356 : RangeOk getRow 2051521 235084 235356 :=
  s_235288.append (by norm_num) r_235288
private theorem s_235421 : RangeOk getRow 2051521 235084 235421 :=
  s_235356.append (by norm_num) r_235356
private theorem s_235487 : RangeOk getRow 2051521 235084 235487 :=
  s_235421.append (by norm_num) r_235421
private theorem s_235553 : RangeOk getRow 2051521 235084 235553 :=
  s_235487.append (by norm_num) r_235487
private theorem s_235621 : RangeOk getRow 2051521 235084 235621 :=
  s_235553.append (by norm_num) r_235553
private theorem s_235690 : RangeOk getRow 2051521 235084 235690 :=
  s_235621.append (by norm_num) r_235621
private theorem s_235760 : RangeOk getRow 2051521 235084 235760 :=
  s_235690.append (by norm_num) r_235690
private theorem s_235829 : RangeOk getRow 2051521 235084 235829 :=
  s_235760.append (by norm_num) r_235760
private theorem s_235897 : RangeOk getRow 2051521 235084 235897 :=
  s_235829.append (by norm_num) r_235829
private theorem s_235964 : RangeOk getRow 2051521 235084 235964 :=
  s_235897.append (by norm_num) r_235897
private theorem s_236032 : RangeOk getRow 2051521 235084 236032 :=
  s_235964.append (by norm_num) r_235964
private theorem s_236098 : RangeOk getRow 2051521 235084 236098 :=
  s_236032.append (by norm_num) r_236032
private theorem s_236165 : RangeOk getRow 2051521 235084 236165 :=
  s_236098.append (by norm_num) r_236098
private theorem s_236234 : RangeOk getRow 2051521 235084 236234 :=
  s_236165.append (by norm_num) r_236165
private theorem s_236304 : RangeOk getRow 2051521 235084 236304 :=
  s_236234.append (by norm_num) r_236234
private theorem s_236374 : RangeOk getRow 2051521 235084 236374 :=
  s_236304.append (by norm_num) r_236304
private theorem s_236442 : RangeOk getRow 2051521 235084 236442 :=
  s_236374.append (by norm_num) r_236374
private theorem s_236511 : RangeOk getRow 2051521 235084 236511 :=
  s_236442.append (by norm_num) r_236442
private theorem s_236580 : RangeOk getRow 2051521 235084 236580 :=
  s_236511.append (by norm_num) r_236511
private theorem s_236648 : RangeOk getRow 2051521 235084 236648 :=
  s_236580.append (by norm_num) r_236580
private theorem s_236716 : RangeOk getRow 2051521 235084 236716 :=
  s_236648.append (by norm_num) r_236648
private theorem s_236785 : RangeOk getRow 2051521 235084 236785 :=
  s_236716.append (by norm_num) r_236716
private theorem s_236855 : RangeOk getRow 2051521 235084 236855 :=
  s_236785.append (by norm_num) r_236785
private theorem s_236923 : RangeOk getRow 2051521 235084 236923 :=
  s_236855.append (by norm_num) r_236855
private theorem s_236990 : RangeOk getRow 2051521 235084 236990 :=
  s_236923.append (by norm_num) r_236923
private theorem s_237058 : RangeOk getRow 2051521 235084 237058 :=
  s_236990.append (by norm_num) r_236990
private theorem s_237126 : RangeOk getRow 2051521 235084 237126 :=
  s_237058.append (by norm_num) r_237058
private theorem s_237193 : RangeOk getRow 2051521 235084 237193 :=
  s_237126.append (by norm_num) r_237126
private theorem s_237262 : RangeOk getRow 2051521 235084 237262 :=
  s_237193.append (by norm_num) r_237193
private theorem s_237332 : RangeOk getRow 2051521 235084 237332 :=
  s_237262.append (by norm_num) r_237262
private theorem s_237400 : RangeOk getRow 2051521 235084 237400 :=
  s_237332.append (by norm_num) r_237332
private theorem s_237466 : RangeOk getRow 2051521 235084 237466 :=
  s_237400.append (by norm_num) r_237400
private theorem s_237533 : RangeOk getRow 2051521 235084 237533 :=
  s_237466.append (by norm_num) r_237466

/-- Rows `[235084, 237533)` are valid. -/
theorem rangeOk_235084_237533 : RangeOk getRow 2051521 235084 237533 := s_237533

end Noperthedron.Solution
