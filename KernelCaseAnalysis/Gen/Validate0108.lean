module

public import KernelCaseAnalysis.Gen.Dispatch

@[expose] public section

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[2049380, 2051521). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_2049380 : RangeOk getRow 2051521 2049380 2049575 := by
  decide +kernel

private theorem r_2049575 : RangeOk getRow 2051521 2049575 2049849 := by
  decide +kernel

private theorem r_2049849 : RangeOk getRow 2051521 2049849 2050044 := by
  decide +kernel

private theorem r_2050044 : RangeOk getRow 2051521 2050044 2050198 := by
  decide +kernel

private theorem r_2050198 : RangeOk getRow 2051521 2050198 2050276 := by
  decide +kernel

private theorem r_2050276 : RangeOk getRow 2051521 2050276 2050319 := by
  decide +kernel

private theorem r_2050319 : RangeOk getRow 2051521 2050319 2050379 := by
  decide +kernel

private theorem r_2050379 : RangeOk getRow 2051521 2050379 2050428 := by
  decide +kernel

private theorem r_2050428 : RangeOk getRow 2051521 2050428 2050474 := by
  decide +kernel

private theorem r_2050474 : RangeOk getRow 2051521 2050474 2050514 := by
  decide +kernel

private theorem r_2050514 : RangeOk getRow 2051521 2050514 2050565 := by
  decide +kernel

private theorem r_2050565 : RangeOk getRow 2051521 2050565 2050613 := by
  decide +kernel

private theorem r_2050613 : RangeOk getRow 2051521 2050613 2050673 := by
  decide +kernel

private theorem r_2050673 : RangeOk getRow 2051521 2050673 2050727 := by
  decide +kernel

private theorem r_2050727 : RangeOk getRow 2051521 2050727 2050779 := by
  decide +kernel

private theorem r_2050779 : RangeOk getRow 2051521 2050779 2050826 := by
  decide +kernel

private theorem r_2050826 : RangeOk getRow 2051521 2050826 2050880 := by
  decide +kernel

private theorem r_2050880 : RangeOk getRow 2051521 2050880 2050926 := by
  decide +kernel

private theorem r_2050926 : RangeOk getRow 2051521 2050926 2050977 := by
  decide +kernel

private theorem r_2050977 : RangeOk getRow 2051521 2050977 2051049 := by
  decide +kernel

private theorem r_2051049 : RangeOk getRow 2051521 2051049 2051241 := by
  decide +kernel

private theorem r_2051241 : RangeOk getRow 2051521 2051241 2051403 := by
  decide +kernel

private theorem r_2051403 : RangeOk getRow 2051521 2051403 2051445 := by
  decide +kernel

private theorem r_2051445 : RangeOk getRow 2051521 2051445 2051491 := by
  decide +kernel

private theorem r_2051491 : RangeOk getRow 2051521 2051491 2051521 := by
  decide +kernel

private theorem s_2049575 : RangeOk getRow 2051521 2049380 2049575 := r_2049380
private theorem s_2049849 : RangeOk getRow 2051521 2049380 2049849 :=
  s_2049575.append (by norm_num) r_2049575
private theorem s_2050044 : RangeOk getRow 2051521 2049380 2050044 :=
  s_2049849.append (by norm_num) r_2049849
private theorem s_2050198 : RangeOk getRow 2051521 2049380 2050198 :=
  s_2050044.append (by norm_num) r_2050044
private theorem s_2050276 : RangeOk getRow 2051521 2049380 2050276 :=
  s_2050198.append (by norm_num) r_2050198
private theorem s_2050319 : RangeOk getRow 2051521 2049380 2050319 :=
  s_2050276.append (by norm_num) r_2050276
private theorem s_2050379 : RangeOk getRow 2051521 2049380 2050379 :=
  s_2050319.append (by norm_num) r_2050319
private theorem s_2050428 : RangeOk getRow 2051521 2049380 2050428 :=
  s_2050379.append (by norm_num) r_2050379
private theorem s_2050474 : RangeOk getRow 2051521 2049380 2050474 :=
  s_2050428.append (by norm_num) r_2050428
private theorem s_2050514 : RangeOk getRow 2051521 2049380 2050514 :=
  s_2050474.append (by norm_num) r_2050474
private theorem s_2050565 : RangeOk getRow 2051521 2049380 2050565 :=
  s_2050514.append (by norm_num) r_2050514
private theorem s_2050613 : RangeOk getRow 2051521 2049380 2050613 :=
  s_2050565.append (by norm_num) r_2050565
private theorem s_2050673 : RangeOk getRow 2051521 2049380 2050673 :=
  s_2050613.append (by norm_num) r_2050613
private theorem s_2050727 : RangeOk getRow 2051521 2049380 2050727 :=
  s_2050673.append (by norm_num) r_2050673
private theorem s_2050779 : RangeOk getRow 2051521 2049380 2050779 :=
  s_2050727.append (by norm_num) r_2050727
private theorem s_2050826 : RangeOk getRow 2051521 2049380 2050826 :=
  s_2050779.append (by norm_num) r_2050779
private theorem s_2050880 : RangeOk getRow 2051521 2049380 2050880 :=
  s_2050826.append (by norm_num) r_2050826
private theorem s_2050926 : RangeOk getRow 2051521 2049380 2050926 :=
  s_2050880.append (by norm_num) r_2050880
private theorem s_2050977 : RangeOk getRow 2051521 2049380 2050977 :=
  s_2050926.append (by norm_num) r_2050926
private theorem s_2051049 : RangeOk getRow 2051521 2049380 2051049 :=
  s_2050977.append (by norm_num) r_2050977
private theorem s_2051241 : RangeOk getRow 2051521 2049380 2051241 :=
  s_2051049.append (by norm_num) r_2051049
private theorem s_2051403 : RangeOk getRow 2051521 2049380 2051403 :=
  s_2051241.append (by norm_num) r_2051241
private theorem s_2051445 : RangeOk getRow 2051521 2049380 2051445 :=
  s_2051403.append (by norm_num) r_2051403
private theorem s_2051491 : RangeOk getRow 2051521 2049380 2051491 :=
  s_2051445.append (by norm_num) r_2051445
private theorem s_2051521 : RangeOk getRow 2051521 2049380 2051521 :=
  s_2051491.append (by norm_num) r_2051491

/-- Rows `[2049380, 2051521)` are valid. -/
theorem rangeOk_2049380_2051521 : RangeOk getRow 2051521 2049380 2051521 := s_2051521

end Noperthedron.Solution

end
