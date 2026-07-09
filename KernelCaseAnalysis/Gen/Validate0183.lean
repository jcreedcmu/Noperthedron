import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[440118, 442381). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_440118 : RangeOk getRow 2051521 440118 440187 := by
  decide +kernel

private theorem r_440187 : RangeOk getRow 2051521 440187 440256 := by
  decide +kernel

private theorem r_440256 : RangeOk getRow 2051521 440256 440325 := by
  decide +kernel

private theorem r_440325 : RangeOk getRow 2051521 440325 440395 := by
  decide +kernel

private theorem r_440395 : RangeOk getRow 2051521 440395 440464 := by
  decide +kernel

private theorem r_440464 : RangeOk getRow 2051521 440464 440532 := by
  decide +kernel

private theorem r_440532 : RangeOk getRow 2051521 440532 440601 := by
  decide +kernel

private theorem r_440601 : RangeOk getRow 2051521 440601 440670 := by
  decide +kernel

private theorem r_440670 : RangeOk getRow 2051521 440670 440739 := by
  decide +kernel

private theorem r_440739 : RangeOk getRow 2051521 440739 440805 := by
  decide +kernel

private theorem r_440805 : RangeOk getRow 2051521 440805 440874 := by
  decide +kernel

private theorem r_440874 : RangeOk getRow 2051521 440874 440944 := by
  decide +kernel

private theorem r_440944 : RangeOk getRow 2051521 440944 441014 := by
  decide +kernel

private theorem r_441014 : RangeOk getRow 2051521 441014 441083 := by
  decide +kernel

private theorem r_441083 : RangeOk getRow 2051521 441083 441153 := by
  decide +kernel

private theorem r_441153 : RangeOk getRow 2051521 441153 441220 := by
  decide +kernel

private theorem r_441220 : RangeOk getRow 2051521 441220 441291 := by
  decide +kernel

private theorem r_441291 : RangeOk getRow 2051521 441291 441358 := by
  decide +kernel

private theorem r_441358 : RangeOk getRow 2051521 441358 441425 := by
  decide +kernel

private theorem r_441425 : RangeOk getRow 2051521 441425 441493 := by
  decide +kernel

private theorem r_441493 : RangeOk getRow 2051521 441493 441561 := by
  decide +kernel

private theorem r_441561 : RangeOk getRow 2051521 441561 441631 := by
  decide +kernel

private theorem r_441631 : RangeOk getRow 2051521 441631 441696 := by
  decide +kernel

private theorem r_441696 : RangeOk getRow 2051521 441696 441760 := by
  decide +kernel

private theorem r_441760 : RangeOk getRow 2051521 441760 441824 := by
  decide +kernel

private theorem r_441824 : RangeOk getRow 2051521 441824 441890 := by
  decide +kernel

private theorem r_441890 : RangeOk getRow 2051521 441890 441955 := by
  decide +kernel

private theorem r_441955 : RangeOk getRow 2051521 441955 442019 := by
  decide +kernel

private theorem r_442019 : RangeOk getRow 2051521 442019 442083 := by
  decide +kernel

private theorem r_442083 : RangeOk getRow 2051521 442083 442147 := by
  decide +kernel

private theorem r_442147 : RangeOk getRow 2051521 442147 442198 := by
  decide +kernel

private theorem r_442198 : RangeOk getRow 2051521 442198 442257 := by
  decide +kernel

private theorem r_442257 : RangeOk getRow 2051521 442257 442316 := by
  decide +kernel

private theorem r_442316 : RangeOk getRow 2051521 442316 442381 := by
  decide +kernel

private theorem s_440187 : RangeOk getRow 2051521 440118 440187 := r_440118
private theorem s_440256 : RangeOk getRow 2051521 440118 440256 :=
  s_440187.append (by norm_num) r_440187
private theorem s_440325 : RangeOk getRow 2051521 440118 440325 :=
  s_440256.append (by norm_num) r_440256
private theorem s_440395 : RangeOk getRow 2051521 440118 440395 :=
  s_440325.append (by norm_num) r_440325
private theorem s_440464 : RangeOk getRow 2051521 440118 440464 :=
  s_440395.append (by norm_num) r_440395
private theorem s_440532 : RangeOk getRow 2051521 440118 440532 :=
  s_440464.append (by norm_num) r_440464
private theorem s_440601 : RangeOk getRow 2051521 440118 440601 :=
  s_440532.append (by norm_num) r_440532
private theorem s_440670 : RangeOk getRow 2051521 440118 440670 :=
  s_440601.append (by norm_num) r_440601
private theorem s_440739 : RangeOk getRow 2051521 440118 440739 :=
  s_440670.append (by norm_num) r_440670
private theorem s_440805 : RangeOk getRow 2051521 440118 440805 :=
  s_440739.append (by norm_num) r_440739
private theorem s_440874 : RangeOk getRow 2051521 440118 440874 :=
  s_440805.append (by norm_num) r_440805
private theorem s_440944 : RangeOk getRow 2051521 440118 440944 :=
  s_440874.append (by norm_num) r_440874
private theorem s_441014 : RangeOk getRow 2051521 440118 441014 :=
  s_440944.append (by norm_num) r_440944
private theorem s_441083 : RangeOk getRow 2051521 440118 441083 :=
  s_441014.append (by norm_num) r_441014
private theorem s_441153 : RangeOk getRow 2051521 440118 441153 :=
  s_441083.append (by norm_num) r_441083
private theorem s_441220 : RangeOk getRow 2051521 440118 441220 :=
  s_441153.append (by norm_num) r_441153
private theorem s_441291 : RangeOk getRow 2051521 440118 441291 :=
  s_441220.append (by norm_num) r_441220
private theorem s_441358 : RangeOk getRow 2051521 440118 441358 :=
  s_441291.append (by norm_num) r_441291
private theorem s_441425 : RangeOk getRow 2051521 440118 441425 :=
  s_441358.append (by norm_num) r_441358
private theorem s_441493 : RangeOk getRow 2051521 440118 441493 :=
  s_441425.append (by norm_num) r_441425
private theorem s_441561 : RangeOk getRow 2051521 440118 441561 :=
  s_441493.append (by norm_num) r_441493
private theorem s_441631 : RangeOk getRow 2051521 440118 441631 :=
  s_441561.append (by norm_num) r_441561
private theorem s_441696 : RangeOk getRow 2051521 440118 441696 :=
  s_441631.append (by norm_num) r_441631
private theorem s_441760 : RangeOk getRow 2051521 440118 441760 :=
  s_441696.append (by norm_num) r_441696
private theorem s_441824 : RangeOk getRow 2051521 440118 441824 :=
  s_441760.append (by norm_num) r_441760
private theorem s_441890 : RangeOk getRow 2051521 440118 441890 :=
  s_441824.append (by norm_num) r_441824
private theorem s_441955 : RangeOk getRow 2051521 440118 441955 :=
  s_441890.append (by norm_num) r_441890
private theorem s_442019 : RangeOk getRow 2051521 440118 442019 :=
  s_441955.append (by norm_num) r_441955
private theorem s_442083 : RangeOk getRow 2051521 440118 442083 :=
  s_442019.append (by norm_num) r_442019
private theorem s_442147 : RangeOk getRow 2051521 440118 442147 :=
  s_442083.append (by norm_num) r_442083
private theorem s_442198 : RangeOk getRow 2051521 440118 442198 :=
  s_442147.append (by norm_num) r_442147
private theorem s_442257 : RangeOk getRow 2051521 440118 442257 :=
  s_442198.append (by norm_num) r_442198
private theorem s_442316 : RangeOk getRow 2051521 440118 442316 :=
  s_442257.append (by norm_num) r_442257
private theorem s_442381 : RangeOk getRow 2051521 440118 442381 :=
  s_442316.append (by norm_num) r_442316

/-- Rows `[440118, 442381)` are valid. -/
theorem rangeOk_440118_442381 : RangeOk getRow 2051521 440118 442381 := s_442381

end Noperthedron.Solution
