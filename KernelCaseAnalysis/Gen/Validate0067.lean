import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[145925, 147640). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_145925 : RangeOk getRow 2051521 145925 145989 := by
  decide +kernel

private theorem r_145989 : RangeOk getRow 2051521 145989 146053 := by
  decide +kernel

private theorem r_146053 : RangeOk getRow 2051521 146053 146117 := by
  decide +kernel

private theorem r_146117 : RangeOk getRow 2051521 146117 146181 := by
  decide +kernel

private theorem r_146181 : RangeOk getRow 2051521 146181 146245 := by
  decide +kernel

private theorem r_146245 : RangeOk getRow 2051521 146245 146309 := by
  decide +kernel

private theorem r_146309 : RangeOk getRow 2051521 146309 146373 := by
  decide +kernel

private theorem r_146373 : RangeOk getRow 2051521 146373 146437 := by
  decide +kernel

private theorem r_146437 : RangeOk getRow 2051521 146437 146501 := by
  decide +kernel

private theorem r_146501 : RangeOk getRow 2051521 146501 146565 := by
  decide +kernel

private theorem r_146565 : RangeOk getRow 2051521 146565 146629 := by
  decide +kernel

private theorem r_146629 : RangeOk getRow 2051521 146629 146693 := by
  decide +kernel

private theorem r_146693 : RangeOk getRow 2051521 146693 146757 := by
  decide +kernel

private theorem r_146757 : RangeOk getRow 2051521 146757 146821 := by
  decide +kernel

private theorem r_146821 : RangeOk getRow 2051521 146821 146885 := by
  decide +kernel

private theorem r_146885 : RangeOk getRow 2051521 146885 146949 := by
  decide +kernel

private theorem r_146949 : RangeOk getRow 2051521 146949 147013 := by
  decide +kernel

private theorem r_147013 : RangeOk getRow 2051521 147013 147077 := by
  decide +kernel

private theorem r_147077 : RangeOk getRow 2051521 147077 147141 := by
  decide +kernel

private theorem r_147141 : RangeOk getRow 2051521 147141 147201 := by
  decide +kernel

private theorem r_147201 : RangeOk getRow 2051521 147201 147256 := by
  decide +kernel

private theorem r_147256 : RangeOk getRow 2051521 147256 147320 := by
  decide +kernel

private theorem r_147320 : RangeOk getRow 2051521 147320 147384 := by
  decide +kernel

private theorem r_147384 : RangeOk getRow 2051521 147384 147448 := by
  decide +kernel

private theorem r_147448 : RangeOk getRow 2051521 147448 147512 := by
  decide +kernel

private theorem r_147512 : RangeOk getRow 2051521 147512 147576 := by
  decide +kernel

private theorem r_147576 : RangeOk getRow 2051521 147576 147640 := by
  decide +kernel

private theorem s_145989 : RangeOk getRow 2051521 145925 145989 := r_145925
private theorem s_146053 : RangeOk getRow 2051521 145925 146053 :=
  s_145989.append (by norm_num) r_145989
private theorem s_146117 : RangeOk getRow 2051521 145925 146117 :=
  s_146053.append (by norm_num) r_146053
private theorem s_146181 : RangeOk getRow 2051521 145925 146181 :=
  s_146117.append (by norm_num) r_146117
private theorem s_146245 : RangeOk getRow 2051521 145925 146245 :=
  s_146181.append (by norm_num) r_146181
private theorem s_146309 : RangeOk getRow 2051521 145925 146309 :=
  s_146245.append (by norm_num) r_146245
private theorem s_146373 : RangeOk getRow 2051521 145925 146373 :=
  s_146309.append (by norm_num) r_146309
private theorem s_146437 : RangeOk getRow 2051521 145925 146437 :=
  s_146373.append (by norm_num) r_146373
private theorem s_146501 : RangeOk getRow 2051521 145925 146501 :=
  s_146437.append (by norm_num) r_146437
private theorem s_146565 : RangeOk getRow 2051521 145925 146565 :=
  s_146501.append (by norm_num) r_146501
private theorem s_146629 : RangeOk getRow 2051521 145925 146629 :=
  s_146565.append (by norm_num) r_146565
private theorem s_146693 : RangeOk getRow 2051521 145925 146693 :=
  s_146629.append (by norm_num) r_146629
private theorem s_146757 : RangeOk getRow 2051521 145925 146757 :=
  s_146693.append (by norm_num) r_146693
private theorem s_146821 : RangeOk getRow 2051521 145925 146821 :=
  s_146757.append (by norm_num) r_146757
private theorem s_146885 : RangeOk getRow 2051521 145925 146885 :=
  s_146821.append (by norm_num) r_146821
private theorem s_146949 : RangeOk getRow 2051521 145925 146949 :=
  s_146885.append (by norm_num) r_146885
private theorem s_147013 : RangeOk getRow 2051521 145925 147013 :=
  s_146949.append (by norm_num) r_146949
private theorem s_147077 : RangeOk getRow 2051521 145925 147077 :=
  s_147013.append (by norm_num) r_147013
private theorem s_147141 : RangeOk getRow 2051521 145925 147141 :=
  s_147077.append (by norm_num) r_147077
private theorem s_147201 : RangeOk getRow 2051521 145925 147201 :=
  s_147141.append (by norm_num) r_147141
private theorem s_147256 : RangeOk getRow 2051521 145925 147256 :=
  s_147201.append (by norm_num) r_147201
private theorem s_147320 : RangeOk getRow 2051521 145925 147320 :=
  s_147256.append (by norm_num) r_147256
private theorem s_147384 : RangeOk getRow 2051521 145925 147384 :=
  s_147320.append (by norm_num) r_147320
private theorem s_147448 : RangeOk getRow 2051521 145925 147448 :=
  s_147384.append (by norm_num) r_147384
private theorem s_147512 : RangeOk getRow 2051521 145925 147512 :=
  s_147448.append (by norm_num) r_147448
private theorem s_147576 : RangeOk getRow 2051521 145925 147576 :=
  s_147512.append (by norm_num) r_147512
private theorem s_147640 : RangeOk getRow 2051521 145925 147640 :=
  s_147576.append (by norm_num) r_147576

/-- Rows `[145925, 147640)` are valid. -/
theorem rangeOk_145925_147640 : RangeOk getRow 2051521 145925 147640 := s_147640

end Noperthedron.Solution
