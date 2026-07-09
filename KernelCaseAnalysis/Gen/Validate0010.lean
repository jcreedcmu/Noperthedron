import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[22165, 23893). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_22165 : RangeOk getRow 2051521 22165 22229 := by
  decide +kernel

private theorem r_22229 : RangeOk getRow 2051521 22229 22293 := by
  decide +kernel

private theorem r_22293 : RangeOk getRow 2051521 22293 22357 := by
  decide +kernel

private theorem r_22357 : RangeOk getRow 2051521 22357 22421 := by
  decide +kernel

private theorem r_22421 : RangeOk getRow 2051521 22421 22485 := by
  decide +kernel

private theorem r_22485 : RangeOk getRow 2051521 22485 22550 := by
  decide +kernel

private theorem r_22550 : RangeOk getRow 2051521 22550 22614 := by
  decide +kernel

private theorem r_22614 : RangeOk getRow 2051521 22614 22678 := by
  decide +kernel

private theorem r_22678 : RangeOk getRow 2051521 22678 22742 := by
  decide +kernel

private theorem r_22742 : RangeOk getRow 2051521 22742 22806 := by
  decide +kernel

private theorem r_22806 : RangeOk getRow 2051521 22806 22870 := by
  decide +kernel

private theorem r_22870 : RangeOk getRow 2051521 22870 22935 := by
  decide +kernel

private theorem r_22935 : RangeOk getRow 2051521 22935 22995 := by
  decide +kernel

private theorem r_22995 : RangeOk getRow 2051521 22995 23059 := by
  decide +kernel

private theorem r_23059 : RangeOk getRow 2051521 23059 23123 := by
  decide +kernel

private theorem r_23123 : RangeOk getRow 2051521 23123 23187 := by
  decide +kernel

private theorem r_23187 : RangeOk getRow 2051521 23187 23251 := by
  decide +kernel

private theorem r_23251 : RangeOk getRow 2051521 23251 23315 := by
  decide +kernel

private theorem r_23315 : RangeOk getRow 2051521 23315 23379 := by
  decide +kernel

private theorem r_23379 : RangeOk getRow 2051521 23379 23444 := by
  decide +kernel

private theorem r_23444 : RangeOk getRow 2051521 23444 23508 := by
  decide +kernel

private theorem r_23508 : RangeOk getRow 2051521 23508 23572 := by
  decide +kernel

private theorem r_23572 : RangeOk getRow 2051521 23572 23636 := by
  decide +kernel

private theorem r_23636 : RangeOk getRow 2051521 23636 23700 := by
  decide +kernel

private theorem r_23700 : RangeOk getRow 2051521 23700 23764 := by
  decide +kernel

private theorem r_23764 : RangeOk getRow 2051521 23764 23828 := by
  decide +kernel

private theorem r_23828 : RangeOk getRow 2051521 23828 23893 := by
  decide +kernel

private theorem s_22229 : RangeOk getRow 2051521 22165 22229 := r_22165
private theorem s_22293 : RangeOk getRow 2051521 22165 22293 :=
  s_22229.append (by norm_num) r_22229
private theorem s_22357 : RangeOk getRow 2051521 22165 22357 :=
  s_22293.append (by norm_num) r_22293
private theorem s_22421 : RangeOk getRow 2051521 22165 22421 :=
  s_22357.append (by norm_num) r_22357
private theorem s_22485 : RangeOk getRow 2051521 22165 22485 :=
  s_22421.append (by norm_num) r_22421
private theorem s_22550 : RangeOk getRow 2051521 22165 22550 :=
  s_22485.append (by norm_num) r_22485
private theorem s_22614 : RangeOk getRow 2051521 22165 22614 :=
  s_22550.append (by norm_num) r_22550
private theorem s_22678 : RangeOk getRow 2051521 22165 22678 :=
  s_22614.append (by norm_num) r_22614
private theorem s_22742 : RangeOk getRow 2051521 22165 22742 :=
  s_22678.append (by norm_num) r_22678
private theorem s_22806 : RangeOk getRow 2051521 22165 22806 :=
  s_22742.append (by norm_num) r_22742
private theorem s_22870 : RangeOk getRow 2051521 22165 22870 :=
  s_22806.append (by norm_num) r_22806
private theorem s_22935 : RangeOk getRow 2051521 22165 22935 :=
  s_22870.append (by norm_num) r_22870
private theorem s_22995 : RangeOk getRow 2051521 22165 22995 :=
  s_22935.append (by norm_num) r_22935
private theorem s_23059 : RangeOk getRow 2051521 22165 23059 :=
  s_22995.append (by norm_num) r_22995
private theorem s_23123 : RangeOk getRow 2051521 22165 23123 :=
  s_23059.append (by norm_num) r_23059
private theorem s_23187 : RangeOk getRow 2051521 22165 23187 :=
  s_23123.append (by norm_num) r_23123
private theorem s_23251 : RangeOk getRow 2051521 22165 23251 :=
  s_23187.append (by norm_num) r_23187
private theorem s_23315 : RangeOk getRow 2051521 22165 23315 :=
  s_23251.append (by norm_num) r_23251
private theorem s_23379 : RangeOk getRow 2051521 22165 23379 :=
  s_23315.append (by norm_num) r_23315
private theorem s_23444 : RangeOk getRow 2051521 22165 23444 :=
  s_23379.append (by norm_num) r_23379
private theorem s_23508 : RangeOk getRow 2051521 22165 23508 :=
  s_23444.append (by norm_num) r_23444
private theorem s_23572 : RangeOk getRow 2051521 22165 23572 :=
  s_23508.append (by norm_num) r_23508
private theorem s_23636 : RangeOk getRow 2051521 22165 23636 :=
  s_23572.append (by norm_num) r_23572
private theorem s_23700 : RangeOk getRow 2051521 22165 23700 :=
  s_23636.append (by norm_num) r_23636
private theorem s_23764 : RangeOk getRow 2051521 22165 23764 :=
  s_23700.append (by norm_num) r_23700
private theorem s_23828 : RangeOk getRow 2051521 22165 23828 :=
  s_23764.append (by norm_num) r_23764
private theorem s_23893 : RangeOk getRow 2051521 22165 23893 :=
  s_23828.append (by norm_num) r_23828

/-- Rows `[22165, 23893)` are valid. -/
theorem rangeOk_22165_23893 : RangeOk getRow 2051521 22165 23893 := s_23893

end Noperthedron.Solution
