import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[725911, 728518). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_725911 : RangeOk getRow 2051521 725911 725978 := by
  decide +kernel

private theorem r_725978 : RangeOk getRow 2051521 725978 726045 := by
  decide +kernel

private theorem r_726045 : RangeOk getRow 2051521 726045 726111 := by
  decide +kernel

private theorem r_726111 : RangeOk getRow 2051521 726111 726178 := by
  decide +kernel

private theorem r_726178 : RangeOk getRow 2051521 726178 726242 := by
  decide +kernel

private theorem r_726242 : RangeOk getRow 2051521 726242 726310 := by
  decide +kernel

private theorem r_726310 : RangeOk getRow 2051521 726310 726382 := by
  decide +kernel

private theorem r_726382 : RangeOk getRow 2051521 726382 726456 := by
  decide +kernel

private theorem r_726456 : RangeOk getRow 2051521 726456 726530 := by
  decide +kernel

private theorem r_726530 : RangeOk getRow 2051521 726530 726602 := by
  decide +kernel

private theorem r_726602 : RangeOk getRow 2051521 726602 726673 := by
  decide +kernel

private theorem r_726673 : RangeOk getRow 2051521 726673 726744 := by
  decide +kernel

private theorem r_726744 : RangeOk getRow 2051521 726744 726811 := by
  decide +kernel

private theorem r_726811 : RangeOk getRow 2051521 726811 726878 := by
  decide +kernel

private theorem r_726878 : RangeOk getRow 2051521 726878 726947 := by
  decide +kernel

private theorem r_726947 : RangeOk getRow 2051521 726947 727015 := by
  decide +kernel

private theorem r_727015 : RangeOk getRow 2051521 727015 727081 := by
  decide +kernel

private theorem r_727081 : RangeOk getRow 2051521 727081 727149 := by
  decide +kernel

private theorem r_727149 : RangeOk getRow 2051521 727149 727217 := by
  decide +kernel

private theorem r_727217 : RangeOk getRow 2051521 727217 727283 := by
  decide +kernel

private theorem r_727283 : RangeOk getRow 2051521 727283 727351 := by
  decide +kernel

private theorem r_727351 : RangeOk getRow 2051521 727351 727419 := by
  decide +kernel

private theorem r_727419 : RangeOk getRow 2051521 727419 727487 := by
  decide +kernel

private theorem r_727487 : RangeOk getRow 2051521 727487 727553 := by
  decide +kernel

private theorem r_727553 : RangeOk getRow 2051521 727553 727620 := by
  decide +kernel

private theorem r_727620 : RangeOk getRow 2051521 727620 727689 := by
  decide +kernel

private theorem r_727689 : RangeOk getRow 2051521 727689 727761 := by
  decide +kernel

private theorem r_727761 : RangeOk getRow 2051521 727761 727835 := by
  decide +kernel

private theorem r_727835 : RangeOk getRow 2051521 727835 727908 := by
  decide +kernel

private theorem r_727908 : RangeOk getRow 2051521 727908 727977 := by
  decide +kernel

private theorem r_727977 : RangeOk getRow 2051521 727977 728045 := by
  decide +kernel

private theorem r_728045 : RangeOk getRow 2051521 728045 728113 := by
  decide +kernel

private theorem r_728113 : RangeOk getRow 2051521 728113 728182 := by
  decide +kernel

private theorem r_728182 : RangeOk getRow 2051521 728182 728248 := by
  decide +kernel

private theorem r_728248 : RangeOk getRow 2051521 728248 728315 := by
  decide +kernel

private theorem r_728315 : RangeOk getRow 2051521 728315 728384 := by
  decide +kernel

private theorem r_728384 : RangeOk getRow 2051521 728384 728451 := by
  decide +kernel

private theorem r_728451 : RangeOk getRow 2051521 728451 728518 := by
  decide +kernel

private theorem s_725978 : RangeOk getRow 2051521 725911 725978 := r_725911
private theorem s_726045 : RangeOk getRow 2051521 725911 726045 :=
  s_725978.append (by norm_num) r_725978
private theorem s_726111 : RangeOk getRow 2051521 725911 726111 :=
  s_726045.append (by norm_num) r_726045
private theorem s_726178 : RangeOk getRow 2051521 725911 726178 :=
  s_726111.append (by norm_num) r_726111
private theorem s_726242 : RangeOk getRow 2051521 725911 726242 :=
  s_726178.append (by norm_num) r_726178
private theorem s_726310 : RangeOk getRow 2051521 725911 726310 :=
  s_726242.append (by norm_num) r_726242
private theorem s_726382 : RangeOk getRow 2051521 725911 726382 :=
  s_726310.append (by norm_num) r_726310
private theorem s_726456 : RangeOk getRow 2051521 725911 726456 :=
  s_726382.append (by norm_num) r_726382
private theorem s_726530 : RangeOk getRow 2051521 725911 726530 :=
  s_726456.append (by norm_num) r_726456
private theorem s_726602 : RangeOk getRow 2051521 725911 726602 :=
  s_726530.append (by norm_num) r_726530
private theorem s_726673 : RangeOk getRow 2051521 725911 726673 :=
  s_726602.append (by norm_num) r_726602
private theorem s_726744 : RangeOk getRow 2051521 725911 726744 :=
  s_726673.append (by norm_num) r_726673
private theorem s_726811 : RangeOk getRow 2051521 725911 726811 :=
  s_726744.append (by norm_num) r_726744
private theorem s_726878 : RangeOk getRow 2051521 725911 726878 :=
  s_726811.append (by norm_num) r_726811
private theorem s_726947 : RangeOk getRow 2051521 725911 726947 :=
  s_726878.append (by norm_num) r_726878
private theorem s_727015 : RangeOk getRow 2051521 725911 727015 :=
  s_726947.append (by norm_num) r_726947
private theorem s_727081 : RangeOk getRow 2051521 725911 727081 :=
  s_727015.append (by norm_num) r_727015
private theorem s_727149 : RangeOk getRow 2051521 725911 727149 :=
  s_727081.append (by norm_num) r_727081
private theorem s_727217 : RangeOk getRow 2051521 725911 727217 :=
  s_727149.append (by norm_num) r_727149
private theorem s_727283 : RangeOk getRow 2051521 725911 727283 :=
  s_727217.append (by norm_num) r_727217
private theorem s_727351 : RangeOk getRow 2051521 725911 727351 :=
  s_727283.append (by norm_num) r_727283
private theorem s_727419 : RangeOk getRow 2051521 725911 727419 :=
  s_727351.append (by norm_num) r_727351
private theorem s_727487 : RangeOk getRow 2051521 725911 727487 :=
  s_727419.append (by norm_num) r_727419
private theorem s_727553 : RangeOk getRow 2051521 725911 727553 :=
  s_727487.append (by norm_num) r_727487
private theorem s_727620 : RangeOk getRow 2051521 725911 727620 :=
  s_727553.append (by norm_num) r_727553
private theorem s_727689 : RangeOk getRow 2051521 725911 727689 :=
  s_727620.append (by norm_num) r_727620
private theorem s_727761 : RangeOk getRow 2051521 725911 727761 :=
  s_727689.append (by norm_num) r_727689
private theorem s_727835 : RangeOk getRow 2051521 725911 727835 :=
  s_727761.append (by norm_num) r_727761
private theorem s_727908 : RangeOk getRow 2051521 725911 727908 :=
  s_727835.append (by norm_num) r_727835
private theorem s_727977 : RangeOk getRow 2051521 725911 727977 :=
  s_727908.append (by norm_num) r_727908
private theorem s_728045 : RangeOk getRow 2051521 725911 728045 :=
  s_727977.append (by norm_num) r_727977
private theorem s_728113 : RangeOk getRow 2051521 725911 728113 :=
  s_728045.append (by norm_num) r_728045
private theorem s_728182 : RangeOk getRow 2051521 725911 728182 :=
  s_728113.append (by norm_num) r_728113
private theorem s_728248 : RangeOk getRow 2051521 725911 728248 :=
  s_728182.append (by norm_num) r_728182
private theorem s_728315 : RangeOk getRow 2051521 725911 728315 :=
  s_728248.append (by norm_num) r_728248
private theorem s_728384 : RangeOk getRow 2051521 725911 728384 :=
  s_728315.append (by norm_num) r_728315
private theorem s_728451 : RangeOk getRow 2051521 725911 728451 :=
  s_728384.append (by norm_num) r_728384
private theorem s_728518 : RangeOk getRow 2051521 725911 728518 :=
  s_728451.append (by norm_num) r_728451

/-- Rows `[725911, 728518)` are valid. -/
theorem rangeOk_725911_728518 : RangeOk getRow 2051521 725911 728518 := s_728518

end Noperthedron.Solution
