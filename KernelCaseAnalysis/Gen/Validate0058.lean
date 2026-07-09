import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[130306, 132042). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_130306 : RangeOk getRow 2051521 130306 130370 := by
  decide +kernel

private theorem r_130370 : RangeOk getRow 2051521 130370 130434 := by
  decide +kernel

private theorem r_130434 : RangeOk getRow 2051521 130434 130499 := by
  decide +kernel

private theorem r_130499 : RangeOk getRow 2051521 130499 130564 := by
  decide +kernel

private theorem r_130564 : RangeOk getRow 2051521 130564 130628 := by
  decide +kernel

private theorem r_130628 : RangeOk getRow 2051521 130628 130692 := by
  decide +kernel

private theorem r_130692 : RangeOk getRow 2051521 130692 130756 := by
  decide +kernel

private theorem r_130756 : RangeOk getRow 2051521 130756 130820 := by
  decide +kernel

private theorem r_130820 : RangeOk getRow 2051521 130820 130884 := by
  decide +kernel

private theorem r_130884 : RangeOk getRow 2051521 130884 130949 := by
  decide +kernel

private theorem r_130949 : RangeOk getRow 2051521 130949 131014 := by
  decide +kernel

private theorem r_131014 : RangeOk getRow 2051521 131014 131078 := by
  decide +kernel

private theorem r_131078 : RangeOk getRow 2051521 131078 131142 := by
  decide +kernel

private theorem r_131142 : RangeOk getRow 2051521 131142 131206 := by
  decide +kernel

private theorem r_131206 : RangeOk getRow 2051521 131206 131270 := by
  decide +kernel

private theorem r_131270 : RangeOk getRow 2051521 131270 131334 := by
  decide +kernel

private theorem r_131334 : RangeOk getRow 2051521 131334 131399 := by
  decide +kernel

private theorem r_131399 : RangeOk getRow 2051521 131399 131464 := by
  decide +kernel

private theorem r_131464 : RangeOk getRow 2051521 131464 131528 := by
  decide +kernel

private theorem r_131528 : RangeOk getRow 2051521 131528 131592 := by
  decide +kernel

private theorem r_131592 : RangeOk getRow 2051521 131592 131656 := by
  decide +kernel

private theorem r_131656 : RangeOk getRow 2051521 131656 131720 := by
  decide +kernel

private theorem r_131720 : RangeOk getRow 2051521 131720 131784 := by
  decide +kernel

private theorem r_131784 : RangeOk getRow 2051521 131784 131849 := by
  decide +kernel

private theorem r_131849 : RangeOk getRow 2051521 131849 131914 := by
  decide +kernel

private theorem r_131914 : RangeOk getRow 2051521 131914 131978 := by
  decide +kernel

private theorem r_131978 : RangeOk getRow 2051521 131978 132042 := by
  decide +kernel

private theorem s_130370 : RangeOk getRow 2051521 130306 130370 := r_130306
private theorem s_130434 : RangeOk getRow 2051521 130306 130434 :=
  s_130370.append (by norm_num) r_130370
private theorem s_130499 : RangeOk getRow 2051521 130306 130499 :=
  s_130434.append (by norm_num) r_130434
private theorem s_130564 : RangeOk getRow 2051521 130306 130564 :=
  s_130499.append (by norm_num) r_130499
private theorem s_130628 : RangeOk getRow 2051521 130306 130628 :=
  s_130564.append (by norm_num) r_130564
private theorem s_130692 : RangeOk getRow 2051521 130306 130692 :=
  s_130628.append (by norm_num) r_130628
private theorem s_130756 : RangeOk getRow 2051521 130306 130756 :=
  s_130692.append (by norm_num) r_130692
private theorem s_130820 : RangeOk getRow 2051521 130306 130820 :=
  s_130756.append (by norm_num) r_130756
private theorem s_130884 : RangeOk getRow 2051521 130306 130884 :=
  s_130820.append (by norm_num) r_130820
private theorem s_130949 : RangeOk getRow 2051521 130306 130949 :=
  s_130884.append (by norm_num) r_130884
private theorem s_131014 : RangeOk getRow 2051521 130306 131014 :=
  s_130949.append (by norm_num) r_130949
private theorem s_131078 : RangeOk getRow 2051521 130306 131078 :=
  s_131014.append (by norm_num) r_131014
private theorem s_131142 : RangeOk getRow 2051521 130306 131142 :=
  s_131078.append (by norm_num) r_131078
private theorem s_131206 : RangeOk getRow 2051521 130306 131206 :=
  s_131142.append (by norm_num) r_131142
private theorem s_131270 : RangeOk getRow 2051521 130306 131270 :=
  s_131206.append (by norm_num) r_131206
private theorem s_131334 : RangeOk getRow 2051521 130306 131334 :=
  s_131270.append (by norm_num) r_131270
private theorem s_131399 : RangeOk getRow 2051521 130306 131399 :=
  s_131334.append (by norm_num) r_131334
private theorem s_131464 : RangeOk getRow 2051521 130306 131464 :=
  s_131399.append (by norm_num) r_131399
private theorem s_131528 : RangeOk getRow 2051521 130306 131528 :=
  s_131464.append (by norm_num) r_131464
private theorem s_131592 : RangeOk getRow 2051521 130306 131592 :=
  s_131528.append (by norm_num) r_131528
private theorem s_131656 : RangeOk getRow 2051521 130306 131656 :=
  s_131592.append (by norm_num) r_131592
private theorem s_131720 : RangeOk getRow 2051521 130306 131720 :=
  s_131656.append (by norm_num) r_131656
private theorem s_131784 : RangeOk getRow 2051521 130306 131784 :=
  s_131720.append (by norm_num) r_131720
private theorem s_131849 : RangeOk getRow 2051521 130306 131849 :=
  s_131784.append (by norm_num) r_131784
private theorem s_131914 : RangeOk getRow 2051521 130306 131914 :=
  s_131849.append (by norm_num) r_131849
private theorem s_131978 : RangeOk getRow 2051521 130306 131978 :=
  s_131914.append (by norm_num) r_131914
private theorem s_132042 : RangeOk getRow 2051521 130306 132042 :=
  s_131978.append (by norm_num) r_131978

/-- Rows `[130306, 132042)` are valid. -/
theorem rangeOk_130306_132042 : RangeOk getRow 2051521 130306 132042 := s_132042

end Noperthedron.Solution
