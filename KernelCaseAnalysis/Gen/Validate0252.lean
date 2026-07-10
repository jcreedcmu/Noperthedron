import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[609304, 611509). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_609304 : RangeOk getRow 2051521 609304 609374 := by
  decide +kernel

private theorem r_609374 : RangeOk getRow 2051521 609374 609441 := by
  decide +kernel

private theorem r_609441 : RangeOk getRow 2051521 609441 609508 := by
  decide +kernel

private theorem r_609508 : RangeOk getRow 2051521 609508 609577 := by
  decide +kernel

private theorem r_609577 : RangeOk getRow 2051521 609577 609642 := by
  decide +kernel

private theorem r_609642 : RangeOk getRow 2051521 609642 609707 := by
  decide +kernel

private theorem r_609707 : RangeOk getRow 2051521 609707 609773 := by
  decide +kernel

private theorem r_609773 : RangeOk getRow 2051521 609773 609840 := by
  decide +kernel

private theorem r_609840 : RangeOk getRow 2051521 609840 609909 := by
  decide +kernel

private theorem r_609909 : RangeOk getRow 2051521 609909 609978 := by
  decide +kernel

private theorem r_609978 : RangeOk getRow 2051521 609978 610047 := by
  decide +kernel

private theorem r_610047 : RangeOk getRow 2051521 610047 610115 := by
  decide +kernel

private theorem r_610115 : RangeOk getRow 2051521 610115 610182 := by
  decide +kernel

private theorem r_610182 : RangeOk getRow 2051521 610182 610247 := by
  decide +kernel

private theorem r_610247 : RangeOk getRow 2051521 610247 610312 := by
  decide +kernel

private theorem r_610312 : RangeOk getRow 2051521 610312 610379 := by
  decide +kernel

private theorem r_610379 : RangeOk getRow 2051521 610379 610446 := by
  decide +kernel

private theorem r_610446 : RangeOk getRow 2051521 610446 610514 := by
  decide +kernel

private theorem r_610514 : RangeOk getRow 2051521 610514 610580 := by
  decide +kernel

private theorem r_610580 : RangeOk getRow 2051521 610580 610645 := by
  decide +kernel

private theorem r_610645 : RangeOk getRow 2051521 610645 610710 := by
  decide +kernel

private theorem r_610710 : RangeOk getRow 2051521 610710 610778 := by
  decide +kernel

private theorem r_610778 : RangeOk getRow 2051521 610778 610844 := by
  decide +kernel

private theorem r_610844 : RangeOk getRow 2051521 610844 610910 := by
  decide +kernel

private theorem r_610910 : RangeOk getRow 2051521 610910 610976 := by
  decide +kernel

private theorem r_610976 : RangeOk getRow 2051521 610976 611044 := by
  decide +kernel

private theorem r_611044 : RangeOk getRow 2051521 611044 611109 := by
  decide +kernel

private theorem r_611109 : RangeOk getRow 2051521 611109 611176 := by
  decide +kernel

private theorem r_611176 : RangeOk getRow 2051521 611176 611241 := by
  decide +kernel

private theorem r_611241 : RangeOk getRow 2051521 611241 611310 := by
  decide +kernel

private theorem r_611310 : RangeOk getRow 2051521 611310 611376 := by
  decide +kernel

private theorem r_611376 : RangeOk getRow 2051521 611376 611442 := by
  decide +kernel

private theorem r_611442 : RangeOk getRow 2051521 611442 611509 := by
  decide +kernel

private theorem s_609374 : RangeOk getRow 2051521 609304 609374 := r_609304
private theorem s_609441 : RangeOk getRow 2051521 609304 609441 :=
  s_609374.append (by norm_num) r_609374
private theorem s_609508 : RangeOk getRow 2051521 609304 609508 :=
  s_609441.append (by norm_num) r_609441
private theorem s_609577 : RangeOk getRow 2051521 609304 609577 :=
  s_609508.append (by norm_num) r_609508
private theorem s_609642 : RangeOk getRow 2051521 609304 609642 :=
  s_609577.append (by norm_num) r_609577
private theorem s_609707 : RangeOk getRow 2051521 609304 609707 :=
  s_609642.append (by norm_num) r_609642
private theorem s_609773 : RangeOk getRow 2051521 609304 609773 :=
  s_609707.append (by norm_num) r_609707
private theorem s_609840 : RangeOk getRow 2051521 609304 609840 :=
  s_609773.append (by norm_num) r_609773
private theorem s_609909 : RangeOk getRow 2051521 609304 609909 :=
  s_609840.append (by norm_num) r_609840
private theorem s_609978 : RangeOk getRow 2051521 609304 609978 :=
  s_609909.append (by norm_num) r_609909
private theorem s_610047 : RangeOk getRow 2051521 609304 610047 :=
  s_609978.append (by norm_num) r_609978
private theorem s_610115 : RangeOk getRow 2051521 609304 610115 :=
  s_610047.append (by norm_num) r_610047
private theorem s_610182 : RangeOk getRow 2051521 609304 610182 :=
  s_610115.append (by norm_num) r_610115
private theorem s_610247 : RangeOk getRow 2051521 609304 610247 :=
  s_610182.append (by norm_num) r_610182
private theorem s_610312 : RangeOk getRow 2051521 609304 610312 :=
  s_610247.append (by norm_num) r_610247
private theorem s_610379 : RangeOk getRow 2051521 609304 610379 :=
  s_610312.append (by norm_num) r_610312
private theorem s_610446 : RangeOk getRow 2051521 609304 610446 :=
  s_610379.append (by norm_num) r_610379
private theorem s_610514 : RangeOk getRow 2051521 609304 610514 :=
  s_610446.append (by norm_num) r_610446
private theorem s_610580 : RangeOk getRow 2051521 609304 610580 :=
  s_610514.append (by norm_num) r_610514
private theorem s_610645 : RangeOk getRow 2051521 609304 610645 :=
  s_610580.append (by norm_num) r_610580
private theorem s_610710 : RangeOk getRow 2051521 609304 610710 :=
  s_610645.append (by norm_num) r_610645
private theorem s_610778 : RangeOk getRow 2051521 609304 610778 :=
  s_610710.append (by norm_num) r_610710
private theorem s_610844 : RangeOk getRow 2051521 609304 610844 :=
  s_610778.append (by norm_num) r_610778
private theorem s_610910 : RangeOk getRow 2051521 609304 610910 :=
  s_610844.append (by norm_num) r_610844
private theorem s_610976 : RangeOk getRow 2051521 609304 610976 :=
  s_610910.append (by norm_num) r_610910
private theorem s_611044 : RangeOk getRow 2051521 609304 611044 :=
  s_610976.append (by norm_num) r_610976
private theorem s_611109 : RangeOk getRow 2051521 609304 611109 :=
  s_611044.append (by norm_num) r_611044
private theorem s_611176 : RangeOk getRow 2051521 609304 611176 :=
  s_611109.append (by norm_num) r_611109
private theorem s_611241 : RangeOk getRow 2051521 609304 611241 :=
  s_611176.append (by norm_num) r_611176
private theorem s_611310 : RangeOk getRow 2051521 609304 611310 :=
  s_611241.append (by norm_num) r_611241
private theorem s_611376 : RangeOk getRow 2051521 609304 611376 :=
  s_611310.append (by norm_num) r_611310
private theorem s_611442 : RangeOk getRow 2051521 609304 611442 :=
  s_611376.append (by norm_num) r_611376
private theorem s_611509 : RangeOk getRow 2051521 609304 611509 :=
  s_611442.append (by norm_num) r_611442

/-- Rows `[609304, 611509)` are valid. -/
theorem rangeOk_609304_611509 : RangeOk getRow 2051521 609304 611509 := s_611509

end Noperthedron.Solution
