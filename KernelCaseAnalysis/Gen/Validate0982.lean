import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[2025063, 2027821). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_2025063 : RangeOk getRow 2051521 2025063 2025115 := by
  decide +kernel

private theorem r_2025115 : RangeOk getRow 2051521 2025115 2025178 := by
  decide +kernel

private theorem r_2025178 : RangeOk getRow 2051521 2025178 2025236 := by
  decide +kernel

private theorem r_2025236 : RangeOk getRow 2051521 2025236 2025304 := by
  decide +kernel

private theorem r_2025304 : RangeOk getRow 2051521 2025304 2025342 := by
  decide +kernel

private theorem r_2025342 : RangeOk getRow 2051521 2025342 2025395 := by
  decide +kernel

private theorem r_2025395 : RangeOk getRow 2051521 2025395 2025433 := by
  decide +kernel

private theorem r_2025433 : RangeOk getRow 2051521 2025433 2025468 := by
  decide +kernel

private theorem r_2025468 : RangeOk getRow 2051521 2025468 2025532 := by
  decide +kernel

private theorem r_2025532 : RangeOk getRow 2051521 2025532 2025602 := by
  decide +kernel

private theorem r_2025602 : RangeOk getRow 2051521 2025602 2025645 := by
  decide +kernel

private theorem r_2025645 : RangeOk getRow 2051521 2025645 2025717 := by
  decide +kernel

private theorem r_2025717 : RangeOk getRow 2051521 2025717 2025768 := by
  decide +kernel

private theorem r_2025768 : RangeOk getRow 2051521 2025768 2025817 := by
  decide +kernel

private theorem r_2025817 : RangeOk getRow 2051521 2025817 2025888 := by
  decide +kernel

private theorem r_2025888 : RangeOk getRow 2051521 2025888 2025932 := by
  decide +kernel

private theorem r_2025932 : RangeOk getRow 2051521 2025932 2025990 := by
  decide +kernel

private theorem r_2025990 : RangeOk getRow 2051521 2025990 2026042 := by
  decide +kernel

private theorem r_2026042 : RangeOk getRow 2051521 2026042 2026107 := by
  decide +kernel

private theorem r_2026107 : RangeOk getRow 2051521 2026107 2026163 := by
  decide +kernel

private theorem r_2026163 : RangeOk getRow 2051521 2026163 2026202 := by
  decide +kernel

private theorem r_2026202 : RangeOk getRow 2051521 2026202 2026246 := by
  decide +kernel

private theorem r_2026246 : RangeOk getRow 2051521 2026246 2026276 := by
  decide +kernel

private theorem r_2026276 : RangeOk getRow 2051521 2026276 2026327 := by
  decide +kernel

private theorem r_2026327 : RangeOk getRow 2051521 2026327 2026385 := by
  decide +kernel

private theorem r_2026385 : RangeOk getRow 2051521 2026385 2026456 := by
  decide +kernel

private theorem r_2026456 : RangeOk getRow 2051521 2026456 2026527 := by
  decide +kernel

private theorem r_2026527 : RangeOk getRow 2051521 2026527 2026591 := by
  decide +kernel

private theorem r_2026591 : RangeOk getRow 2051521 2026591 2026634 := by
  decide +kernel

private theorem r_2026634 : RangeOk getRow 2051521 2026634 2026688 := by
  decide +kernel

private theorem r_2026688 : RangeOk getRow 2051521 2026688 2026752 := by
  decide +kernel

private theorem r_2026752 : RangeOk getRow 2051521 2026752 2026824 := by
  decide +kernel

private theorem r_2026824 : RangeOk getRow 2051521 2026824 2026888 := by
  decide +kernel

private theorem r_2026888 : RangeOk getRow 2051521 2026888 2026939 := by
  decide +kernel

private theorem r_2026939 : RangeOk getRow 2051521 2026939 2026989 := by
  decide +kernel

private theorem r_2026989 : RangeOk getRow 2051521 2026989 2027029 := by
  decide +kernel

private theorem r_2027029 : RangeOk getRow 2051521 2027029 2027087 := by
  decide +kernel

private theorem r_2027087 : RangeOk getRow 2051521 2027087 2027159 := by
  decide +kernel

private theorem r_2027159 : RangeOk getRow 2051521 2027159 2027223 := by
  decide +kernel

private theorem r_2027223 : RangeOk getRow 2051521 2027223 2027267 := by
  decide +kernel

private theorem r_2027267 : RangeOk getRow 2051521 2027267 2027324 := by
  decide +kernel

private theorem r_2027324 : RangeOk getRow 2051521 2027324 2027389 := by
  decide +kernel

private theorem r_2027389 : RangeOk getRow 2051521 2027389 2027453 := by
  decide +kernel

private theorem r_2027453 : RangeOk getRow 2051521 2027453 2027489 := by
  decide +kernel

private theorem r_2027489 : RangeOk getRow 2051521 2027489 2027545 := by
  decide +kernel

private theorem r_2027545 : RangeOk getRow 2051521 2027545 2027595 := by
  decide +kernel

private theorem r_2027595 : RangeOk getRow 2051521 2027595 2027658 := by
  decide +kernel

private theorem r_2027658 : RangeOk getRow 2051521 2027658 2027728 := by
  decide +kernel

private theorem r_2027728 : RangeOk getRow 2051521 2027728 2027778 := by
  decide +kernel

private theorem r_2027778 : RangeOk getRow 2051521 2027778 2027821 := by
  decide +kernel

private theorem s_2025115 : RangeOk getRow 2051521 2025063 2025115 := r_2025063
private theorem s_2025178 : RangeOk getRow 2051521 2025063 2025178 :=
  s_2025115.append (by norm_num) r_2025115
private theorem s_2025236 : RangeOk getRow 2051521 2025063 2025236 :=
  s_2025178.append (by norm_num) r_2025178
private theorem s_2025304 : RangeOk getRow 2051521 2025063 2025304 :=
  s_2025236.append (by norm_num) r_2025236
private theorem s_2025342 : RangeOk getRow 2051521 2025063 2025342 :=
  s_2025304.append (by norm_num) r_2025304
private theorem s_2025395 : RangeOk getRow 2051521 2025063 2025395 :=
  s_2025342.append (by norm_num) r_2025342
private theorem s_2025433 : RangeOk getRow 2051521 2025063 2025433 :=
  s_2025395.append (by norm_num) r_2025395
private theorem s_2025468 : RangeOk getRow 2051521 2025063 2025468 :=
  s_2025433.append (by norm_num) r_2025433
private theorem s_2025532 : RangeOk getRow 2051521 2025063 2025532 :=
  s_2025468.append (by norm_num) r_2025468
private theorem s_2025602 : RangeOk getRow 2051521 2025063 2025602 :=
  s_2025532.append (by norm_num) r_2025532
private theorem s_2025645 : RangeOk getRow 2051521 2025063 2025645 :=
  s_2025602.append (by norm_num) r_2025602
private theorem s_2025717 : RangeOk getRow 2051521 2025063 2025717 :=
  s_2025645.append (by norm_num) r_2025645
private theorem s_2025768 : RangeOk getRow 2051521 2025063 2025768 :=
  s_2025717.append (by norm_num) r_2025717
private theorem s_2025817 : RangeOk getRow 2051521 2025063 2025817 :=
  s_2025768.append (by norm_num) r_2025768
private theorem s_2025888 : RangeOk getRow 2051521 2025063 2025888 :=
  s_2025817.append (by norm_num) r_2025817
private theorem s_2025932 : RangeOk getRow 2051521 2025063 2025932 :=
  s_2025888.append (by norm_num) r_2025888
private theorem s_2025990 : RangeOk getRow 2051521 2025063 2025990 :=
  s_2025932.append (by norm_num) r_2025932
private theorem s_2026042 : RangeOk getRow 2051521 2025063 2026042 :=
  s_2025990.append (by norm_num) r_2025990
private theorem s_2026107 : RangeOk getRow 2051521 2025063 2026107 :=
  s_2026042.append (by norm_num) r_2026042
private theorem s_2026163 : RangeOk getRow 2051521 2025063 2026163 :=
  s_2026107.append (by norm_num) r_2026107
private theorem s_2026202 : RangeOk getRow 2051521 2025063 2026202 :=
  s_2026163.append (by norm_num) r_2026163
private theorem s_2026246 : RangeOk getRow 2051521 2025063 2026246 :=
  s_2026202.append (by norm_num) r_2026202
private theorem s_2026276 : RangeOk getRow 2051521 2025063 2026276 :=
  s_2026246.append (by norm_num) r_2026246
private theorem s_2026327 : RangeOk getRow 2051521 2025063 2026327 :=
  s_2026276.append (by norm_num) r_2026276
private theorem s_2026385 : RangeOk getRow 2051521 2025063 2026385 :=
  s_2026327.append (by norm_num) r_2026327
private theorem s_2026456 : RangeOk getRow 2051521 2025063 2026456 :=
  s_2026385.append (by norm_num) r_2026385
private theorem s_2026527 : RangeOk getRow 2051521 2025063 2026527 :=
  s_2026456.append (by norm_num) r_2026456
private theorem s_2026591 : RangeOk getRow 2051521 2025063 2026591 :=
  s_2026527.append (by norm_num) r_2026527
private theorem s_2026634 : RangeOk getRow 2051521 2025063 2026634 :=
  s_2026591.append (by norm_num) r_2026591
private theorem s_2026688 : RangeOk getRow 2051521 2025063 2026688 :=
  s_2026634.append (by norm_num) r_2026634
private theorem s_2026752 : RangeOk getRow 2051521 2025063 2026752 :=
  s_2026688.append (by norm_num) r_2026688
private theorem s_2026824 : RangeOk getRow 2051521 2025063 2026824 :=
  s_2026752.append (by norm_num) r_2026752
private theorem s_2026888 : RangeOk getRow 2051521 2025063 2026888 :=
  s_2026824.append (by norm_num) r_2026824
private theorem s_2026939 : RangeOk getRow 2051521 2025063 2026939 :=
  s_2026888.append (by norm_num) r_2026888
private theorem s_2026989 : RangeOk getRow 2051521 2025063 2026989 :=
  s_2026939.append (by norm_num) r_2026939
private theorem s_2027029 : RangeOk getRow 2051521 2025063 2027029 :=
  s_2026989.append (by norm_num) r_2026989
private theorem s_2027087 : RangeOk getRow 2051521 2025063 2027087 :=
  s_2027029.append (by norm_num) r_2027029
private theorem s_2027159 : RangeOk getRow 2051521 2025063 2027159 :=
  s_2027087.append (by norm_num) r_2027087
private theorem s_2027223 : RangeOk getRow 2051521 2025063 2027223 :=
  s_2027159.append (by norm_num) r_2027159
private theorem s_2027267 : RangeOk getRow 2051521 2025063 2027267 :=
  s_2027223.append (by norm_num) r_2027223
private theorem s_2027324 : RangeOk getRow 2051521 2025063 2027324 :=
  s_2027267.append (by norm_num) r_2027267
private theorem s_2027389 : RangeOk getRow 2051521 2025063 2027389 :=
  s_2027324.append (by norm_num) r_2027324
private theorem s_2027453 : RangeOk getRow 2051521 2025063 2027453 :=
  s_2027389.append (by norm_num) r_2027389
private theorem s_2027489 : RangeOk getRow 2051521 2025063 2027489 :=
  s_2027453.append (by norm_num) r_2027453
private theorem s_2027545 : RangeOk getRow 2051521 2025063 2027545 :=
  s_2027489.append (by norm_num) r_2027489
private theorem s_2027595 : RangeOk getRow 2051521 2025063 2027595 :=
  s_2027545.append (by norm_num) r_2027545
private theorem s_2027658 : RangeOk getRow 2051521 2025063 2027658 :=
  s_2027595.append (by norm_num) r_2027595
private theorem s_2027728 : RangeOk getRow 2051521 2025063 2027728 :=
  s_2027658.append (by norm_num) r_2027658
private theorem s_2027778 : RangeOk getRow 2051521 2025063 2027778 :=
  s_2027728.append (by norm_num) r_2027728
private theorem s_2027821 : RangeOk getRow 2051521 2025063 2027821 :=
  s_2027778.append (by norm_num) r_2027778

/-- Rows `[2025063, 2027821)` are valid. -/
theorem rangeOk_2025063_2027821 : RangeOk getRow 2051521 2025063 2027821 := s_2027821

end Noperthedron.Solution
