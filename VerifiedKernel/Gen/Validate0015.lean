import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[30800, 32529). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_30800 : RangeOk getRow 2051521 30800 30864 := by
  decide +kernel

private theorem r_30864 : RangeOk getRow 2051521 30864 30928 := by
  decide +kernel

private theorem r_30928 : RangeOk getRow 2051521 30928 30992 := by
  decide +kernel

private theorem r_30992 : RangeOk getRow 2051521 30992 31057 := by
  decide +kernel

private theorem r_31057 : RangeOk getRow 2051521 31057 31121 := by
  decide +kernel

private theorem r_31121 : RangeOk getRow 2051521 31121 31185 := by
  decide +kernel

private theorem r_31185 : RangeOk getRow 2051521 31185 31249 := by
  decide +kernel

private theorem r_31249 : RangeOk getRow 2051521 31249 31313 := by
  decide +kernel

private theorem r_31313 : RangeOk getRow 2051521 31313 31377 := by
  decide +kernel

private theorem r_31377 : RangeOk getRow 2051521 31377 31441 := by
  decide +kernel

private theorem r_31441 : RangeOk getRow 2051521 31441 31505 := by
  decide +kernel

private theorem r_31505 : RangeOk getRow 2051521 31505 31569 := by
  decide +kernel

private theorem r_31569 : RangeOk getRow 2051521 31569 31633 := by
  decide +kernel

private theorem r_31633 : RangeOk getRow 2051521 31633 31697 := by
  decide +kernel

private theorem r_31697 : RangeOk getRow 2051521 31697 31761 := by
  decide +kernel

private theorem r_31761 : RangeOk getRow 2051521 31761 31825 := by
  decide +kernel

private theorem r_31825 : RangeOk getRow 2051521 31825 31889 := by
  decide +kernel

private theorem r_31889 : RangeOk getRow 2051521 31889 31953 := by
  decide +kernel

private theorem r_31953 : RangeOk getRow 2051521 31953 32017 := by
  decide +kernel

private theorem r_32017 : RangeOk getRow 2051521 32017 32081 := by
  decide +kernel

private theorem r_32081 : RangeOk getRow 2051521 32081 32145 := by
  decide +kernel

private theorem r_32145 : RangeOk getRow 2051521 32145 32209 := by
  decide +kernel

private theorem r_32209 : RangeOk getRow 2051521 32209 32273 := by
  decide +kernel

private theorem r_32273 : RangeOk getRow 2051521 32273 32337 := by
  decide +kernel

private theorem r_32337 : RangeOk getRow 2051521 32337 32401 := by
  decide +kernel

private theorem r_32401 : RangeOk getRow 2051521 32401 32465 := by
  decide +kernel

private theorem r_32465 : RangeOk getRow 2051521 32465 32529 := by
  decide +kernel

private theorem s_30864 : RangeOk getRow 2051521 30800 30864 := r_30800
private theorem s_30928 : RangeOk getRow 2051521 30800 30928 :=
  s_30864.append (by norm_num) r_30864
private theorem s_30992 : RangeOk getRow 2051521 30800 30992 :=
  s_30928.append (by norm_num) r_30928
private theorem s_31057 : RangeOk getRow 2051521 30800 31057 :=
  s_30992.append (by norm_num) r_30992
private theorem s_31121 : RangeOk getRow 2051521 30800 31121 :=
  s_31057.append (by norm_num) r_31057
private theorem s_31185 : RangeOk getRow 2051521 30800 31185 :=
  s_31121.append (by norm_num) r_31121
private theorem s_31249 : RangeOk getRow 2051521 30800 31249 :=
  s_31185.append (by norm_num) r_31185
private theorem s_31313 : RangeOk getRow 2051521 30800 31313 :=
  s_31249.append (by norm_num) r_31249
private theorem s_31377 : RangeOk getRow 2051521 30800 31377 :=
  s_31313.append (by norm_num) r_31313
private theorem s_31441 : RangeOk getRow 2051521 30800 31441 :=
  s_31377.append (by norm_num) r_31377
private theorem s_31505 : RangeOk getRow 2051521 30800 31505 :=
  s_31441.append (by norm_num) r_31441
private theorem s_31569 : RangeOk getRow 2051521 30800 31569 :=
  s_31505.append (by norm_num) r_31505
private theorem s_31633 : RangeOk getRow 2051521 30800 31633 :=
  s_31569.append (by norm_num) r_31569
private theorem s_31697 : RangeOk getRow 2051521 30800 31697 :=
  s_31633.append (by norm_num) r_31633
private theorem s_31761 : RangeOk getRow 2051521 30800 31761 :=
  s_31697.append (by norm_num) r_31697
private theorem s_31825 : RangeOk getRow 2051521 30800 31825 :=
  s_31761.append (by norm_num) r_31761
private theorem s_31889 : RangeOk getRow 2051521 30800 31889 :=
  s_31825.append (by norm_num) r_31825
private theorem s_31953 : RangeOk getRow 2051521 30800 31953 :=
  s_31889.append (by norm_num) r_31889
private theorem s_32017 : RangeOk getRow 2051521 30800 32017 :=
  s_31953.append (by norm_num) r_31953
private theorem s_32081 : RangeOk getRow 2051521 30800 32081 :=
  s_32017.append (by norm_num) r_32017
private theorem s_32145 : RangeOk getRow 2051521 30800 32145 :=
  s_32081.append (by norm_num) r_32081
private theorem s_32209 : RangeOk getRow 2051521 30800 32209 :=
  s_32145.append (by norm_num) r_32145
private theorem s_32273 : RangeOk getRow 2051521 30800 32273 :=
  s_32209.append (by norm_num) r_32209
private theorem s_32337 : RangeOk getRow 2051521 30800 32337 :=
  s_32273.append (by norm_num) r_32273
private theorem s_32401 : RangeOk getRow 2051521 30800 32401 :=
  s_32337.append (by norm_num) r_32337
private theorem s_32465 : RangeOk getRow 2051521 30800 32465 :=
  s_32401.append (by norm_num) r_32401
private theorem s_32529 : RangeOk getRow 2051521 30800 32529 :=
  s_32465.append (by norm_num) r_32465

/-- Rows `[30800, 32529)` are valid. -/
theorem rangeOk_30800_32529 : RangeOk getRow 2051521 30800 32529 := s_32529

end Noperthedron.Solution
