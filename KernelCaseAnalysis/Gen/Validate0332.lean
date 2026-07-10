import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[799080, 801368). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_799080 : RangeOk getRow 2051521 799080 799147 := by
  decide +kernel

private theorem r_799147 : RangeOk getRow 2051521 799147 799212 := by
  decide +kernel

private theorem r_799212 : RangeOk getRow 2051521 799212 799280 := by
  decide +kernel

private theorem r_799280 : RangeOk getRow 2051521 799280 799349 := by
  decide +kernel

private theorem r_799349 : RangeOk getRow 2051521 799349 799418 := by
  decide +kernel

private theorem r_799418 : RangeOk getRow 2051521 799418 799485 := by
  decide +kernel

private theorem r_799485 : RangeOk getRow 2051521 799485 799550 := by
  decide +kernel

private theorem r_799550 : RangeOk getRow 2051521 799550 799618 := by
  decide +kernel

private theorem r_799618 : RangeOk getRow 2051521 799618 799686 := by
  decide +kernel

private theorem r_799686 : RangeOk getRow 2051521 799686 799754 := by
  decide +kernel

private theorem r_799754 : RangeOk getRow 2051521 799754 799823 := by
  decide +kernel

private theorem r_799823 : RangeOk getRow 2051521 799823 799889 := by
  decide +kernel

private theorem r_799889 : RangeOk getRow 2051521 799889 799955 := by
  decide +kernel

private theorem r_799955 : RangeOk getRow 2051521 799955 800022 := by
  decide +kernel

private theorem r_800022 : RangeOk getRow 2051521 800022 800090 := by
  decide +kernel

private theorem r_800090 : RangeOk getRow 2051521 800090 800158 := by
  decide +kernel

private theorem r_800158 : RangeOk getRow 2051521 800158 800225 := by
  decide +kernel

private theorem r_800225 : RangeOk getRow 2051521 800225 800293 := by
  decide +kernel

private theorem r_800293 : RangeOk getRow 2051521 800293 800359 := by
  decide +kernel

private theorem r_800359 : RangeOk getRow 2051521 800359 800425 := by
  decide +kernel

private theorem r_800425 : RangeOk getRow 2051521 800425 800493 := by
  decide +kernel

private theorem r_800493 : RangeOk getRow 2051521 800493 800561 := by
  decide +kernel

private theorem r_800561 : RangeOk getRow 2051521 800561 800627 := by
  decide +kernel

private theorem r_800627 : RangeOk getRow 2051521 800627 800695 := by
  decide +kernel

private theorem r_800695 : RangeOk getRow 2051521 800695 800763 := by
  decide +kernel

private theorem r_800763 : RangeOk getRow 2051521 800763 800829 := by
  decide +kernel

private theorem r_800829 : RangeOk getRow 2051521 800829 800896 := by
  decide +kernel

private theorem r_800896 : RangeOk getRow 2051521 800896 800964 := by
  decide +kernel

private theorem r_800964 : RangeOk getRow 2051521 800964 801031 := by
  decide +kernel

private theorem r_801031 : RangeOk getRow 2051521 801031 801099 := by
  decide +kernel

private theorem r_801099 : RangeOk getRow 2051521 801099 801166 := by
  decide +kernel

private theorem r_801166 : RangeOk getRow 2051521 801166 801233 := by
  decide +kernel

private theorem r_801233 : RangeOk getRow 2051521 801233 801300 := by
  decide +kernel

private theorem r_801300 : RangeOk getRow 2051521 801300 801368 := by
  decide +kernel

private theorem s_799147 : RangeOk getRow 2051521 799080 799147 := r_799080
private theorem s_799212 : RangeOk getRow 2051521 799080 799212 :=
  s_799147.append (by norm_num) r_799147
private theorem s_799280 : RangeOk getRow 2051521 799080 799280 :=
  s_799212.append (by norm_num) r_799212
private theorem s_799349 : RangeOk getRow 2051521 799080 799349 :=
  s_799280.append (by norm_num) r_799280
private theorem s_799418 : RangeOk getRow 2051521 799080 799418 :=
  s_799349.append (by norm_num) r_799349
private theorem s_799485 : RangeOk getRow 2051521 799080 799485 :=
  s_799418.append (by norm_num) r_799418
private theorem s_799550 : RangeOk getRow 2051521 799080 799550 :=
  s_799485.append (by norm_num) r_799485
private theorem s_799618 : RangeOk getRow 2051521 799080 799618 :=
  s_799550.append (by norm_num) r_799550
private theorem s_799686 : RangeOk getRow 2051521 799080 799686 :=
  s_799618.append (by norm_num) r_799618
private theorem s_799754 : RangeOk getRow 2051521 799080 799754 :=
  s_799686.append (by norm_num) r_799686
private theorem s_799823 : RangeOk getRow 2051521 799080 799823 :=
  s_799754.append (by norm_num) r_799754
private theorem s_799889 : RangeOk getRow 2051521 799080 799889 :=
  s_799823.append (by norm_num) r_799823
private theorem s_799955 : RangeOk getRow 2051521 799080 799955 :=
  s_799889.append (by norm_num) r_799889
private theorem s_800022 : RangeOk getRow 2051521 799080 800022 :=
  s_799955.append (by norm_num) r_799955
private theorem s_800090 : RangeOk getRow 2051521 799080 800090 :=
  s_800022.append (by norm_num) r_800022
private theorem s_800158 : RangeOk getRow 2051521 799080 800158 :=
  s_800090.append (by norm_num) r_800090
private theorem s_800225 : RangeOk getRow 2051521 799080 800225 :=
  s_800158.append (by norm_num) r_800158
private theorem s_800293 : RangeOk getRow 2051521 799080 800293 :=
  s_800225.append (by norm_num) r_800225
private theorem s_800359 : RangeOk getRow 2051521 799080 800359 :=
  s_800293.append (by norm_num) r_800293
private theorem s_800425 : RangeOk getRow 2051521 799080 800425 :=
  s_800359.append (by norm_num) r_800359
private theorem s_800493 : RangeOk getRow 2051521 799080 800493 :=
  s_800425.append (by norm_num) r_800425
private theorem s_800561 : RangeOk getRow 2051521 799080 800561 :=
  s_800493.append (by norm_num) r_800493
private theorem s_800627 : RangeOk getRow 2051521 799080 800627 :=
  s_800561.append (by norm_num) r_800561
private theorem s_800695 : RangeOk getRow 2051521 799080 800695 :=
  s_800627.append (by norm_num) r_800627
private theorem s_800763 : RangeOk getRow 2051521 799080 800763 :=
  s_800695.append (by norm_num) r_800695
private theorem s_800829 : RangeOk getRow 2051521 799080 800829 :=
  s_800763.append (by norm_num) r_800763
private theorem s_800896 : RangeOk getRow 2051521 799080 800896 :=
  s_800829.append (by norm_num) r_800829
private theorem s_800964 : RangeOk getRow 2051521 799080 800964 :=
  s_800896.append (by norm_num) r_800896
private theorem s_801031 : RangeOk getRow 2051521 799080 801031 :=
  s_800964.append (by norm_num) r_800964
private theorem s_801099 : RangeOk getRow 2051521 799080 801099 :=
  s_801031.append (by norm_num) r_801031
private theorem s_801166 : RangeOk getRow 2051521 799080 801166 :=
  s_801099.append (by norm_num) r_801099
private theorem s_801233 : RangeOk getRow 2051521 799080 801233 :=
  s_801166.append (by norm_num) r_801166
private theorem s_801300 : RangeOk getRow 2051521 799080 801300 :=
  s_801233.append (by norm_num) r_801233
private theorem s_801368 : RangeOk getRow 2051521 799080 801368 :=
  s_801300.append (by norm_num) r_801300

/-- Rows `[799080, 801368)` are valid. -/
theorem rangeOk_799080_801368 : RangeOk getRow 2051521 799080 801368 := s_801368

end Noperthedron.Solution
