import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[707086, 709378). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_707086 : RangeOk getRow 2051521 707086 707153 := by
  decide +kernel

private theorem r_707153 : RangeOk getRow 2051521 707153 707221 := by
  decide +kernel

private theorem r_707221 : RangeOk getRow 2051521 707221 707289 := by
  decide +kernel

private theorem r_707289 : RangeOk getRow 2051521 707289 707354 := by
  decide +kernel

private theorem r_707354 : RangeOk getRow 2051521 707354 707420 := by
  decide +kernel

private theorem r_707420 : RangeOk getRow 2051521 707420 707486 := by
  decide +kernel

private theorem r_707486 : RangeOk getRow 2051521 707486 707555 := by
  decide +kernel

private theorem r_707555 : RangeOk getRow 2051521 707555 707623 := by
  decide +kernel

private theorem r_707623 : RangeOk getRow 2051521 707623 707689 := by
  decide +kernel

private theorem r_707689 : RangeOk getRow 2051521 707689 707755 := by
  decide +kernel

private theorem r_707755 : RangeOk getRow 2051521 707755 707824 := by
  decide +kernel

private theorem r_707824 : RangeOk getRow 2051521 707824 707892 := by
  decide +kernel

private theorem r_707892 : RangeOk getRow 2051521 707892 707959 := by
  decide +kernel

private theorem r_707959 : RangeOk getRow 2051521 707959 708028 := by
  decide +kernel

private theorem r_708028 : RangeOk getRow 2051521 708028 708095 := by
  decide +kernel

private theorem r_708095 : RangeOk getRow 2051521 708095 708161 := by
  decide +kernel

private theorem r_708161 : RangeOk getRow 2051521 708161 708228 := by
  decide +kernel

private theorem r_708228 : RangeOk getRow 2051521 708228 708295 := by
  decide +kernel

private theorem r_708295 : RangeOk getRow 2051521 708295 708363 := by
  decide +kernel

private theorem r_708363 : RangeOk getRow 2051521 708363 708428 := by
  decide +kernel

private theorem r_708428 : RangeOk getRow 2051521 708428 708495 := by
  decide +kernel

private theorem r_708495 : RangeOk getRow 2051521 708495 708563 := by
  decide +kernel

private theorem r_708563 : RangeOk getRow 2051521 708563 708631 := by
  decide +kernel

private theorem r_708631 : RangeOk getRow 2051521 708631 708699 := by
  decide +kernel

private theorem r_708699 : RangeOk getRow 2051521 708699 708768 := by
  decide +kernel

private theorem r_708768 : RangeOk getRow 2051521 708768 708836 := by
  decide +kernel

private theorem r_708836 : RangeOk getRow 2051521 708836 708904 := by
  decide +kernel

private theorem r_708904 : RangeOk getRow 2051521 708904 708969 := by
  decide +kernel

private theorem r_708969 : RangeOk getRow 2051521 708969 709036 := by
  decide +kernel

private theorem r_709036 : RangeOk getRow 2051521 709036 709105 := by
  decide +kernel

private theorem r_709105 : RangeOk getRow 2051521 709105 709173 := by
  decide +kernel

private theorem r_709173 : RangeOk getRow 2051521 709173 709242 := by
  decide +kernel

private theorem r_709242 : RangeOk getRow 2051521 709242 709310 := by
  decide +kernel

private theorem r_709310 : RangeOk getRow 2051521 709310 709378 := by
  decide +kernel

private theorem s_707153 : RangeOk getRow 2051521 707086 707153 := r_707086
private theorem s_707221 : RangeOk getRow 2051521 707086 707221 :=
  s_707153.append (by norm_num) r_707153
private theorem s_707289 : RangeOk getRow 2051521 707086 707289 :=
  s_707221.append (by norm_num) r_707221
private theorem s_707354 : RangeOk getRow 2051521 707086 707354 :=
  s_707289.append (by norm_num) r_707289
private theorem s_707420 : RangeOk getRow 2051521 707086 707420 :=
  s_707354.append (by norm_num) r_707354
private theorem s_707486 : RangeOk getRow 2051521 707086 707486 :=
  s_707420.append (by norm_num) r_707420
private theorem s_707555 : RangeOk getRow 2051521 707086 707555 :=
  s_707486.append (by norm_num) r_707486
private theorem s_707623 : RangeOk getRow 2051521 707086 707623 :=
  s_707555.append (by norm_num) r_707555
private theorem s_707689 : RangeOk getRow 2051521 707086 707689 :=
  s_707623.append (by norm_num) r_707623
private theorem s_707755 : RangeOk getRow 2051521 707086 707755 :=
  s_707689.append (by norm_num) r_707689
private theorem s_707824 : RangeOk getRow 2051521 707086 707824 :=
  s_707755.append (by norm_num) r_707755
private theorem s_707892 : RangeOk getRow 2051521 707086 707892 :=
  s_707824.append (by norm_num) r_707824
private theorem s_707959 : RangeOk getRow 2051521 707086 707959 :=
  s_707892.append (by norm_num) r_707892
private theorem s_708028 : RangeOk getRow 2051521 707086 708028 :=
  s_707959.append (by norm_num) r_707959
private theorem s_708095 : RangeOk getRow 2051521 707086 708095 :=
  s_708028.append (by norm_num) r_708028
private theorem s_708161 : RangeOk getRow 2051521 707086 708161 :=
  s_708095.append (by norm_num) r_708095
private theorem s_708228 : RangeOk getRow 2051521 707086 708228 :=
  s_708161.append (by norm_num) r_708161
private theorem s_708295 : RangeOk getRow 2051521 707086 708295 :=
  s_708228.append (by norm_num) r_708228
private theorem s_708363 : RangeOk getRow 2051521 707086 708363 :=
  s_708295.append (by norm_num) r_708295
private theorem s_708428 : RangeOk getRow 2051521 707086 708428 :=
  s_708363.append (by norm_num) r_708363
private theorem s_708495 : RangeOk getRow 2051521 707086 708495 :=
  s_708428.append (by norm_num) r_708428
private theorem s_708563 : RangeOk getRow 2051521 707086 708563 :=
  s_708495.append (by norm_num) r_708495
private theorem s_708631 : RangeOk getRow 2051521 707086 708631 :=
  s_708563.append (by norm_num) r_708563
private theorem s_708699 : RangeOk getRow 2051521 707086 708699 :=
  s_708631.append (by norm_num) r_708631
private theorem s_708768 : RangeOk getRow 2051521 707086 708768 :=
  s_708699.append (by norm_num) r_708699
private theorem s_708836 : RangeOk getRow 2051521 707086 708836 :=
  s_708768.append (by norm_num) r_708768
private theorem s_708904 : RangeOk getRow 2051521 707086 708904 :=
  s_708836.append (by norm_num) r_708836
private theorem s_708969 : RangeOk getRow 2051521 707086 708969 :=
  s_708904.append (by norm_num) r_708904
private theorem s_709036 : RangeOk getRow 2051521 707086 709036 :=
  s_708969.append (by norm_num) r_708969
private theorem s_709105 : RangeOk getRow 2051521 707086 709105 :=
  s_709036.append (by norm_num) r_709036
private theorem s_709173 : RangeOk getRow 2051521 707086 709173 :=
  s_709105.append (by norm_num) r_709105
private theorem s_709242 : RangeOk getRow 2051521 707086 709242 :=
  s_709173.append (by norm_num) r_709173
private theorem s_709310 : RangeOk getRow 2051521 707086 709310 :=
  s_709242.append (by norm_num) r_709242
private theorem s_709378 : RangeOk getRow 2051521 707086 709378 :=
  s_709310.append (by norm_num) r_709310

/-- Rows `[707086, 709378)` are valid. -/
theorem rangeOk_707086_709378 : RangeOk getRow 2051521 707086 709378 := s_709378

end Noperthedron.Solution
