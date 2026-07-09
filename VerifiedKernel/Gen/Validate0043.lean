import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[91783, 93505). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_91783 : RangeOk getRow 2051521 91783 91847 := by
  decide +kernel

private theorem r_91847 : RangeOk getRow 2051521 91847 91909 := by
  decide +kernel

private theorem r_91909 : RangeOk getRow 2051521 91909 91968 := by
  decide +kernel

private theorem r_91968 : RangeOk getRow 2051521 91968 92032 := by
  decide +kernel

private theorem r_92032 : RangeOk getRow 2051521 92032 92096 := by
  decide +kernel

private theorem r_92096 : RangeOk getRow 2051521 92096 92160 := by
  decide +kernel

private theorem r_92160 : RangeOk getRow 2051521 92160 92224 := by
  decide +kernel

private theorem r_92224 : RangeOk getRow 2051521 92224 92288 := by
  decide +kernel

private theorem r_92288 : RangeOk getRow 2051521 92288 92352 := by
  decide +kernel

private theorem r_92352 : RangeOk getRow 2051521 92352 92416 := by
  decide +kernel

private theorem r_92416 : RangeOk getRow 2051521 92416 92480 := by
  decide +kernel

private theorem r_92480 : RangeOk getRow 2051521 92480 92544 := by
  decide +kernel

private theorem r_92544 : RangeOk getRow 2051521 92544 92608 := by
  decide +kernel

private theorem r_92608 : RangeOk getRow 2051521 92608 92672 := by
  decide +kernel

private theorem r_92672 : RangeOk getRow 2051521 92672 92737 := by
  decide +kernel

private theorem r_92737 : RangeOk getRow 2051521 92737 92801 := by
  decide +kernel

private theorem r_92801 : RangeOk getRow 2051521 92801 92865 := by
  decide +kernel

private theorem r_92865 : RangeOk getRow 2051521 92865 92929 := by
  decide +kernel

private theorem r_92929 : RangeOk getRow 2051521 92929 92993 := by
  decide +kernel

private theorem r_92993 : RangeOk getRow 2051521 92993 93057 := by
  decide +kernel

private theorem r_93057 : RangeOk getRow 2051521 93057 93121 := by
  decide +kernel

private theorem r_93121 : RangeOk getRow 2051521 93121 93185 := by
  decide +kernel

private theorem r_93185 : RangeOk getRow 2051521 93185 93249 := by
  decide +kernel

private theorem r_93249 : RangeOk getRow 2051521 93249 93313 := by
  decide +kernel

private theorem r_93313 : RangeOk getRow 2051521 93313 93377 := by
  decide +kernel

private theorem r_93377 : RangeOk getRow 2051521 93377 93441 := by
  decide +kernel

private theorem r_93441 : RangeOk getRow 2051521 93441 93505 := by
  decide +kernel

private theorem s_91847 : RangeOk getRow 2051521 91783 91847 := r_91783
private theorem s_91909 : RangeOk getRow 2051521 91783 91909 :=
  s_91847.append (by norm_num) r_91847
private theorem s_91968 : RangeOk getRow 2051521 91783 91968 :=
  s_91909.append (by norm_num) r_91909
private theorem s_92032 : RangeOk getRow 2051521 91783 92032 :=
  s_91968.append (by norm_num) r_91968
private theorem s_92096 : RangeOk getRow 2051521 91783 92096 :=
  s_92032.append (by norm_num) r_92032
private theorem s_92160 : RangeOk getRow 2051521 91783 92160 :=
  s_92096.append (by norm_num) r_92096
private theorem s_92224 : RangeOk getRow 2051521 91783 92224 :=
  s_92160.append (by norm_num) r_92160
private theorem s_92288 : RangeOk getRow 2051521 91783 92288 :=
  s_92224.append (by norm_num) r_92224
private theorem s_92352 : RangeOk getRow 2051521 91783 92352 :=
  s_92288.append (by norm_num) r_92288
private theorem s_92416 : RangeOk getRow 2051521 91783 92416 :=
  s_92352.append (by norm_num) r_92352
private theorem s_92480 : RangeOk getRow 2051521 91783 92480 :=
  s_92416.append (by norm_num) r_92416
private theorem s_92544 : RangeOk getRow 2051521 91783 92544 :=
  s_92480.append (by norm_num) r_92480
private theorem s_92608 : RangeOk getRow 2051521 91783 92608 :=
  s_92544.append (by norm_num) r_92544
private theorem s_92672 : RangeOk getRow 2051521 91783 92672 :=
  s_92608.append (by norm_num) r_92608
private theorem s_92737 : RangeOk getRow 2051521 91783 92737 :=
  s_92672.append (by norm_num) r_92672
private theorem s_92801 : RangeOk getRow 2051521 91783 92801 :=
  s_92737.append (by norm_num) r_92737
private theorem s_92865 : RangeOk getRow 2051521 91783 92865 :=
  s_92801.append (by norm_num) r_92801
private theorem s_92929 : RangeOk getRow 2051521 91783 92929 :=
  s_92865.append (by norm_num) r_92865
private theorem s_92993 : RangeOk getRow 2051521 91783 92993 :=
  s_92929.append (by norm_num) r_92929
private theorem s_93057 : RangeOk getRow 2051521 91783 93057 :=
  s_92993.append (by norm_num) r_92993
private theorem s_93121 : RangeOk getRow 2051521 91783 93121 :=
  s_93057.append (by norm_num) r_93057
private theorem s_93185 : RangeOk getRow 2051521 91783 93185 :=
  s_93121.append (by norm_num) r_93121
private theorem s_93249 : RangeOk getRow 2051521 91783 93249 :=
  s_93185.append (by norm_num) r_93185
private theorem s_93313 : RangeOk getRow 2051521 91783 93313 :=
  s_93249.append (by norm_num) r_93249
private theorem s_93377 : RangeOk getRow 2051521 91783 93377 :=
  s_93313.append (by norm_num) r_93313
private theorem s_93441 : RangeOk getRow 2051521 91783 93441 :=
  s_93377.append (by norm_num) r_93377
private theorem s_93505 : RangeOk getRow 2051521 91783 93505 :=
  s_93441.append (by norm_num) r_93441

/-- Rows `[91783, 93505)` are valid. -/
theorem rangeOk_91783_93505 : RangeOk getRow 2051521 91783 93505 := s_93505

end Noperthedron.Solution
