import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[147640, 149359). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_147640 : RangeOk getRow 2051521 147640 147695 := by
  decide +kernel

private theorem r_147695 : RangeOk getRow 2051521 147695 147759 := by
  decide +kernel

private theorem r_147759 : RangeOk getRow 2051521 147759 147823 := by
  decide +kernel

private theorem r_147823 : RangeOk getRow 2051521 147823 147887 := by
  decide +kernel

private theorem r_147887 : RangeOk getRow 2051521 147887 147951 := by
  decide +kernel

private theorem r_147951 : RangeOk getRow 2051521 147951 148015 := by
  decide +kernel

private theorem r_148015 : RangeOk getRow 2051521 148015 148079 := by
  decide +kernel

private theorem r_148079 : RangeOk getRow 2051521 148079 148143 := by
  decide +kernel

private theorem r_148143 : RangeOk getRow 2051521 148143 148207 := by
  decide +kernel

private theorem r_148207 : RangeOk getRow 2051521 148207 148271 := by
  decide +kernel

private theorem r_148271 : RangeOk getRow 2051521 148271 148335 := by
  decide +kernel

private theorem r_148335 : RangeOk getRow 2051521 148335 148399 := by
  decide +kernel

private theorem r_148399 : RangeOk getRow 2051521 148399 148463 := by
  decide +kernel

private theorem r_148463 : RangeOk getRow 2051521 148463 148527 := by
  decide +kernel

private theorem r_148527 : RangeOk getRow 2051521 148527 148591 := by
  decide +kernel

private theorem r_148591 : RangeOk getRow 2051521 148591 148655 := by
  decide +kernel

private theorem r_148655 : RangeOk getRow 2051521 148655 148719 := by
  decide +kernel

private theorem r_148719 : RangeOk getRow 2051521 148719 148783 := by
  decide +kernel

private theorem r_148783 : RangeOk getRow 2051521 148783 148847 := by
  decide +kernel

private theorem r_148847 : RangeOk getRow 2051521 148847 148911 := by
  decide +kernel

private theorem r_148911 : RangeOk getRow 2051521 148911 148975 := by
  decide +kernel

private theorem r_148975 : RangeOk getRow 2051521 148975 149039 := by
  decide +kernel

private theorem r_149039 : RangeOk getRow 2051521 149039 149103 := by
  decide +kernel

private theorem r_149103 : RangeOk getRow 2051521 149103 149167 := by
  decide +kernel

private theorem r_149167 : RangeOk getRow 2051521 149167 149231 := by
  decide +kernel

private theorem r_149231 : RangeOk getRow 2051521 149231 149295 := by
  decide +kernel

private theorem r_149295 : RangeOk getRow 2051521 149295 149359 := by
  decide +kernel

private theorem s_147695 : RangeOk getRow 2051521 147640 147695 := r_147640
private theorem s_147759 : RangeOk getRow 2051521 147640 147759 :=
  s_147695.append (by norm_num) r_147695
private theorem s_147823 : RangeOk getRow 2051521 147640 147823 :=
  s_147759.append (by norm_num) r_147759
private theorem s_147887 : RangeOk getRow 2051521 147640 147887 :=
  s_147823.append (by norm_num) r_147823
private theorem s_147951 : RangeOk getRow 2051521 147640 147951 :=
  s_147887.append (by norm_num) r_147887
private theorem s_148015 : RangeOk getRow 2051521 147640 148015 :=
  s_147951.append (by norm_num) r_147951
private theorem s_148079 : RangeOk getRow 2051521 147640 148079 :=
  s_148015.append (by norm_num) r_148015
private theorem s_148143 : RangeOk getRow 2051521 147640 148143 :=
  s_148079.append (by norm_num) r_148079
private theorem s_148207 : RangeOk getRow 2051521 147640 148207 :=
  s_148143.append (by norm_num) r_148143
private theorem s_148271 : RangeOk getRow 2051521 147640 148271 :=
  s_148207.append (by norm_num) r_148207
private theorem s_148335 : RangeOk getRow 2051521 147640 148335 :=
  s_148271.append (by norm_num) r_148271
private theorem s_148399 : RangeOk getRow 2051521 147640 148399 :=
  s_148335.append (by norm_num) r_148335
private theorem s_148463 : RangeOk getRow 2051521 147640 148463 :=
  s_148399.append (by norm_num) r_148399
private theorem s_148527 : RangeOk getRow 2051521 147640 148527 :=
  s_148463.append (by norm_num) r_148463
private theorem s_148591 : RangeOk getRow 2051521 147640 148591 :=
  s_148527.append (by norm_num) r_148527
private theorem s_148655 : RangeOk getRow 2051521 147640 148655 :=
  s_148591.append (by norm_num) r_148591
private theorem s_148719 : RangeOk getRow 2051521 147640 148719 :=
  s_148655.append (by norm_num) r_148655
private theorem s_148783 : RangeOk getRow 2051521 147640 148783 :=
  s_148719.append (by norm_num) r_148719
private theorem s_148847 : RangeOk getRow 2051521 147640 148847 :=
  s_148783.append (by norm_num) r_148783
private theorem s_148911 : RangeOk getRow 2051521 147640 148911 :=
  s_148847.append (by norm_num) r_148847
private theorem s_148975 : RangeOk getRow 2051521 147640 148975 :=
  s_148911.append (by norm_num) r_148911
private theorem s_149039 : RangeOk getRow 2051521 147640 149039 :=
  s_148975.append (by norm_num) r_148975
private theorem s_149103 : RangeOk getRow 2051521 147640 149103 :=
  s_149039.append (by norm_num) r_149039
private theorem s_149167 : RangeOk getRow 2051521 147640 149167 :=
  s_149103.append (by norm_num) r_149103
private theorem s_149231 : RangeOk getRow 2051521 147640 149231 :=
  s_149167.append (by norm_num) r_149167
private theorem s_149295 : RangeOk getRow 2051521 147640 149295 :=
  s_149231.append (by norm_num) r_149231
private theorem s_149359 : RangeOk getRow 2051521 147640 149359 :=
  s_149295.append (by norm_num) r_149295

/-- Rows `[147640, 149359)` are valid. -/
theorem rangeOk_147640_149359 : RangeOk getRow 2051521 147640 149359 := s_149359

end Noperthedron.Solution
