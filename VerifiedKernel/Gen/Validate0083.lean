import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[186255, 187987). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_186255 : RangeOk getRow 2051521 186255 186320 := by
  decide +kernel

private theorem r_186320 : RangeOk getRow 2051521 186320 186384 := by
  decide +kernel

private theorem r_186384 : RangeOk getRow 2051521 186384 186448 := by
  decide +kernel

private theorem r_186448 : RangeOk getRow 2051521 186448 186512 := by
  decide +kernel

private theorem r_186512 : RangeOk getRow 2051521 186512 186576 := by
  decide +kernel

private theorem r_186576 : RangeOk getRow 2051521 186576 186640 := by
  decide +kernel

private theorem r_186640 : RangeOk getRow 2051521 186640 186704 := by
  decide +kernel

private theorem r_186704 : RangeOk getRow 2051521 186704 186769 := by
  decide +kernel

private theorem r_186769 : RangeOk getRow 2051521 186769 186833 := by
  decide +kernel

private theorem r_186833 : RangeOk getRow 2051521 186833 186897 := by
  decide +kernel

private theorem r_186897 : RangeOk getRow 2051521 186897 186961 := by
  decide +kernel

private theorem r_186961 : RangeOk getRow 2051521 186961 187025 := by
  decide +kernel

private theorem r_187025 : RangeOk getRow 2051521 187025 187089 := by
  decide +kernel

private theorem r_187089 : RangeOk getRow 2051521 187089 187153 := by
  decide +kernel

private theorem r_187153 : RangeOk getRow 2051521 187153 187218 := by
  decide +kernel

private theorem r_187218 : RangeOk getRow 2051521 187218 187282 := by
  decide +kernel

private theorem r_187282 : RangeOk getRow 2051521 187282 187346 := by
  decide +kernel

private theorem r_187346 : RangeOk getRow 2051521 187346 187410 := by
  decide +kernel

private theorem r_187410 : RangeOk getRow 2051521 187410 187474 := by
  decide +kernel

private theorem r_187474 : RangeOk getRow 2051521 187474 187538 := by
  decide +kernel

private theorem r_187538 : RangeOk getRow 2051521 187538 187602 := by
  decide +kernel

private theorem r_187602 : RangeOk getRow 2051521 187602 187667 := by
  decide +kernel

private theorem r_187667 : RangeOk getRow 2051521 187667 187731 := by
  decide +kernel

private theorem r_187731 : RangeOk getRow 2051521 187731 187795 := by
  decide +kernel

private theorem r_187795 : RangeOk getRow 2051521 187795 187859 := by
  decide +kernel

private theorem r_187859 : RangeOk getRow 2051521 187859 187923 := by
  decide +kernel

private theorem r_187923 : RangeOk getRow 2051521 187923 187987 := by
  decide +kernel

private theorem s_186320 : RangeOk getRow 2051521 186255 186320 := r_186255
private theorem s_186384 : RangeOk getRow 2051521 186255 186384 :=
  s_186320.append (by norm_num) r_186320
private theorem s_186448 : RangeOk getRow 2051521 186255 186448 :=
  s_186384.append (by norm_num) r_186384
private theorem s_186512 : RangeOk getRow 2051521 186255 186512 :=
  s_186448.append (by norm_num) r_186448
private theorem s_186576 : RangeOk getRow 2051521 186255 186576 :=
  s_186512.append (by norm_num) r_186512
private theorem s_186640 : RangeOk getRow 2051521 186255 186640 :=
  s_186576.append (by norm_num) r_186576
private theorem s_186704 : RangeOk getRow 2051521 186255 186704 :=
  s_186640.append (by norm_num) r_186640
private theorem s_186769 : RangeOk getRow 2051521 186255 186769 :=
  s_186704.append (by norm_num) r_186704
private theorem s_186833 : RangeOk getRow 2051521 186255 186833 :=
  s_186769.append (by norm_num) r_186769
private theorem s_186897 : RangeOk getRow 2051521 186255 186897 :=
  s_186833.append (by norm_num) r_186833
private theorem s_186961 : RangeOk getRow 2051521 186255 186961 :=
  s_186897.append (by norm_num) r_186897
private theorem s_187025 : RangeOk getRow 2051521 186255 187025 :=
  s_186961.append (by norm_num) r_186961
private theorem s_187089 : RangeOk getRow 2051521 186255 187089 :=
  s_187025.append (by norm_num) r_187025
private theorem s_187153 : RangeOk getRow 2051521 186255 187153 :=
  s_187089.append (by norm_num) r_187089
private theorem s_187218 : RangeOk getRow 2051521 186255 187218 :=
  s_187153.append (by norm_num) r_187153
private theorem s_187282 : RangeOk getRow 2051521 186255 187282 :=
  s_187218.append (by norm_num) r_187218
private theorem s_187346 : RangeOk getRow 2051521 186255 187346 :=
  s_187282.append (by norm_num) r_187282
private theorem s_187410 : RangeOk getRow 2051521 186255 187410 :=
  s_187346.append (by norm_num) r_187346
private theorem s_187474 : RangeOk getRow 2051521 186255 187474 :=
  s_187410.append (by norm_num) r_187410
private theorem s_187538 : RangeOk getRow 2051521 186255 187538 :=
  s_187474.append (by norm_num) r_187474
private theorem s_187602 : RangeOk getRow 2051521 186255 187602 :=
  s_187538.append (by norm_num) r_187538
private theorem s_187667 : RangeOk getRow 2051521 186255 187667 :=
  s_187602.append (by norm_num) r_187602
private theorem s_187731 : RangeOk getRow 2051521 186255 187731 :=
  s_187667.append (by norm_num) r_187667
private theorem s_187795 : RangeOk getRow 2051521 186255 187795 :=
  s_187731.append (by norm_num) r_187731
private theorem s_187859 : RangeOk getRow 2051521 186255 187859 :=
  s_187795.append (by norm_num) r_187795
private theorem s_187923 : RangeOk getRow 2051521 186255 187923 :=
  s_187859.append (by norm_num) r_187859
private theorem s_187987 : RangeOk getRow 2051521 186255 187987 :=
  s_187923.append (by norm_num) r_187923

/-- Rows `[186255, 187987)` are valid. -/
theorem rangeOk_186255_187987 : RangeOk getRow 2051521 186255 187987 := s_187987

end Noperthedron.Solution
