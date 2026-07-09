import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[933415, 935791). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_933415 : RangeOk getRow 2051521 933415 933483 := by
  decide +kernel

private theorem r_933483 : RangeOk getRow 2051521 933483 933553 := by
  decide +kernel

private theorem r_933553 : RangeOk getRow 2051521 933553 933623 := by
  decide +kernel

private theorem r_933623 : RangeOk getRow 2051521 933623 933690 := by
  decide +kernel

private theorem r_933690 : RangeOk getRow 2051521 933690 933758 := by
  decide +kernel

private theorem r_933758 : RangeOk getRow 2051521 933758 933825 := by
  decide +kernel

private theorem r_933825 : RangeOk getRow 2051521 933825 933892 := by
  decide +kernel

private theorem r_933892 : RangeOk getRow 2051521 933892 933958 := by
  decide +kernel

private theorem r_933958 : RangeOk getRow 2051521 933958 934024 := by
  decide +kernel

private theorem r_934024 : RangeOk getRow 2051521 934024 934093 := by
  decide +kernel

private theorem r_934093 : RangeOk getRow 2051521 934093 934165 := by
  decide +kernel

private theorem r_934165 : RangeOk getRow 2051521 934165 934233 := by
  decide +kernel

private theorem r_934233 : RangeOk getRow 2051521 934233 934301 := by
  decide +kernel

private theorem r_934301 : RangeOk getRow 2051521 934301 934369 := by
  decide +kernel

private theorem r_934369 : RangeOk getRow 2051521 934369 934440 := by
  decide +kernel

private theorem r_934440 : RangeOk getRow 2051521 934440 934508 := by
  decide +kernel

private theorem r_934508 : RangeOk getRow 2051521 934508 934575 := by
  decide +kernel

private theorem r_934575 : RangeOk getRow 2051521 934575 934642 := by
  decide +kernel

private theorem r_934642 : RangeOk getRow 2051521 934642 934707 := by
  decide +kernel

private theorem r_934707 : RangeOk getRow 2051521 934707 934775 := by
  decide +kernel

private theorem r_934775 : RangeOk getRow 2051521 934775 934842 := by
  decide +kernel

private theorem r_934842 : RangeOk getRow 2051521 934842 934907 := by
  decide +kernel

private theorem r_934907 : RangeOk getRow 2051521 934907 934975 := by
  decide +kernel

private theorem r_934975 : RangeOk getRow 2051521 934975 935046 := by
  decide +kernel

private theorem r_935046 : RangeOk getRow 2051521 935046 935115 := by
  decide +kernel

private theorem r_935115 : RangeOk getRow 2051521 935115 935183 := by
  decide +kernel

private theorem r_935183 : RangeOk getRow 2051521 935183 935249 := by
  decide +kernel

private theorem r_935249 : RangeOk getRow 2051521 935249 935317 := by
  decide +kernel

private theorem r_935317 : RangeOk getRow 2051521 935317 935384 := by
  decide +kernel

private theorem r_935384 : RangeOk getRow 2051521 935384 935451 := by
  decide +kernel

private theorem r_935451 : RangeOk getRow 2051521 935451 935518 := by
  decide +kernel

private theorem r_935518 : RangeOk getRow 2051521 935518 935586 := by
  decide +kernel

private theorem r_935586 : RangeOk getRow 2051521 935586 935651 := by
  decide +kernel

private theorem r_935651 : RangeOk getRow 2051521 935651 935723 := by
  decide +kernel

private theorem r_935723 : RangeOk getRow 2051521 935723 935791 := by
  decide +kernel

private theorem s_933483 : RangeOk getRow 2051521 933415 933483 := r_933415
private theorem s_933553 : RangeOk getRow 2051521 933415 933553 :=
  s_933483.append (by norm_num) r_933483
private theorem s_933623 : RangeOk getRow 2051521 933415 933623 :=
  s_933553.append (by norm_num) r_933553
private theorem s_933690 : RangeOk getRow 2051521 933415 933690 :=
  s_933623.append (by norm_num) r_933623
private theorem s_933758 : RangeOk getRow 2051521 933415 933758 :=
  s_933690.append (by norm_num) r_933690
private theorem s_933825 : RangeOk getRow 2051521 933415 933825 :=
  s_933758.append (by norm_num) r_933758
private theorem s_933892 : RangeOk getRow 2051521 933415 933892 :=
  s_933825.append (by norm_num) r_933825
private theorem s_933958 : RangeOk getRow 2051521 933415 933958 :=
  s_933892.append (by norm_num) r_933892
private theorem s_934024 : RangeOk getRow 2051521 933415 934024 :=
  s_933958.append (by norm_num) r_933958
private theorem s_934093 : RangeOk getRow 2051521 933415 934093 :=
  s_934024.append (by norm_num) r_934024
private theorem s_934165 : RangeOk getRow 2051521 933415 934165 :=
  s_934093.append (by norm_num) r_934093
private theorem s_934233 : RangeOk getRow 2051521 933415 934233 :=
  s_934165.append (by norm_num) r_934165
private theorem s_934301 : RangeOk getRow 2051521 933415 934301 :=
  s_934233.append (by norm_num) r_934233
private theorem s_934369 : RangeOk getRow 2051521 933415 934369 :=
  s_934301.append (by norm_num) r_934301
private theorem s_934440 : RangeOk getRow 2051521 933415 934440 :=
  s_934369.append (by norm_num) r_934369
private theorem s_934508 : RangeOk getRow 2051521 933415 934508 :=
  s_934440.append (by norm_num) r_934440
private theorem s_934575 : RangeOk getRow 2051521 933415 934575 :=
  s_934508.append (by norm_num) r_934508
private theorem s_934642 : RangeOk getRow 2051521 933415 934642 :=
  s_934575.append (by norm_num) r_934575
private theorem s_934707 : RangeOk getRow 2051521 933415 934707 :=
  s_934642.append (by norm_num) r_934642
private theorem s_934775 : RangeOk getRow 2051521 933415 934775 :=
  s_934707.append (by norm_num) r_934707
private theorem s_934842 : RangeOk getRow 2051521 933415 934842 :=
  s_934775.append (by norm_num) r_934775
private theorem s_934907 : RangeOk getRow 2051521 933415 934907 :=
  s_934842.append (by norm_num) r_934842
private theorem s_934975 : RangeOk getRow 2051521 933415 934975 :=
  s_934907.append (by norm_num) r_934907
private theorem s_935046 : RangeOk getRow 2051521 933415 935046 :=
  s_934975.append (by norm_num) r_934975
private theorem s_935115 : RangeOk getRow 2051521 933415 935115 :=
  s_935046.append (by norm_num) r_935046
private theorem s_935183 : RangeOk getRow 2051521 933415 935183 :=
  s_935115.append (by norm_num) r_935115
private theorem s_935249 : RangeOk getRow 2051521 933415 935249 :=
  s_935183.append (by norm_num) r_935183
private theorem s_935317 : RangeOk getRow 2051521 933415 935317 :=
  s_935249.append (by norm_num) r_935249
private theorem s_935384 : RangeOk getRow 2051521 933415 935384 :=
  s_935317.append (by norm_num) r_935317
private theorem s_935451 : RangeOk getRow 2051521 933415 935451 :=
  s_935384.append (by norm_num) r_935384
private theorem s_935518 : RangeOk getRow 2051521 933415 935518 :=
  s_935451.append (by norm_num) r_935451
private theorem s_935586 : RangeOk getRow 2051521 933415 935586 :=
  s_935518.append (by norm_num) r_935518
private theorem s_935651 : RangeOk getRow 2051521 933415 935651 :=
  s_935586.append (by norm_num) r_935586
private theorem s_935723 : RangeOk getRow 2051521 933415 935723 :=
  s_935651.append (by norm_num) r_935651
private theorem s_935791 : RangeOk getRow 2051521 933415 935791 :=
  s_935723.append (by norm_num) r_935723

/-- Rows `[933415, 935791)` are valid. -/
theorem rangeOk_933415_935791 : RangeOk getRow 2051521 933415 935791 := s_935791

end Noperthedron.Solution
