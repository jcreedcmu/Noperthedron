import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1146680, 1149465). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1146680 : RangeOk getRow 2051521 1146680 1146751 := by
  decide +kernel

private theorem r_1146751 : RangeOk getRow 2051521 1146751 1146821 := by
  decide +kernel

private theorem r_1146821 : RangeOk getRow 2051521 1146821 1146892 := by
  decide +kernel

private theorem r_1146892 : RangeOk getRow 2051521 1146892 1146963 := by
  decide +kernel

private theorem r_1146963 : RangeOk getRow 2051521 1146963 1147036 := by
  decide +kernel

private theorem r_1147036 : RangeOk getRow 2051521 1147036 1147108 := by
  decide +kernel

private theorem r_1147108 : RangeOk getRow 2051521 1147108 1147179 := by
  decide +kernel

private theorem r_1147179 : RangeOk getRow 2051521 1147179 1147248 := by
  decide +kernel

private theorem r_1147248 : RangeOk getRow 2051521 1147248 1147314 := by
  decide +kernel

private theorem r_1147314 : RangeOk getRow 2051521 1147314 1147383 := by
  decide +kernel

private theorem r_1147383 : RangeOk getRow 2051521 1147383 1147453 := by
  decide +kernel

private theorem r_1147453 : RangeOk getRow 2051521 1147453 1147524 := by
  decide +kernel

private theorem r_1147524 : RangeOk getRow 2051521 1147524 1147595 := by
  decide +kernel

private theorem r_1147595 : RangeOk getRow 2051521 1147595 1147666 := by
  decide +kernel

private theorem r_1147666 : RangeOk getRow 2051521 1147666 1147735 := by
  decide +kernel

private theorem r_1147735 : RangeOk getRow 2051521 1147735 1147804 := by
  decide +kernel

private theorem r_1147804 : RangeOk getRow 2051521 1147804 1147870 := by
  decide +kernel

private theorem r_1147870 : RangeOk getRow 2051521 1147870 1147939 := by
  decide +kernel

private theorem r_1147939 : RangeOk getRow 2051521 1147939 1148008 := by
  decide +kernel

private theorem r_1148008 : RangeOk getRow 2051521 1148008 1148074 := by
  decide +kernel

private theorem r_1148074 : RangeOk getRow 2051521 1148074 1148143 := by
  decide +kernel

private theorem r_1148143 : RangeOk getRow 2051521 1148143 1148213 := by
  decide +kernel

private theorem r_1148213 : RangeOk getRow 2051521 1148213 1148285 := by
  decide +kernel

private theorem r_1148285 : RangeOk getRow 2051521 1148285 1148357 := by
  decide +kernel

private theorem r_1148357 : RangeOk getRow 2051521 1148357 1148428 := by
  decide +kernel

private theorem r_1148428 : RangeOk getRow 2051521 1148428 1148496 := by
  decide +kernel

private theorem r_1148496 : RangeOk getRow 2051521 1148496 1148564 := by
  decide +kernel

private theorem r_1148564 : RangeOk getRow 2051521 1148564 1148631 := by
  decide +kernel

private theorem r_1148631 : RangeOk getRow 2051521 1148631 1148699 := by
  decide +kernel

private theorem r_1148699 : RangeOk getRow 2051521 1148699 1148771 := by
  decide +kernel

private theorem r_1148771 : RangeOk getRow 2051521 1148771 1148841 := by
  decide +kernel

private theorem r_1148841 : RangeOk getRow 2051521 1148841 1148912 := by
  decide +kernel

private theorem r_1148912 : RangeOk getRow 2051521 1148912 1148982 := by
  decide +kernel

private theorem r_1148982 : RangeOk getRow 2051521 1148982 1149048 := by
  decide +kernel

private theorem r_1149048 : RangeOk getRow 2051521 1149048 1149115 := by
  decide +kernel

private theorem r_1149115 : RangeOk getRow 2051521 1149115 1149184 := by
  decide +kernel

private theorem r_1149184 : RangeOk getRow 2051521 1149184 1149255 := by
  decide +kernel

private theorem r_1149255 : RangeOk getRow 2051521 1149255 1149325 := by
  decide +kernel

private theorem r_1149325 : RangeOk getRow 2051521 1149325 1149395 := by
  decide +kernel

private theorem r_1149395 : RangeOk getRow 2051521 1149395 1149465 := by
  decide +kernel

private theorem s_1146751 : RangeOk getRow 2051521 1146680 1146751 := r_1146680
private theorem s_1146821 : RangeOk getRow 2051521 1146680 1146821 :=
  s_1146751.append (by norm_num) r_1146751
private theorem s_1146892 : RangeOk getRow 2051521 1146680 1146892 :=
  s_1146821.append (by norm_num) r_1146821
private theorem s_1146963 : RangeOk getRow 2051521 1146680 1146963 :=
  s_1146892.append (by norm_num) r_1146892
private theorem s_1147036 : RangeOk getRow 2051521 1146680 1147036 :=
  s_1146963.append (by norm_num) r_1146963
private theorem s_1147108 : RangeOk getRow 2051521 1146680 1147108 :=
  s_1147036.append (by norm_num) r_1147036
private theorem s_1147179 : RangeOk getRow 2051521 1146680 1147179 :=
  s_1147108.append (by norm_num) r_1147108
private theorem s_1147248 : RangeOk getRow 2051521 1146680 1147248 :=
  s_1147179.append (by norm_num) r_1147179
private theorem s_1147314 : RangeOk getRow 2051521 1146680 1147314 :=
  s_1147248.append (by norm_num) r_1147248
private theorem s_1147383 : RangeOk getRow 2051521 1146680 1147383 :=
  s_1147314.append (by norm_num) r_1147314
private theorem s_1147453 : RangeOk getRow 2051521 1146680 1147453 :=
  s_1147383.append (by norm_num) r_1147383
private theorem s_1147524 : RangeOk getRow 2051521 1146680 1147524 :=
  s_1147453.append (by norm_num) r_1147453
private theorem s_1147595 : RangeOk getRow 2051521 1146680 1147595 :=
  s_1147524.append (by norm_num) r_1147524
private theorem s_1147666 : RangeOk getRow 2051521 1146680 1147666 :=
  s_1147595.append (by norm_num) r_1147595
private theorem s_1147735 : RangeOk getRow 2051521 1146680 1147735 :=
  s_1147666.append (by norm_num) r_1147666
private theorem s_1147804 : RangeOk getRow 2051521 1146680 1147804 :=
  s_1147735.append (by norm_num) r_1147735
private theorem s_1147870 : RangeOk getRow 2051521 1146680 1147870 :=
  s_1147804.append (by norm_num) r_1147804
private theorem s_1147939 : RangeOk getRow 2051521 1146680 1147939 :=
  s_1147870.append (by norm_num) r_1147870
private theorem s_1148008 : RangeOk getRow 2051521 1146680 1148008 :=
  s_1147939.append (by norm_num) r_1147939
private theorem s_1148074 : RangeOk getRow 2051521 1146680 1148074 :=
  s_1148008.append (by norm_num) r_1148008
private theorem s_1148143 : RangeOk getRow 2051521 1146680 1148143 :=
  s_1148074.append (by norm_num) r_1148074
private theorem s_1148213 : RangeOk getRow 2051521 1146680 1148213 :=
  s_1148143.append (by norm_num) r_1148143
private theorem s_1148285 : RangeOk getRow 2051521 1146680 1148285 :=
  s_1148213.append (by norm_num) r_1148213
private theorem s_1148357 : RangeOk getRow 2051521 1146680 1148357 :=
  s_1148285.append (by norm_num) r_1148285
private theorem s_1148428 : RangeOk getRow 2051521 1146680 1148428 :=
  s_1148357.append (by norm_num) r_1148357
private theorem s_1148496 : RangeOk getRow 2051521 1146680 1148496 :=
  s_1148428.append (by norm_num) r_1148428
private theorem s_1148564 : RangeOk getRow 2051521 1146680 1148564 :=
  s_1148496.append (by norm_num) r_1148496
private theorem s_1148631 : RangeOk getRow 2051521 1146680 1148631 :=
  s_1148564.append (by norm_num) r_1148564
private theorem s_1148699 : RangeOk getRow 2051521 1146680 1148699 :=
  s_1148631.append (by norm_num) r_1148631
private theorem s_1148771 : RangeOk getRow 2051521 1146680 1148771 :=
  s_1148699.append (by norm_num) r_1148699
private theorem s_1148841 : RangeOk getRow 2051521 1146680 1148841 :=
  s_1148771.append (by norm_num) r_1148771
private theorem s_1148912 : RangeOk getRow 2051521 1146680 1148912 :=
  s_1148841.append (by norm_num) r_1148841
private theorem s_1148982 : RangeOk getRow 2051521 1146680 1148982 :=
  s_1148912.append (by norm_num) r_1148912
private theorem s_1149048 : RangeOk getRow 2051521 1146680 1149048 :=
  s_1148982.append (by norm_num) r_1148982
private theorem s_1149115 : RangeOk getRow 2051521 1146680 1149115 :=
  s_1149048.append (by norm_num) r_1149048
private theorem s_1149184 : RangeOk getRow 2051521 1146680 1149184 :=
  s_1149115.append (by norm_num) r_1149115
private theorem s_1149255 : RangeOk getRow 2051521 1146680 1149255 :=
  s_1149184.append (by norm_num) r_1149184
private theorem s_1149325 : RangeOk getRow 2051521 1146680 1149325 :=
  s_1149255.append (by norm_num) r_1149255
private theorem s_1149395 : RangeOk getRow 2051521 1146680 1149395 :=
  s_1149325.append (by norm_num) r_1149325
private theorem s_1149465 : RangeOk getRow 2051521 1146680 1149465 :=
  s_1149395.append (by norm_num) r_1149395

/-- Rows `[1146680, 1149465)` are valid. -/
theorem rangeOk_1146680_1149465 : RangeOk getRow 2051521 1146680 1149465 := s_1149465

end Noperthedron.Solution
