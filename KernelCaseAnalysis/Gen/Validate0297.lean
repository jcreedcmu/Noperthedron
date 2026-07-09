import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[716338, 718472). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_716338 : RangeOk getRow 2051521 716338 716405 := by
  decide +kernel

private theorem r_716405 : RangeOk getRow 2051521 716405 716473 := by
  decide +kernel

private theorem r_716473 : RangeOk getRow 2051521 716473 716541 := by
  decide +kernel

private theorem r_716541 : RangeOk getRow 2051521 716541 716609 := by
  decide +kernel

private theorem r_716609 : RangeOk getRow 2051521 716609 716675 := by
  decide +kernel

private theorem r_716675 : RangeOk getRow 2051521 716675 716740 := by
  decide +kernel

private theorem r_716740 : RangeOk getRow 2051521 716740 716807 := by
  decide +kernel

private theorem r_716807 : RangeOk getRow 2051521 716807 716874 := by
  decide +kernel

private theorem r_716874 : RangeOk getRow 2051521 716874 716941 := by
  decide +kernel

private theorem r_716941 : RangeOk getRow 2051521 716941 717006 := by
  decide +kernel

private theorem r_717006 : RangeOk getRow 2051521 717006 717072 := by
  decide +kernel

private theorem r_717072 : RangeOk getRow 2051521 717072 717138 := by
  decide +kernel

private theorem r_717138 : RangeOk getRow 2051521 717138 717205 := by
  decide +kernel

private theorem r_717205 : RangeOk getRow 2051521 717205 717270 := by
  decide +kernel

private theorem r_717270 : RangeOk getRow 2051521 717270 717340 := by
  decide +kernel

private theorem r_717340 : RangeOk getRow 2051521 717340 717405 := by
  decide +kernel

private theorem r_717405 : RangeOk getRow 2051521 717405 717470 := by
  decide +kernel

private theorem r_717470 : RangeOk getRow 2051521 717470 717537 := by
  decide +kernel

private theorem r_717537 : RangeOk getRow 2051521 717537 717604 := by
  decide +kernel

private theorem r_717604 : RangeOk getRow 2051521 717604 717671 := by
  decide +kernel

private theorem r_717671 : RangeOk getRow 2051521 717671 717737 := by
  decide +kernel

private theorem r_717737 : RangeOk getRow 2051521 717737 717802 := by
  decide +kernel

private theorem r_717802 : RangeOk getRow 2051521 717802 717868 := by
  decide +kernel

private theorem r_717868 : RangeOk getRow 2051521 717868 717935 := by
  decide +kernel

private theorem r_717935 : RangeOk getRow 2051521 717935 718005 := by
  decide +kernel

private theorem r_718005 : RangeOk getRow 2051521 718005 718074 := by
  decide +kernel

private theorem r_718074 : RangeOk getRow 2051521 718074 718141 := by
  decide +kernel

private theorem r_718141 : RangeOk getRow 2051521 718141 718207 := by
  decide +kernel

private theorem r_718207 : RangeOk getRow 2051521 718207 718272 := by
  decide +kernel

private theorem r_718272 : RangeOk getRow 2051521 718272 718338 := by
  decide +kernel

private theorem r_718338 : RangeOk getRow 2051521 718338 718404 := by
  decide +kernel

private theorem r_718404 : RangeOk getRow 2051521 718404 718472 := by
  decide +kernel

private theorem s_716405 : RangeOk getRow 2051521 716338 716405 := r_716338
private theorem s_716473 : RangeOk getRow 2051521 716338 716473 :=
  s_716405.append (by norm_num) r_716405
private theorem s_716541 : RangeOk getRow 2051521 716338 716541 :=
  s_716473.append (by norm_num) r_716473
private theorem s_716609 : RangeOk getRow 2051521 716338 716609 :=
  s_716541.append (by norm_num) r_716541
private theorem s_716675 : RangeOk getRow 2051521 716338 716675 :=
  s_716609.append (by norm_num) r_716609
private theorem s_716740 : RangeOk getRow 2051521 716338 716740 :=
  s_716675.append (by norm_num) r_716675
private theorem s_716807 : RangeOk getRow 2051521 716338 716807 :=
  s_716740.append (by norm_num) r_716740
private theorem s_716874 : RangeOk getRow 2051521 716338 716874 :=
  s_716807.append (by norm_num) r_716807
private theorem s_716941 : RangeOk getRow 2051521 716338 716941 :=
  s_716874.append (by norm_num) r_716874
private theorem s_717006 : RangeOk getRow 2051521 716338 717006 :=
  s_716941.append (by norm_num) r_716941
private theorem s_717072 : RangeOk getRow 2051521 716338 717072 :=
  s_717006.append (by norm_num) r_717006
private theorem s_717138 : RangeOk getRow 2051521 716338 717138 :=
  s_717072.append (by norm_num) r_717072
private theorem s_717205 : RangeOk getRow 2051521 716338 717205 :=
  s_717138.append (by norm_num) r_717138
private theorem s_717270 : RangeOk getRow 2051521 716338 717270 :=
  s_717205.append (by norm_num) r_717205
private theorem s_717340 : RangeOk getRow 2051521 716338 717340 :=
  s_717270.append (by norm_num) r_717270
private theorem s_717405 : RangeOk getRow 2051521 716338 717405 :=
  s_717340.append (by norm_num) r_717340
private theorem s_717470 : RangeOk getRow 2051521 716338 717470 :=
  s_717405.append (by norm_num) r_717405
private theorem s_717537 : RangeOk getRow 2051521 716338 717537 :=
  s_717470.append (by norm_num) r_717470
private theorem s_717604 : RangeOk getRow 2051521 716338 717604 :=
  s_717537.append (by norm_num) r_717537
private theorem s_717671 : RangeOk getRow 2051521 716338 717671 :=
  s_717604.append (by norm_num) r_717604
private theorem s_717737 : RangeOk getRow 2051521 716338 717737 :=
  s_717671.append (by norm_num) r_717671
private theorem s_717802 : RangeOk getRow 2051521 716338 717802 :=
  s_717737.append (by norm_num) r_717737
private theorem s_717868 : RangeOk getRow 2051521 716338 717868 :=
  s_717802.append (by norm_num) r_717802
private theorem s_717935 : RangeOk getRow 2051521 716338 717935 :=
  s_717868.append (by norm_num) r_717868
private theorem s_718005 : RangeOk getRow 2051521 716338 718005 :=
  s_717935.append (by norm_num) r_717935
private theorem s_718074 : RangeOk getRow 2051521 716338 718074 :=
  s_718005.append (by norm_num) r_718005
private theorem s_718141 : RangeOk getRow 2051521 716338 718141 :=
  s_718074.append (by norm_num) r_718074
private theorem s_718207 : RangeOk getRow 2051521 716338 718207 :=
  s_718141.append (by norm_num) r_718141
private theorem s_718272 : RangeOk getRow 2051521 716338 718272 :=
  s_718207.append (by norm_num) r_718207
private theorem s_718338 : RangeOk getRow 2051521 716338 718338 :=
  s_718272.append (by norm_num) r_718272
private theorem s_718404 : RangeOk getRow 2051521 716338 718404 :=
  s_718338.append (by norm_num) r_718338
private theorem s_718472 : RangeOk getRow 2051521 716338 718472 :=
  s_718404.append (by norm_num) r_718404

/-- Rows `[716338, 718472)` are valid. -/
theorem rangeOk_716338_718472 : RangeOk getRow 2051521 716338 718472 := s_718472

end Noperthedron.Solution
