import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1225016, 1227133). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1225016 : RangeOk getRow 2051521 1225016 1225088 := by
  decide +kernel

private theorem r_1225088 : RangeOk getRow 2051521 1225088 1225160 := by
  decide +kernel

private theorem r_1225160 : RangeOk getRow 2051521 1225160 1225231 := by
  decide +kernel

private theorem r_1225231 : RangeOk getRow 2051521 1225231 1225303 := by
  decide +kernel

private theorem r_1225303 : RangeOk getRow 2051521 1225303 1225373 := by
  decide +kernel

private theorem r_1225373 : RangeOk getRow 2051521 1225373 1225441 := by
  decide +kernel

private theorem r_1225441 : RangeOk getRow 2051521 1225441 1225510 := by
  decide +kernel

private theorem r_1225510 : RangeOk getRow 2051521 1225510 1225580 := by
  decide +kernel

private theorem r_1225580 : RangeOk getRow 2051521 1225580 1225649 := by
  decide +kernel

private theorem r_1225649 : RangeOk getRow 2051521 1225649 1225719 := by
  decide +kernel

private theorem r_1225719 : RangeOk getRow 2051521 1225719 1225789 := by
  decide +kernel

private theorem r_1225789 : RangeOk getRow 2051521 1225789 1225857 := by
  decide +kernel

private theorem r_1225857 : RangeOk getRow 2051521 1225857 1225926 := by
  decide +kernel

private theorem r_1225926 : RangeOk getRow 2051521 1225926 1225997 := by
  decide +kernel

private theorem r_1225997 : RangeOk getRow 2051521 1225997 1226069 := by
  decide +kernel

private theorem r_1226069 : RangeOk getRow 2051521 1226069 1226141 := by
  decide +kernel

private theorem r_1226141 : RangeOk getRow 2051521 1226141 1226213 := by
  decide +kernel

private theorem r_1226213 : RangeOk getRow 2051521 1226213 1226285 := by
  decide +kernel

private theorem r_1226285 : RangeOk getRow 2051521 1226285 1226329 := by
  decide +kernel

private theorem r_1226329 : RangeOk getRow 2051521 1226329 1226377 := by
  decide +kernel

private theorem r_1226377 : RangeOk getRow 2051521 1226377 1226389 := by
  decide +kernel

private theorem r_1226389 : RangeOk getRow 2051521 1226389 1226417 := by
  decide +kernel

private theorem r_1226417 : RangeOk getRow 2051521 1226417 1226446 := by
  decide +kernel

private theorem r_1226446 : RangeOk getRow 2051521 1226446 1226514 := by
  decide +kernel

private theorem r_1226514 : RangeOk getRow 2051521 1226514 1226586 := by
  decide +kernel

private theorem r_1226586 : RangeOk getRow 2051521 1226586 1226624 := by
  decide +kernel

private theorem r_1226624 : RangeOk getRow 2051521 1226624 1226633 := by
  decide +kernel

private theorem r_1226633 : RangeOk getRow 2051521 1226633 1226649 := by
  decide +kernel

private theorem r_1226649 : RangeOk getRow 2051521 1226649 1226661 := by
  decide +kernel

private theorem r_1226661 : RangeOk getRow 2051521 1226661 1226671 := by
  decide +kernel

private theorem r_1226671 : RangeOk getRow 2051521 1226671 1226687 := by
  decide +kernel

private theorem r_1226687 : RangeOk getRow 2051521 1226687 1226697 := by
  decide +kernel

private theorem r_1226697 : RangeOk getRow 2051521 1226697 1226714 := by
  decide +kernel

private theorem r_1226714 : RangeOk getRow 2051521 1226714 1226787 := by
  decide +kernel

private theorem r_1226787 : RangeOk getRow 2051521 1226787 1226822 := by
  decide +kernel

private theorem r_1226822 : RangeOk getRow 2051521 1226822 1226831 := by
  decide +kernel

private theorem r_1226831 : RangeOk getRow 2051521 1226831 1226842 := by
  decide +kernel

private theorem r_1226842 : RangeOk getRow 2051521 1226842 1226861 := by
  decide +kernel

private theorem r_1226861 : RangeOk getRow 2051521 1226861 1226870 := by
  decide +kernel

private theorem r_1226870 : RangeOk getRow 2051521 1226870 1226886 := by
  decide +kernel

private theorem r_1226886 : RangeOk getRow 2051521 1226886 1226895 := by
  decide +kernel

private theorem r_1226895 : RangeOk getRow 2051521 1226895 1226917 := by
  decide +kernel

private theorem r_1226917 : RangeOk getRow 2051521 1226917 1226939 := by
  decide +kernel

private theorem r_1226939 : RangeOk getRow 2051521 1226939 1226949 := by
  decide +kernel

private theorem r_1226949 : RangeOk getRow 2051521 1226949 1226963 := by
  decide +kernel

private theorem r_1226963 : RangeOk getRow 2051521 1226963 1227016 := by
  decide +kernel

private theorem r_1227016 : RangeOk getRow 2051521 1227016 1227066 := by
  decide +kernel

private theorem r_1227066 : RangeOk getRow 2051521 1227066 1227079 := by
  decide +kernel

private theorem r_1227079 : RangeOk getRow 2051521 1227079 1227096 := by
  decide +kernel

private theorem r_1227096 : RangeOk getRow 2051521 1227096 1227112 := by
  decide +kernel

private theorem r_1227112 : RangeOk getRow 2051521 1227112 1227133 := by
  decide +kernel

private theorem s_1225088 : RangeOk getRow 2051521 1225016 1225088 := r_1225016
private theorem s_1225160 : RangeOk getRow 2051521 1225016 1225160 :=
  s_1225088.append (by norm_num) r_1225088
private theorem s_1225231 : RangeOk getRow 2051521 1225016 1225231 :=
  s_1225160.append (by norm_num) r_1225160
private theorem s_1225303 : RangeOk getRow 2051521 1225016 1225303 :=
  s_1225231.append (by norm_num) r_1225231
private theorem s_1225373 : RangeOk getRow 2051521 1225016 1225373 :=
  s_1225303.append (by norm_num) r_1225303
private theorem s_1225441 : RangeOk getRow 2051521 1225016 1225441 :=
  s_1225373.append (by norm_num) r_1225373
private theorem s_1225510 : RangeOk getRow 2051521 1225016 1225510 :=
  s_1225441.append (by norm_num) r_1225441
private theorem s_1225580 : RangeOk getRow 2051521 1225016 1225580 :=
  s_1225510.append (by norm_num) r_1225510
private theorem s_1225649 : RangeOk getRow 2051521 1225016 1225649 :=
  s_1225580.append (by norm_num) r_1225580
private theorem s_1225719 : RangeOk getRow 2051521 1225016 1225719 :=
  s_1225649.append (by norm_num) r_1225649
private theorem s_1225789 : RangeOk getRow 2051521 1225016 1225789 :=
  s_1225719.append (by norm_num) r_1225719
private theorem s_1225857 : RangeOk getRow 2051521 1225016 1225857 :=
  s_1225789.append (by norm_num) r_1225789
private theorem s_1225926 : RangeOk getRow 2051521 1225016 1225926 :=
  s_1225857.append (by norm_num) r_1225857
private theorem s_1225997 : RangeOk getRow 2051521 1225016 1225997 :=
  s_1225926.append (by norm_num) r_1225926
private theorem s_1226069 : RangeOk getRow 2051521 1225016 1226069 :=
  s_1225997.append (by norm_num) r_1225997
private theorem s_1226141 : RangeOk getRow 2051521 1225016 1226141 :=
  s_1226069.append (by norm_num) r_1226069
private theorem s_1226213 : RangeOk getRow 2051521 1225016 1226213 :=
  s_1226141.append (by norm_num) r_1226141
private theorem s_1226285 : RangeOk getRow 2051521 1225016 1226285 :=
  s_1226213.append (by norm_num) r_1226213
private theorem s_1226329 : RangeOk getRow 2051521 1225016 1226329 :=
  s_1226285.append (by norm_num) r_1226285
private theorem s_1226377 : RangeOk getRow 2051521 1225016 1226377 :=
  s_1226329.append (by norm_num) r_1226329
private theorem s_1226389 : RangeOk getRow 2051521 1225016 1226389 :=
  s_1226377.append (by norm_num) r_1226377
private theorem s_1226417 : RangeOk getRow 2051521 1225016 1226417 :=
  s_1226389.append (by norm_num) r_1226389
private theorem s_1226446 : RangeOk getRow 2051521 1225016 1226446 :=
  s_1226417.append (by norm_num) r_1226417
private theorem s_1226514 : RangeOk getRow 2051521 1225016 1226514 :=
  s_1226446.append (by norm_num) r_1226446
private theorem s_1226586 : RangeOk getRow 2051521 1225016 1226586 :=
  s_1226514.append (by norm_num) r_1226514
private theorem s_1226624 : RangeOk getRow 2051521 1225016 1226624 :=
  s_1226586.append (by norm_num) r_1226586
private theorem s_1226633 : RangeOk getRow 2051521 1225016 1226633 :=
  s_1226624.append (by norm_num) r_1226624
private theorem s_1226649 : RangeOk getRow 2051521 1225016 1226649 :=
  s_1226633.append (by norm_num) r_1226633
private theorem s_1226661 : RangeOk getRow 2051521 1225016 1226661 :=
  s_1226649.append (by norm_num) r_1226649
private theorem s_1226671 : RangeOk getRow 2051521 1225016 1226671 :=
  s_1226661.append (by norm_num) r_1226661
private theorem s_1226687 : RangeOk getRow 2051521 1225016 1226687 :=
  s_1226671.append (by norm_num) r_1226671
private theorem s_1226697 : RangeOk getRow 2051521 1225016 1226697 :=
  s_1226687.append (by norm_num) r_1226687
private theorem s_1226714 : RangeOk getRow 2051521 1225016 1226714 :=
  s_1226697.append (by norm_num) r_1226697
private theorem s_1226787 : RangeOk getRow 2051521 1225016 1226787 :=
  s_1226714.append (by norm_num) r_1226714
private theorem s_1226822 : RangeOk getRow 2051521 1225016 1226822 :=
  s_1226787.append (by norm_num) r_1226787
private theorem s_1226831 : RangeOk getRow 2051521 1225016 1226831 :=
  s_1226822.append (by norm_num) r_1226822
private theorem s_1226842 : RangeOk getRow 2051521 1225016 1226842 :=
  s_1226831.append (by norm_num) r_1226831
private theorem s_1226861 : RangeOk getRow 2051521 1225016 1226861 :=
  s_1226842.append (by norm_num) r_1226842
private theorem s_1226870 : RangeOk getRow 2051521 1225016 1226870 :=
  s_1226861.append (by norm_num) r_1226861
private theorem s_1226886 : RangeOk getRow 2051521 1225016 1226886 :=
  s_1226870.append (by norm_num) r_1226870
private theorem s_1226895 : RangeOk getRow 2051521 1225016 1226895 :=
  s_1226886.append (by norm_num) r_1226886
private theorem s_1226917 : RangeOk getRow 2051521 1225016 1226917 :=
  s_1226895.append (by norm_num) r_1226895
private theorem s_1226939 : RangeOk getRow 2051521 1225016 1226939 :=
  s_1226917.append (by norm_num) r_1226917
private theorem s_1226949 : RangeOk getRow 2051521 1225016 1226949 :=
  s_1226939.append (by norm_num) r_1226939
private theorem s_1226963 : RangeOk getRow 2051521 1225016 1226963 :=
  s_1226949.append (by norm_num) r_1226949
private theorem s_1227016 : RangeOk getRow 2051521 1225016 1227016 :=
  s_1226963.append (by norm_num) r_1226963
private theorem s_1227066 : RangeOk getRow 2051521 1225016 1227066 :=
  s_1227016.append (by norm_num) r_1227016
private theorem s_1227079 : RangeOk getRow 2051521 1225016 1227079 :=
  s_1227066.append (by norm_num) r_1227066
private theorem s_1227096 : RangeOk getRow 2051521 1225016 1227096 :=
  s_1227079.append (by norm_num) r_1227079
private theorem s_1227112 : RangeOk getRow 2051521 1225016 1227112 :=
  s_1227096.append (by norm_num) r_1227096
private theorem s_1227133 : RangeOk getRow 2051521 1225016 1227133 :=
  s_1227112.append (by norm_num) r_1227112

/-- Rows `[1225016, 1227133)` are valid. -/
theorem rangeOk_1225016_1227133 : RangeOk getRow 2051521 1225016 1227133 := s_1227133

end Noperthedron.Solution
