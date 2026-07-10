import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[36057, 37786). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_36057 : RangeOk getRow 2051521 36057 36121 := by
  decide +kernel

private theorem r_36121 : RangeOk getRow 2051521 36121 36185 := by
  decide +kernel

private theorem r_36185 : RangeOk getRow 2051521 36185 36250 := by
  decide +kernel

private theorem r_36250 : RangeOk getRow 2051521 36250 36314 := by
  decide +kernel

private theorem r_36314 : RangeOk getRow 2051521 36314 36378 := by
  decide +kernel

private theorem r_36378 : RangeOk getRow 2051521 36378 36442 := by
  decide +kernel

private theorem r_36442 : RangeOk getRow 2051521 36442 36506 := by
  decide +kernel

private theorem r_36506 : RangeOk getRow 2051521 36506 36570 := by
  decide +kernel

private theorem r_36570 : RangeOk getRow 2051521 36570 36634 := by
  decide +kernel

private theorem r_36634 : RangeOk getRow 2051521 36634 36698 := by
  decide +kernel

private theorem r_36698 : RangeOk getRow 2051521 36698 36762 := by
  decide +kernel

private theorem r_36762 : RangeOk getRow 2051521 36762 36826 := by
  decide +kernel

private theorem r_36826 : RangeOk getRow 2051521 36826 36890 := by
  decide +kernel

private theorem r_36890 : RangeOk getRow 2051521 36890 36954 := by
  decide +kernel

private theorem r_36954 : RangeOk getRow 2051521 36954 37018 := by
  decide +kernel

private theorem r_37018 : RangeOk getRow 2051521 37018 37082 := by
  decide +kernel

private theorem r_37082 : RangeOk getRow 2051521 37082 37146 := by
  decide +kernel

private theorem r_37146 : RangeOk getRow 2051521 37146 37210 := by
  decide +kernel

private theorem r_37210 : RangeOk getRow 2051521 37210 37274 := by
  decide +kernel

private theorem r_37274 : RangeOk getRow 2051521 37274 37338 := by
  decide +kernel

private theorem r_37338 : RangeOk getRow 2051521 37338 37402 := by
  decide +kernel

private theorem r_37402 : RangeOk getRow 2051521 37402 37466 := by
  decide +kernel

private theorem r_37466 : RangeOk getRow 2051521 37466 37530 := by
  decide +kernel

private theorem r_37530 : RangeOk getRow 2051521 37530 37594 := by
  decide +kernel

private theorem r_37594 : RangeOk getRow 2051521 37594 37658 := by
  decide +kernel

private theorem r_37658 : RangeOk getRow 2051521 37658 37722 := by
  decide +kernel

private theorem r_37722 : RangeOk getRow 2051521 37722 37786 := by
  decide +kernel

private theorem s_36121 : RangeOk getRow 2051521 36057 36121 := r_36057
private theorem s_36185 : RangeOk getRow 2051521 36057 36185 :=
  s_36121.append (by norm_num) r_36121
private theorem s_36250 : RangeOk getRow 2051521 36057 36250 :=
  s_36185.append (by norm_num) r_36185
private theorem s_36314 : RangeOk getRow 2051521 36057 36314 :=
  s_36250.append (by norm_num) r_36250
private theorem s_36378 : RangeOk getRow 2051521 36057 36378 :=
  s_36314.append (by norm_num) r_36314
private theorem s_36442 : RangeOk getRow 2051521 36057 36442 :=
  s_36378.append (by norm_num) r_36378
private theorem s_36506 : RangeOk getRow 2051521 36057 36506 :=
  s_36442.append (by norm_num) r_36442
private theorem s_36570 : RangeOk getRow 2051521 36057 36570 :=
  s_36506.append (by norm_num) r_36506
private theorem s_36634 : RangeOk getRow 2051521 36057 36634 :=
  s_36570.append (by norm_num) r_36570
private theorem s_36698 : RangeOk getRow 2051521 36057 36698 :=
  s_36634.append (by norm_num) r_36634
private theorem s_36762 : RangeOk getRow 2051521 36057 36762 :=
  s_36698.append (by norm_num) r_36698
private theorem s_36826 : RangeOk getRow 2051521 36057 36826 :=
  s_36762.append (by norm_num) r_36762
private theorem s_36890 : RangeOk getRow 2051521 36057 36890 :=
  s_36826.append (by norm_num) r_36826
private theorem s_36954 : RangeOk getRow 2051521 36057 36954 :=
  s_36890.append (by norm_num) r_36890
private theorem s_37018 : RangeOk getRow 2051521 36057 37018 :=
  s_36954.append (by norm_num) r_36954
private theorem s_37082 : RangeOk getRow 2051521 36057 37082 :=
  s_37018.append (by norm_num) r_37018
private theorem s_37146 : RangeOk getRow 2051521 36057 37146 :=
  s_37082.append (by norm_num) r_37082
private theorem s_37210 : RangeOk getRow 2051521 36057 37210 :=
  s_37146.append (by norm_num) r_37146
private theorem s_37274 : RangeOk getRow 2051521 36057 37274 :=
  s_37210.append (by norm_num) r_37210
private theorem s_37338 : RangeOk getRow 2051521 36057 37338 :=
  s_37274.append (by norm_num) r_37274
private theorem s_37402 : RangeOk getRow 2051521 36057 37402 :=
  s_37338.append (by norm_num) r_37338
private theorem s_37466 : RangeOk getRow 2051521 36057 37466 :=
  s_37402.append (by norm_num) r_37402
private theorem s_37530 : RangeOk getRow 2051521 36057 37530 :=
  s_37466.append (by norm_num) r_37466
private theorem s_37594 : RangeOk getRow 2051521 36057 37594 :=
  s_37530.append (by norm_num) r_37530
private theorem s_37658 : RangeOk getRow 2051521 36057 37658 :=
  s_37594.append (by norm_num) r_37594
private theorem s_37722 : RangeOk getRow 2051521 36057 37722 :=
  s_37658.append (by norm_num) r_37658
private theorem s_37786 : RangeOk getRow 2051521 36057 37786 :=
  s_37722.append (by norm_num) r_37722

/-- Rows `[36057, 37786)` are valid. -/
theorem rangeOk_36057_37786 : RangeOk getRow 2051521 36057 37786 := s_37786

end Noperthedron.Solution
