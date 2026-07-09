import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[687545, 689830). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_687545 : RangeOk getRow 2051521 687545 687615 := by
  decide +kernel

private theorem r_687615 : RangeOk getRow 2051521 687615 687684 := by
  decide +kernel

private theorem r_687684 : RangeOk getRow 2051521 687684 687751 := by
  decide +kernel

private theorem r_687751 : RangeOk getRow 2051521 687751 687818 := by
  decide +kernel

private theorem r_687818 : RangeOk getRow 2051521 687818 687887 := by
  decide +kernel

private theorem r_687887 : RangeOk getRow 2051521 687887 687955 := by
  decide +kernel

private theorem r_687955 : RangeOk getRow 2051521 687955 688021 := by
  decide +kernel

private theorem r_688021 : RangeOk getRow 2051521 688021 688086 := by
  decide +kernel

private theorem r_688086 : RangeOk getRow 2051521 688086 688153 := by
  decide +kernel

private theorem r_688153 : RangeOk getRow 2051521 688153 688220 := by
  decide +kernel

private theorem r_688220 : RangeOk getRow 2051521 688220 688288 := by
  decide +kernel

private theorem r_688288 : RangeOk getRow 2051521 688288 688356 := by
  decide +kernel

private theorem r_688356 : RangeOk getRow 2051521 688356 688424 := by
  decide +kernel

private theorem r_688424 : RangeOk getRow 2051521 688424 688493 := by
  decide +kernel

private theorem r_688493 : RangeOk getRow 2051521 688493 688561 := by
  decide +kernel

private theorem r_688561 : RangeOk getRow 2051521 688561 688628 := by
  decide +kernel

private theorem r_688628 : RangeOk getRow 2051521 688628 688695 := by
  decide +kernel

private theorem r_688695 : RangeOk getRow 2051521 688695 688760 := by
  decide +kernel

private theorem r_688760 : RangeOk getRow 2051521 688760 688825 := by
  decide +kernel

private theorem r_688825 : RangeOk getRow 2051521 688825 688891 := by
  decide +kernel

private theorem r_688891 : RangeOk getRow 2051521 688891 688959 := by
  decide +kernel

private theorem r_688959 : RangeOk getRow 2051521 688959 689026 := by
  decide +kernel

private theorem r_689026 : RangeOk getRow 2051521 689026 689093 := by
  decide +kernel

private theorem r_689093 : RangeOk getRow 2051521 689093 689159 := by
  decide +kernel

private theorem r_689159 : RangeOk getRow 2051521 689159 689225 := by
  decide +kernel

private theorem r_689225 : RangeOk getRow 2051521 689225 689292 := by
  decide +kernel

private theorem r_689292 : RangeOk getRow 2051521 689292 689361 := by
  decide +kernel

private theorem r_689361 : RangeOk getRow 2051521 689361 689429 := by
  decide +kernel

private theorem r_689429 : RangeOk getRow 2051521 689429 689498 := by
  decide +kernel

private theorem r_689498 : RangeOk getRow 2051521 689498 689566 := by
  decide +kernel

private theorem r_689566 : RangeOk getRow 2051521 689566 689632 := by
  decide +kernel

private theorem r_689632 : RangeOk getRow 2051521 689632 689699 := by
  decide +kernel

private theorem r_689699 : RangeOk getRow 2051521 689699 689765 := by
  decide +kernel

private theorem r_689765 : RangeOk getRow 2051521 689765 689830 := by
  decide +kernel

private theorem s_687615 : RangeOk getRow 2051521 687545 687615 := r_687545
private theorem s_687684 : RangeOk getRow 2051521 687545 687684 :=
  s_687615.append (by norm_num) r_687615
private theorem s_687751 : RangeOk getRow 2051521 687545 687751 :=
  s_687684.append (by norm_num) r_687684
private theorem s_687818 : RangeOk getRow 2051521 687545 687818 :=
  s_687751.append (by norm_num) r_687751
private theorem s_687887 : RangeOk getRow 2051521 687545 687887 :=
  s_687818.append (by norm_num) r_687818
private theorem s_687955 : RangeOk getRow 2051521 687545 687955 :=
  s_687887.append (by norm_num) r_687887
private theorem s_688021 : RangeOk getRow 2051521 687545 688021 :=
  s_687955.append (by norm_num) r_687955
private theorem s_688086 : RangeOk getRow 2051521 687545 688086 :=
  s_688021.append (by norm_num) r_688021
private theorem s_688153 : RangeOk getRow 2051521 687545 688153 :=
  s_688086.append (by norm_num) r_688086
private theorem s_688220 : RangeOk getRow 2051521 687545 688220 :=
  s_688153.append (by norm_num) r_688153
private theorem s_688288 : RangeOk getRow 2051521 687545 688288 :=
  s_688220.append (by norm_num) r_688220
private theorem s_688356 : RangeOk getRow 2051521 687545 688356 :=
  s_688288.append (by norm_num) r_688288
private theorem s_688424 : RangeOk getRow 2051521 687545 688424 :=
  s_688356.append (by norm_num) r_688356
private theorem s_688493 : RangeOk getRow 2051521 687545 688493 :=
  s_688424.append (by norm_num) r_688424
private theorem s_688561 : RangeOk getRow 2051521 687545 688561 :=
  s_688493.append (by norm_num) r_688493
private theorem s_688628 : RangeOk getRow 2051521 687545 688628 :=
  s_688561.append (by norm_num) r_688561
private theorem s_688695 : RangeOk getRow 2051521 687545 688695 :=
  s_688628.append (by norm_num) r_688628
private theorem s_688760 : RangeOk getRow 2051521 687545 688760 :=
  s_688695.append (by norm_num) r_688695
private theorem s_688825 : RangeOk getRow 2051521 687545 688825 :=
  s_688760.append (by norm_num) r_688760
private theorem s_688891 : RangeOk getRow 2051521 687545 688891 :=
  s_688825.append (by norm_num) r_688825
private theorem s_688959 : RangeOk getRow 2051521 687545 688959 :=
  s_688891.append (by norm_num) r_688891
private theorem s_689026 : RangeOk getRow 2051521 687545 689026 :=
  s_688959.append (by norm_num) r_688959
private theorem s_689093 : RangeOk getRow 2051521 687545 689093 :=
  s_689026.append (by norm_num) r_689026
private theorem s_689159 : RangeOk getRow 2051521 687545 689159 :=
  s_689093.append (by norm_num) r_689093
private theorem s_689225 : RangeOk getRow 2051521 687545 689225 :=
  s_689159.append (by norm_num) r_689159
private theorem s_689292 : RangeOk getRow 2051521 687545 689292 :=
  s_689225.append (by norm_num) r_689225
private theorem s_689361 : RangeOk getRow 2051521 687545 689361 :=
  s_689292.append (by norm_num) r_689292
private theorem s_689429 : RangeOk getRow 2051521 687545 689429 :=
  s_689361.append (by norm_num) r_689361
private theorem s_689498 : RangeOk getRow 2051521 687545 689498 :=
  s_689429.append (by norm_num) r_689429
private theorem s_689566 : RangeOk getRow 2051521 687545 689566 :=
  s_689498.append (by norm_num) r_689498
private theorem s_689632 : RangeOk getRow 2051521 687545 689632 :=
  s_689566.append (by norm_num) r_689566
private theorem s_689699 : RangeOk getRow 2051521 687545 689699 :=
  s_689632.append (by norm_num) r_689632
private theorem s_689765 : RangeOk getRow 2051521 687545 689765 :=
  s_689699.append (by norm_num) r_689699
private theorem s_689830 : RangeOk getRow 2051521 687545 689830 :=
  s_689765.append (by norm_num) r_689765

/-- Rows `[687545, 689830)` are valid. -/
theorem rangeOk_687545_689830 : RangeOk getRow 2051521 687545 689830 := s_689830

end Noperthedron.Solution
