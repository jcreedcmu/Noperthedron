import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[878693, 881312). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_878693 : RangeOk getRow 2051521 878693 878761 := by
  decide +kernel

private theorem r_878761 : RangeOk getRow 2051521 878761 878828 := by
  decide +kernel

private theorem r_878828 : RangeOk getRow 2051521 878828 878896 := by
  decide +kernel

private theorem r_878896 : RangeOk getRow 2051521 878896 878967 := by
  decide +kernel

private theorem r_878967 : RangeOk getRow 2051521 878967 879034 := by
  decide +kernel

private theorem r_879034 : RangeOk getRow 2051521 879034 879102 := by
  decide +kernel

private theorem r_879102 : RangeOk getRow 2051521 879102 879169 := by
  decide +kernel

private theorem r_879169 : RangeOk getRow 2051521 879169 879236 := by
  decide +kernel

private theorem r_879236 : RangeOk getRow 2051521 879236 879306 := by
  decide +kernel

private theorem r_879306 : RangeOk getRow 2051521 879306 879378 := by
  decide +kernel

private theorem r_879378 : RangeOk getRow 2051521 879378 879446 := by
  decide +kernel

private theorem r_879446 : RangeOk getRow 2051521 879446 879513 := by
  decide +kernel

private theorem r_879513 : RangeOk getRow 2051521 879513 879579 := by
  decide +kernel

private theorem r_879579 : RangeOk getRow 2051521 879579 879649 := by
  decide +kernel

private theorem r_879649 : RangeOk getRow 2051521 879649 879716 := by
  decide +kernel

private theorem r_879716 : RangeOk getRow 2051521 879716 879784 := by
  decide +kernel

private theorem r_879784 : RangeOk getRow 2051521 879784 879851 := by
  decide +kernel

private theorem r_879851 : RangeOk getRow 2051521 879851 879920 := by
  decide +kernel

private theorem r_879920 : RangeOk getRow 2051521 879920 879992 := by
  decide +kernel

private theorem r_879992 : RangeOk getRow 2051521 879992 880062 := by
  decide +kernel

private theorem r_880062 : RangeOk getRow 2051521 880062 880135 := by
  decide +kernel

private theorem r_880135 : RangeOk getRow 2051521 880135 880203 := by
  decide +kernel

private theorem r_880203 : RangeOk getRow 2051521 880203 880274 := by
  decide +kernel

private theorem r_880274 : RangeOk getRow 2051521 880274 880346 := by
  decide +kernel

private theorem r_880346 : RangeOk getRow 2051521 880346 880416 := by
  decide +kernel

private theorem r_880416 : RangeOk getRow 2051521 880416 880486 := by
  decide +kernel

private theorem r_880486 : RangeOk getRow 2051521 880486 880558 := by
  decide +kernel

private theorem r_880558 : RangeOk getRow 2051521 880558 880628 := by
  decide +kernel

private theorem r_880628 : RangeOk getRow 2051521 880628 880697 := by
  decide +kernel

private theorem r_880697 : RangeOk getRow 2051521 880697 880765 := by
  decide +kernel

private theorem r_880765 : RangeOk getRow 2051521 880765 880834 := by
  decide +kernel

private theorem r_880834 : RangeOk getRow 2051521 880834 880905 := by
  decide +kernel

private theorem r_880905 : RangeOk getRow 2051521 880905 880974 := by
  decide +kernel

private theorem r_880974 : RangeOk getRow 2051521 880974 881040 := by
  decide +kernel

private theorem r_881040 : RangeOk getRow 2051521 881040 881107 := by
  decide +kernel

private theorem r_881107 : RangeOk getRow 2051521 881107 881176 := by
  decide +kernel

private theorem r_881176 : RangeOk getRow 2051521 881176 881244 := by
  decide +kernel

private theorem r_881244 : RangeOk getRow 2051521 881244 881312 := by
  decide +kernel

private theorem s_878761 : RangeOk getRow 2051521 878693 878761 := r_878693
private theorem s_878828 : RangeOk getRow 2051521 878693 878828 :=
  s_878761.append (by norm_num) r_878761
private theorem s_878896 : RangeOk getRow 2051521 878693 878896 :=
  s_878828.append (by norm_num) r_878828
private theorem s_878967 : RangeOk getRow 2051521 878693 878967 :=
  s_878896.append (by norm_num) r_878896
private theorem s_879034 : RangeOk getRow 2051521 878693 879034 :=
  s_878967.append (by norm_num) r_878967
private theorem s_879102 : RangeOk getRow 2051521 878693 879102 :=
  s_879034.append (by norm_num) r_879034
private theorem s_879169 : RangeOk getRow 2051521 878693 879169 :=
  s_879102.append (by norm_num) r_879102
private theorem s_879236 : RangeOk getRow 2051521 878693 879236 :=
  s_879169.append (by norm_num) r_879169
private theorem s_879306 : RangeOk getRow 2051521 878693 879306 :=
  s_879236.append (by norm_num) r_879236
private theorem s_879378 : RangeOk getRow 2051521 878693 879378 :=
  s_879306.append (by norm_num) r_879306
private theorem s_879446 : RangeOk getRow 2051521 878693 879446 :=
  s_879378.append (by norm_num) r_879378
private theorem s_879513 : RangeOk getRow 2051521 878693 879513 :=
  s_879446.append (by norm_num) r_879446
private theorem s_879579 : RangeOk getRow 2051521 878693 879579 :=
  s_879513.append (by norm_num) r_879513
private theorem s_879649 : RangeOk getRow 2051521 878693 879649 :=
  s_879579.append (by norm_num) r_879579
private theorem s_879716 : RangeOk getRow 2051521 878693 879716 :=
  s_879649.append (by norm_num) r_879649
private theorem s_879784 : RangeOk getRow 2051521 878693 879784 :=
  s_879716.append (by norm_num) r_879716
private theorem s_879851 : RangeOk getRow 2051521 878693 879851 :=
  s_879784.append (by norm_num) r_879784
private theorem s_879920 : RangeOk getRow 2051521 878693 879920 :=
  s_879851.append (by norm_num) r_879851
private theorem s_879992 : RangeOk getRow 2051521 878693 879992 :=
  s_879920.append (by norm_num) r_879920
private theorem s_880062 : RangeOk getRow 2051521 878693 880062 :=
  s_879992.append (by norm_num) r_879992
private theorem s_880135 : RangeOk getRow 2051521 878693 880135 :=
  s_880062.append (by norm_num) r_880062
private theorem s_880203 : RangeOk getRow 2051521 878693 880203 :=
  s_880135.append (by norm_num) r_880135
private theorem s_880274 : RangeOk getRow 2051521 878693 880274 :=
  s_880203.append (by norm_num) r_880203
private theorem s_880346 : RangeOk getRow 2051521 878693 880346 :=
  s_880274.append (by norm_num) r_880274
private theorem s_880416 : RangeOk getRow 2051521 878693 880416 :=
  s_880346.append (by norm_num) r_880346
private theorem s_880486 : RangeOk getRow 2051521 878693 880486 :=
  s_880416.append (by norm_num) r_880416
private theorem s_880558 : RangeOk getRow 2051521 878693 880558 :=
  s_880486.append (by norm_num) r_880486
private theorem s_880628 : RangeOk getRow 2051521 878693 880628 :=
  s_880558.append (by norm_num) r_880558
private theorem s_880697 : RangeOk getRow 2051521 878693 880697 :=
  s_880628.append (by norm_num) r_880628
private theorem s_880765 : RangeOk getRow 2051521 878693 880765 :=
  s_880697.append (by norm_num) r_880697
private theorem s_880834 : RangeOk getRow 2051521 878693 880834 :=
  s_880765.append (by norm_num) r_880765
private theorem s_880905 : RangeOk getRow 2051521 878693 880905 :=
  s_880834.append (by norm_num) r_880834
private theorem s_880974 : RangeOk getRow 2051521 878693 880974 :=
  s_880905.append (by norm_num) r_880905
private theorem s_881040 : RangeOk getRow 2051521 878693 881040 :=
  s_880974.append (by norm_num) r_880974
private theorem s_881107 : RangeOk getRow 2051521 878693 881107 :=
  s_881040.append (by norm_num) r_881040
private theorem s_881176 : RangeOk getRow 2051521 878693 881176 :=
  s_881107.append (by norm_num) r_881107
private theorem s_881244 : RangeOk getRow 2051521 878693 881244 :=
  s_881176.append (by norm_num) r_881176
private theorem s_881312 : RangeOk getRow 2051521 878693 881312 :=
  s_881244.append (by norm_num) r_881244

/-- Rows `[878693, 881312)` are valid. -/
theorem rangeOk_878693_881312 : RangeOk getRow 2051521 878693 881312 := s_881312

end Noperthedron.Solution
