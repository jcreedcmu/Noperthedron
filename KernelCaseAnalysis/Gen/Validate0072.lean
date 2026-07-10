import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[154537, 157140). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_154537 : RangeOk getRow 2051521 154537 154601 := by
  decide +kernel

private theorem r_154601 : RangeOk getRow 2051521 154601 154666 := by
  decide +kernel

private theorem r_154666 : RangeOk getRow 2051521 154666 154730 := by
  decide +kernel

private theorem r_154730 : RangeOk getRow 2051521 154730 154795 := by
  decide +kernel

private theorem r_154795 : RangeOk getRow 2051521 154795 154860 := by
  decide +kernel

private theorem r_154860 : RangeOk getRow 2051521 154860 154924 := by
  decide +kernel

private theorem r_154924 : RangeOk getRow 2051521 154924 154988 := by
  decide +kernel

private theorem r_154988 : RangeOk getRow 2051521 154988 155052 := by
  decide +kernel

private theorem r_155052 : RangeOk getRow 2051521 155052 155117 := by
  decide +kernel

private theorem r_155117 : RangeOk getRow 2051521 155117 155181 := by
  decide +kernel

private theorem r_155181 : RangeOk getRow 2051521 155181 155246 := by
  decide +kernel

private theorem r_155246 : RangeOk getRow 2051521 155246 155310 := by
  decide +kernel

private theorem r_155310 : RangeOk getRow 2051521 155310 155374 := by
  decide +kernel

private theorem r_155374 : RangeOk getRow 2051521 155374 155444 := by
  decide +kernel

private theorem r_155444 : RangeOk getRow 2051521 155444 155520 := by
  decide +kernel

private theorem r_155520 : RangeOk getRow 2051521 155520 155590 := by
  decide +kernel

private theorem r_155590 : RangeOk getRow 2051521 155590 155657 := by
  decide +kernel

private theorem r_155657 : RangeOk getRow 2051521 155657 155727 := by
  decide +kernel

private theorem r_155727 : RangeOk getRow 2051521 155727 155795 := by
  decide +kernel

private theorem r_155795 : RangeOk getRow 2051521 155795 155859 := by
  decide +kernel

private theorem r_155859 : RangeOk getRow 2051521 155859 155935 := by
  decide +kernel

private theorem r_155935 : RangeOk getRow 2051521 155935 156011 := by
  decide +kernel

private theorem r_156011 : RangeOk getRow 2051521 156011 156086 := by
  decide +kernel

private theorem r_156086 : RangeOk getRow 2051521 156086 156157 := by
  decide +kernel

private theorem r_156157 : RangeOk getRow 2051521 156157 156226 := by
  decide +kernel

private theorem r_156226 : RangeOk getRow 2051521 156226 156290 := by
  decide +kernel

private theorem r_156290 : RangeOk getRow 2051521 156290 156363 := by
  decide +kernel

private theorem r_156363 : RangeOk getRow 2051521 156363 156434 := by
  decide +kernel

private theorem r_156434 : RangeOk getRow 2051521 156434 156509 := by
  decide +kernel

private theorem r_156509 : RangeOk getRow 2051521 156509 156581 := by
  decide +kernel

private theorem r_156581 : RangeOk getRow 2051521 156581 156651 := by
  decide +kernel

private theorem r_156651 : RangeOk getRow 2051521 156651 156716 := by
  decide +kernel

private theorem r_156716 : RangeOk getRow 2051521 156716 156784 := by
  decide +kernel

private theorem r_156784 : RangeOk getRow 2051521 156784 156854 := by
  decide +kernel

private theorem r_156854 : RangeOk getRow 2051521 156854 156929 := by
  decide +kernel

private theorem r_156929 : RangeOk getRow 2051521 156929 157001 := by
  decide +kernel

private theorem r_157001 : RangeOk getRow 2051521 157001 157073 := by
  decide +kernel

private theorem r_157073 : RangeOk getRow 2051521 157073 157140 := by
  decide +kernel

private theorem s_154601 : RangeOk getRow 2051521 154537 154601 := r_154537
private theorem s_154666 : RangeOk getRow 2051521 154537 154666 :=
  s_154601.append (by norm_num) r_154601
private theorem s_154730 : RangeOk getRow 2051521 154537 154730 :=
  s_154666.append (by norm_num) r_154666
private theorem s_154795 : RangeOk getRow 2051521 154537 154795 :=
  s_154730.append (by norm_num) r_154730
private theorem s_154860 : RangeOk getRow 2051521 154537 154860 :=
  s_154795.append (by norm_num) r_154795
private theorem s_154924 : RangeOk getRow 2051521 154537 154924 :=
  s_154860.append (by norm_num) r_154860
private theorem s_154988 : RangeOk getRow 2051521 154537 154988 :=
  s_154924.append (by norm_num) r_154924
private theorem s_155052 : RangeOk getRow 2051521 154537 155052 :=
  s_154988.append (by norm_num) r_154988
private theorem s_155117 : RangeOk getRow 2051521 154537 155117 :=
  s_155052.append (by norm_num) r_155052
private theorem s_155181 : RangeOk getRow 2051521 154537 155181 :=
  s_155117.append (by norm_num) r_155117
private theorem s_155246 : RangeOk getRow 2051521 154537 155246 :=
  s_155181.append (by norm_num) r_155181
private theorem s_155310 : RangeOk getRow 2051521 154537 155310 :=
  s_155246.append (by norm_num) r_155246
private theorem s_155374 : RangeOk getRow 2051521 154537 155374 :=
  s_155310.append (by norm_num) r_155310
private theorem s_155444 : RangeOk getRow 2051521 154537 155444 :=
  s_155374.append (by norm_num) r_155374
private theorem s_155520 : RangeOk getRow 2051521 154537 155520 :=
  s_155444.append (by norm_num) r_155444
private theorem s_155590 : RangeOk getRow 2051521 154537 155590 :=
  s_155520.append (by norm_num) r_155520
private theorem s_155657 : RangeOk getRow 2051521 154537 155657 :=
  s_155590.append (by norm_num) r_155590
private theorem s_155727 : RangeOk getRow 2051521 154537 155727 :=
  s_155657.append (by norm_num) r_155657
private theorem s_155795 : RangeOk getRow 2051521 154537 155795 :=
  s_155727.append (by norm_num) r_155727
private theorem s_155859 : RangeOk getRow 2051521 154537 155859 :=
  s_155795.append (by norm_num) r_155795
private theorem s_155935 : RangeOk getRow 2051521 154537 155935 :=
  s_155859.append (by norm_num) r_155859
private theorem s_156011 : RangeOk getRow 2051521 154537 156011 :=
  s_155935.append (by norm_num) r_155935
private theorem s_156086 : RangeOk getRow 2051521 154537 156086 :=
  s_156011.append (by norm_num) r_156011
private theorem s_156157 : RangeOk getRow 2051521 154537 156157 :=
  s_156086.append (by norm_num) r_156086
private theorem s_156226 : RangeOk getRow 2051521 154537 156226 :=
  s_156157.append (by norm_num) r_156157
private theorem s_156290 : RangeOk getRow 2051521 154537 156290 :=
  s_156226.append (by norm_num) r_156226
private theorem s_156363 : RangeOk getRow 2051521 154537 156363 :=
  s_156290.append (by norm_num) r_156290
private theorem s_156434 : RangeOk getRow 2051521 154537 156434 :=
  s_156363.append (by norm_num) r_156363
private theorem s_156509 : RangeOk getRow 2051521 154537 156509 :=
  s_156434.append (by norm_num) r_156434
private theorem s_156581 : RangeOk getRow 2051521 154537 156581 :=
  s_156509.append (by norm_num) r_156509
private theorem s_156651 : RangeOk getRow 2051521 154537 156651 :=
  s_156581.append (by norm_num) r_156581
private theorem s_156716 : RangeOk getRow 2051521 154537 156716 :=
  s_156651.append (by norm_num) r_156651
private theorem s_156784 : RangeOk getRow 2051521 154537 156784 :=
  s_156716.append (by norm_num) r_156716
private theorem s_156854 : RangeOk getRow 2051521 154537 156854 :=
  s_156784.append (by norm_num) r_156784
private theorem s_156929 : RangeOk getRow 2051521 154537 156929 :=
  s_156854.append (by norm_num) r_156854
private theorem s_157001 : RangeOk getRow 2051521 154537 157001 :=
  s_156929.append (by norm_num) r_156929
private theorem s_157073 : RangeOk getRow 2051521 154537 157073 :=
  s_157001.append (by norm_num) r_157001
private theorem s_157140 : RangeOk getRow 2051521 154537 157140 :=
  s_157073.append (by norm_num) r_157073

/-- Rows `[154537, 157140)` are valid. -/
theorem rangeOk_154537_157140 : RangeOk getRow 2051521 154537 157140 := s_157140

end Noperthedron.Solution
