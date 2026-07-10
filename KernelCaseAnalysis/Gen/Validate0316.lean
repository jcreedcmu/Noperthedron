import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[761666, 763961). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_761666 : RangeOk getRow 2051521 761666 761737 := by
  decide +kernel

private theorem r_761737 : RangeOk getRow 2051521 761737 761807 := by
  decide +kernel

private theorem r_761807 : RangeOk getRow 2051521 761807 761875 := by
  decide +kernel

private theorem r_761875 : RangeOk getRow 2051521 761875 761942 := by
  decide +kernel

private theorem r_761942 : RangeOk getRow 2051521 761942 762009 := by
  decide +kernel

private theorem r_762009 : RangeOk getRow 2051521 762009 762076 := by
  decide +kernel

private theorem r_762076 : RangeOk getRow 2051521 762076 762143 := by
  decide +kernel

private theorem r_762143 : RangeOk getRow 2051521 762143 762209 := by
  decide +kernel

private theorem r_762209 : RangeOk getRow 2051521 762209 762277 := by
  decide +kernel

private theorem r_762277 : RangeOk getRow 2051521 762277 762344 := by
  decide +kernel

private theorem r_762344 : RangeOk getRow 2051521 762344 762412 := by
  decide +kernel

private theorem r_762412 : RangeOk getRow 2051521 762412 762478 := by
  decide +kernel

private theorem r_762478 : RangeOk getRow 2051521 762478 762544 := by
  decide +kernel

private theorem r_762544 : RangeOk getRow 2051521 762544 762611 := by
  decide +kernel

private theorem r_762611 : RangeOk getRow 2051521 762611 762678 := by
  decide +kernel

private theorem r_762678 : RangeOk getRow 2051521 762678 762747 := by
  decide +kernel

private theorem r_762747 : RangeOk getRow 2051521 762747 762813 := by
  decide +kernel

private theorem r_762813 : RangeOk getRow 2051521 762813 762882 := by
  decide +kernel

private theorem r_762882 : RangeOk getRow 2051521 762882 762952 := by
  decide +kernel

private theorem r_762952 : RangeOk getRow 2051521 762952 763019 := by
  decide +kernel

private theorem r_763019 : RangeOk getRow 2051521 763019 763087 := by
  decide +kernel

private theorem r_763087 : RangeOk getRow 2051521 763087 763153 := by
  decide +kernel

private theorem r_763153 : RangeOk getRow 2051521 763153 763220 := by
  decide +kernel

private theorem r_763220 : RangeOk getRow 2051521 763220 763288 := by
  decide +kernel

private theorem r_763288 : RangeOk getRow 2051521 763288 763355 := by
  decide +kernel

private theorem r_763355 : RangeOk getRow 2051521 763355 763422 := by
  decide +kernel

private theorem r_763422 : RangeOk getRow 2051521 763422 763489 := by
  decide +kernel

private theorem r_763489 : RangeOk getRow 2051521 763489 763555 := by
  decide +kernel

private theorem r_763555 : RangeOk getRow 2051521 763555 763623 := by
  decide +kernel

private theorem r_763623 : RangeOk getRow 2051521 763623 763691 := by
  decide +kernel

private theorem r_763691 : RangeOk getRow 2051521 763691 763758 := by
  decide +kernel

private theorem r_763758 : RangeOk getRow 2051521 763758 763827 := by
  decide +kernel

private theorem r_763827 : RangeOk getRow 2051521 763827 763894 := by
  decide +kernel

private theorem r_763894 : RangeOk getRow 2051521 763894 763961 := by
  decide +kernel

private theorem s_761737 : RangeOk getRow 2051521 761666 761737 := r_761666
private theorem s_761807 : RangeOk getRow 2051521 761666 761807 :=
  s_761737.append (by norm_num) r_761737
private theorem s_761875 : RangeOk getRow 2051521 761666 761875 :=
  s_761807.append (by norm_num) r_761807
private theorem s_761942 : RangeOk getRow 2051521 761666 761942 :=
  s_761875.append (by norm_num) r_761875
private theorem s_762009 : RangeOk getRow 2051521 761666 762009 :=
  s_761942.append (by norm_num) r_761942
private theorem s_762076 : RangeOk getRow 2051521 761666 762076 :=
  s_762009.append (by norm_num) r_762009
private theorem s_762143 : RangeOk getRow 2051521 761666 762143 :=
  s_762076.append (by norm_num) r_762076
private theorem s_762209 : RangeOk getRow 2051521 761666 762209 :=
  s_762143.append (by norm_num) r_762143
private theorem s_762277 : RangeOk getRow 2051521 761666 762277 :=
  s_762209.append (by norm_num) r_762209
private theorem s_762344 : RangeOk getRow 2051521 761666 762344 :=
  s_762277.append (by norm_num) r_762277
private theorem s_762412 : RangeOk getRow 2051521 761666 762412 :=
  s_762344.append (by norm_num) r_762344
private theorem s_762478 : RangeOk getRow 2051521 761666 762478 :=
  s_762412.append (by norm_num) r_762412
private theorem s_762544 : RangeOk getRow 2051521 761666 762544 :=
  s_762478.append (by norm_num) r_762478
private theorem s_762611 : RangeOk getRow 2051521 761666 762611 :=
  s_762544.append (by norm_num) r_762544
private theorem s_762678 : RangeOk getRow 2051521 761666 762678 :=
  s_762611.append (by norm_num) r_762611
private theorem s_762747 : RangeOk getRow 2051521 761666 762747 :=
  s_762678.append (by norm_num) r_762678
private theorem s_762813 : RangeOk getRow 2051521 761666 762813 :=
  s_762747.append (by norm_num) r_762747
private theorem s_762882 : RangeOk getRow 2051521 761666 762882 :=
  s_762813.append (by norm_num) r_762813
private theorem s_762952 : RangeOk getRow 2051521 761666 762952 :=
  s_762882.append (by norm_num) r_762882
private theorem s_763019 : RangeOk getRow 2051521 761666 763019 :=
  s_762952.append (by norm_num) r_762952
private theorem s_763087 : RangeOk getRow 2051521 761666 763087 :=
  s_763019.append (by norm_num) r_763019
private theorem s_763153 : RangeOk getRow 2051521 761666 763153 :=
  s_763087.append (by norm_num) r_763087
private theorem s_763220 : RangeOk getRow 2051521 761666 763220 :=
  s_763153.append (by norm_num) r_763153
private theorem s_763288 : RangeOk getRow 2051521 761666 763288 :=
  s_763220.append (by norm_num) r_763220
private theorem s_763355 : RangeOk getRow 2051521 761666 763355 :=
  s_763288.append (by norm_num) r_763288
private theorem s_763422 : RangeOk getRow 2051521 761666 763422 :=
  s_763355.append (by norm_num) r_763355
private theorem s_763489 : RangeOk getRow 2051521 761666 763489 :=
  s_763422.append (by norm_num) r_763422
private theorem s_763555 : RangeOk getRow 2051521 761666 763555 :=
  s_763489.append (by norm_num) r_763489
private theorem s_763623 : RangeOk getRow 2051521 761666 763623 :=
  s_763555.append (by norm_num) r_763555
private theorem s_763691 : RangeOk getRow 2051521 761666 763691 :=
  s_763623.append (by norm_num) r_763623
private theorem s_763758 : RangeOk getRow 2051521 761666 763758 :=
  s_763691.append (by norm_num) r_763691
private theorem s_763827 : RangeOk getRow 2051521 761666 763827 :=
  s_763758.append (by norm_num) r_763758
private theorem s_763894 : RangeOk getRow 2051521 761666 763894 :=
  s_763827.append (by norm_num) r_763827
private theorem s_763961 : RangeOk getRow 2051521 761666 763961 :=
  s_763894.append (by norm_num) r_763894

/-- Rows `[761666, 763961)` are valid. -/
theorem rangeOk_761666_763961 : RangeOk getRow 2051521 761666 763961 := s_763961

end Noperthedron.Solution
