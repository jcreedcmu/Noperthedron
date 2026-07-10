import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1663127, 1666008). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1663127 : RangeOk getRow 2051521 1663127 1663172 := by
  decide +kernel

private theorem r_1663172 : RangeOk getRow 2051521 1663172 1663221 := by
  decide +kernel

private theorem r_1663221 : RangeOk getRow 2051521 1663221 1663250 := by
  decide +kernel

private theorem r_1663250 : RangeOk getRow 2051521 1663250 1663288 := by
  decide +kernel

private theorem r_1663288 : RangeOk getRow 2051521 1663288 1663319 := by
  decide +kernel

private theorem r_1663319 : RangeOk getRow 2051521 1663319 1663362 := by
  decide +kernel

private theorem r_1663362 : RangeOk getRow 2051521 1663362 1663426 := by
  decide +kernel

private theorem r_1663426 : RangeOk getRow 2051521 1663426 1663490 := by
  decide +kernel

private theorem r_1663490 : RangeOk getRow 2051521 1663490 1663554 := by
  decide +kernel

private theorem r_1663554 : RangeOk getRow 2051521 1663554 1663625 := by
  decide +kernel

private theorem r_1663625 : RangeOk getRow 2051521 1663625 1663696 := by
  decide +kernel

private theorem r_1663696 : RangeOk getRow 2051521 1663696 1663767 := by
  decide +kernel

private theorem r_1663767 : RangeOk getRow 2051521 1663767 1663831 := by
  decide +kernel

private theorem r_1663831 : RangeOk getRow 2051521 1663831 1663881 := by
  decide +kernel

private theorem r_1663881 : RangeOk getRow 2051521 1663881 1663953 := by
  decide +kernel

private theorem r_1663953 : RangeOk getRow 2051521 1663953 1664023 := by
  decide +kernel

private theorem r_1664023 : RangeOk getRow 2051521 1664023 1664095 := by
  decide +kernel

private theorem r_1664095 : RangeOk getRow 2051521 1664095 1664164 := by
  decide +kernel

private theorem r_1664164 : RangeOk getRow 2051521 1664164 1664225 := by
  decide +kernel

private theorem r_1664225 : RangeOk getRow 2051521 1664225 1664289 := by
  decide +kernel

private theorem r_1664289 : RangeOk getRow 2051521 1664289 1664360 := by
  decide +kernel

private theorem r_1664360 : RangeOk getRow 2051521 1664360 1664433 := by
  decide +kernel

private theorem r_1664433 : RangeOk getRow 2051521 1664433 1664504 := by
  decide +kernel

private theorem r_1664504 : RangeOk getRow 2051521 1664504 1664574 := by
  decide +kernel

private theorem r_1664574 : RangeOk getRow 2051521 1664574 1664645 := by
  decide +kernel

private theorem r_1664645 : RangeOk getRow 2051521 1664645 1664716 := by
  decide +kernel

private theorem r_1664716 : RangeOk getRow 2051521 1664716 1664785 := by
  decide +kernel

private theorem r_1664785 : RangeOk getRow 2051521 1664785 1664821 := by
  decide +kernel

private theorem r_1664821 : RangeOk getRow 2051521 1664821 1664893 := by
  decide +kernel

private theorem r_1664893 : RangeOk getRow 2051521 1664893 1664957 := by
  decide +kernel

private theorem r_1664957 : RangeOk getRow 2051521 1664957 1665028 := by
  decide +kernel

private theorem r_1665028 : RangeOk getRow 2051521 1665028 1665098 := by
  decide +kernel

private theorem r_1665098 : RangeOk getRow 2051521 1665098 1665170 := by
  decide +kernel

private theorem r_1665170 : RangeOk getRow 2051521 1665170 1665228 := by
  decide +kernel

private theorem r_1665228 : RangeOk getRow 2051521 1665228 1665300 := by
  decide +kernel

private theorem r_1665300 : RangeOk getRow 2051521 1665300 1665372 := by
  decide +kernel

private theorem r_1665372 : RangeOk getRow 2051521 1665372 1665429 := by
  decide +kernel

private theorem r_1665429 : RangeOk getRow 2051521 1665429 1665502 := by
  decide +kernel

private theorem r_1665502 : RangeOk getRow 2051521 1665502 1665567 := by
  decide +kernel

private theorem r_1665567 : RangeOk getRow 2051521 1665567 1665636 := by
  decide +kernel

private theorem r_1665636 : RangeOk getRow 2051521 1665636 1665673 := by
  decide +kernel

private theorem r_1665673 : RangeOk getRow 2051521 1665673 1665734 := by
  decide +kernel

private theorem r_1665734 : RangeOk getRow 2051521 1665734 1665792 := by
  decide +kernel

private theorem r_1665792 : RangeOk getRow 2051521 1665792 1665848 := by
  decide +kernel

private theorem r_1665848 : RangeOk getRow 2051521 1665848 1665898 := by
  decide +kernel

private theorem r_1665898 : RangeOk getRow 2051521 1665898 1665950 := by
  decide +kernel

private theorem r_1665950 : RangeOk getRow 2051521 1665950 1666008 := by
  decide +kernel

private theorem s_1663172 : RangeOk getRow 2051521 1663127 1663172 := r_1663127
private theorem s_1663221 : RangeOk getRow 2051521 1663127 1663221 :=
  s_1663172.append (by norm_num) r_1663172
private theorem s_1663250 : RangeOk getRow 2051521 1663127 1663250 :=
  s_1663221.append (by norm_num) r_1663221
private theorem s_1663288 : RangeOk getRow 2051521 1663127 1663288 :=
  s_1663250.append (by norm_num) r_1663250
private theorem s_1663319 : RangeOk getRow 2051521 1663127 1663319 :=
  s_1663288.append (by norm_num) r_1663288
private theorem s_1663362 : RangeOk getRow 2051521 1663127 1663362 :=
  s_1663319.append (by norm_num) r_1663319
private theorem s_1663426 : RangeOk getRow 2051521 1663127 1663426 :=
  s_1663362.append (by norm_num) r_1663362
private theorem s_1663490 : RangeOk getRow 2051521 1663127 1663490 :=
  s_1663426.append (by norm_num) r_1663426
private theorem s_1663554 : RangeOk getRow 2051521 1663127 1663554 :=
  s_1663490.append (by norm_num) r_1663490
private theorem s_1663625 : RangeOk getRow 2051521 1663127 1663625 :=
  s_1663554.append (by norm_num) r_1663554
private theorem s_1663696 : RangeOk getRow 2051521 1663127 1663696 :=
  s_1663625.append (by norm_num) r_1663625
private theorem s_1663767 : RangeOk getRow 2051521 1663127 1663767 :=
  s_1663696.append (by norm_num) r_1663696
private theorem s_1663831 : RangeOk getRow 2051521 1663127 1663831 :=
  s_1663767.append (by norm_num) r_1663767
private theorem s_1663881 : RangeOk getRow 2051521 1663127 1663881 :=
  s_1663831.append (by norm_num) r_1663831
private theorem s_1663953 : RangeOk getRow 2051521 1663127 1663953 :=
  s_1663881.append (by norm_num) r_1663881
private theorem s_1664023 : RangeOk getRow 2051521 1663127 1664023 :=
  s_1663953.append (by norm_num) r_1663953
private theorem s_1664095 : RangeOk getRow 2051521 1663127 1664095 :=
  s_1664023.append (by norm_num) r_1664023
private theorem s_1664164 : RangeOk getRow 2051521 1663127 1664164 :=
  s_1664095.append (by norm_num) r_1664095
private theorem s_1664225 : RangeOk getRow 2051521 1663127 1664225 :=
  s_1664164.append (by norm_num) r_1664164
private theorem s_1664289 : RangeOk getRow 2051521 1663127 1664289 :=
  s_1664225.append (by norm_num) r_1664225
private theorem s_1664360 : RangeOk getRow 2051521 1663127 1664360 :=
  s_1664289.append (by norm_num) r_1664289
private theorem s_1664433 : RangeOk getRow 2051521 1663127 1664433 :=
  s_1664360.append (by norm_num) r_1664360
private theorem s_1664504 : RangeOk getRow 2051521 1663127 1664504 :=
  s_1664433.append (by norm_num) r_1664433
private theorem s_1664574 : RangeOk getRow 2051521 1663127 1664574 :=
  s_1664504.append (by norm_num) r_1664504
private theorem s_1664645 : RangeOk getRow 2051521 1663127 1664645 :=
  s_1664574.append (by norm_num) r_1664574
private theorem s_1664716 : RangeOk getRow 2051521 1663127 1664716 :=
  s_1664645.append (by norm_num) r_1664645
private theorem s_1664785 : RangeOk getRow 2051521 1663127 1664785 :=
  s_1664716.append (by norm_num) r_1664716
private theorem s_1664821 : RangeOk getRow 2051521 1663127 1664821 :=
  s_1664785.append (by norm_num) r_1664785
private theorem s_1664893 : RangeOk getRow 2051521 1663127 1664893 :=
  s_1664821.append (by norm_num) r_1664821
private theorem s_1664957 : RangeOk getRow 2051521 1663127 1664957 :=
  s_1664893.append (by norm_num) r_1664893
private theorem s_1665028 : RangeOk getRow 2051521 1663127 1665028 :=
  s_1664957.append (by norm_num) r_1664957
private theorem s_1665098 : RangeOk getRow 2051521 1663127 1665098 :=
  s_1665028.append (by norm_num) r_1665028
private theorem s_1665170 : RangeOk getRow 2051521 1663127 1665170 :=
  s_1665098.append (by norm_num) r_1665098
private theorem s_1665228 : RangeOk getRow 2051521 1663127 1665228 :=
  s_1665170.append (by norm_num) r_1665170
private theorem s_1665300 : RangeOk getRow 2051521 1663127 1665300 :=
  s_1665228.append (by norm_num) r_1665228
private theorem s_1665372 : RangeOk getRow 2051521 1663127 1665372 :=
  s_1665300.append (by norm_num) r_1665300
private theorem s_1665429 : RangeOk getRow 2051521 1663127 1665429 :=
  s_1665372.append (by norm_num) r_1665372
private theorem s_1665502 : RangeOk getRow 2051521 1663127 1665502 :=
  s_1665429.append (by norm_num) r_1665429
private theorem s_1665567 : RangeOk getRow 2051521 1663127 1665567 :=
  s_1665502.append (by norm_num) r_1665502
private theorem s_1665636 : RangeOk getRow 2051521 1663127 1665636 :=
  s_1665567.append (by norm_num) r_1665567
private theorem s_1665673 : RangeOk getRow 2051521 1663127 1665673 :=
  s_1665636.append (by norm_num) r_1665636
private theorem s_1665734 : RangeOk getRow 2051521 1663127 1665734 :=
  s_1665673.append (by norm_num) r_1665673
private theorem s_1665792 : RangeOk getRow 2051521 1663127 1665792 :=
  s_1665734.append (by norm_num) r_1665734
private theorem s_1665848 : RangeOk getRow 2051521 1663127 1665848 :=
  s_1665792.append (by norm_num) r_1665792
private theorem s_1665898 : RangeOk getRow 2051521 1663127 1665898 :=
  s_1665848.append (by norm_num) r_1665848
private theorem s_1665950 : RangeOk getRow 2051521 1663127 1665950 :=
  s_1665898.append (by norm_num) r_1665898
private theorem s_1666008 : RangeOk getRow 2051521 1663127 1666008 :=
  s_1665950.append (by norm_num) r_1665950

/-- Rows `[1663127, 1666008)` are valid. -/
theorem rangeOk_1663127_1666008 : RangeOk getRow 2051521 1663127 1666008 := s_1666008

end Noperthedron.Solution
