import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[482503, 484945). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_482503 : RangeOk getRow 2051521 482503 482571 := by
  decide +kernel

private theorem r_482571 : RangeOk getRow 2051521 482571 482641 := by
  decide +kernel

private theorem r_482641 : RangeOk getRow 2051521 482641 482712 := by
  decide +kernel

private theorem r_482712 : RangeOk getRow 2051521 482712 482781 := by
  decide +kernel

private theorem r_482781 : RangeOk getRow 2051521 482781 482850 := by
  decide +kernel

private theorem r_482850 : RangeOk getRow 2051521 482850 482918 := by
  decide +kernel

private theorem r_482918 : RangeOk getRow 2051521 482918 482986 := by
  decide +kernel

private theorem r_482986 : RangeOk getRow 2051521 482986 483054 := by
  decide +kernel

private theorem r_483054 : RangeOk getRow 2051521 483054 483123 := by
  decide +kernel

private theorem r_483123 : RangeOk getRow 2051521 483123 483193 := by
  decide +kernel

private theorem r_483193 : RangeOk getRow 2051521 483193 483263 := by
  decide +kernel

private theorem r_483263 : RangeOk getRow 2051521 483263 483332 := by
  decide +kernel

private theorem r_483332 : RangeOk getRow 2051521 483332 483401 := by
  decide +kernel

private theorem r_483401 : RangeOk getRow 2051521 483401 483468 := by
  decide +kernel

private theorem r_483468 : RangeOk getRow 2051521 483468 483535 := by
  decide +kernel

private theorem r_483535 : RangeOk getRow 2051521 483535 483602 := by
  decide +kernel

private theorem r_483602 : RangeOk getRow 2051521 483602 483671 := by
  decide +kernel

private theorem r_483671 : RangeOk getRow 2051521 483671 483740 := by
  decide +kernel

private theorem r_483740 : RangeOk getRow 2051521 483740 483809 := by
  decide +kernel

private theorem r_483809 : RangeOk getRow 2051521 483809 483877 := by
  decide +kernel

private theorem r_483877 : RangeOk getRow 2051521 483877 483944 := by
  decide +kernel

private theorem r_483944 : RangeOk getRow 2051521 483944 484013 := by
  decide +kernel

private theorem r_484013 : RangeOk getRow 2051521 484013 484081 := by
  decide +kernel

private theorem r_484081 : RangeOk getRow 2051521 484081 484150 := by
  decide +kernel

private theorem r_484150 : RangeOk getRow 2051521 484150 484219 := by
  decide +kernel

private theorem r_484219 : RangeOk getRow 2051521 484219 484284 := by
  decide +kernel

private theorem r_484284 : RangeOk getRow 2051521 484284 484348 := by
  decide +kernel

private theorem r_484348 : RangeOk getRow 2051521 484348 484417 := by
  decide +kernel

private theorem r_484417 : RangeOk getRow 2051521 484417 484488 := by
  decide +kernel

private theorem r_484488 : RangeOk getRow 2051521 484488 484556 := by
  decide +kernel

private theorem r_484556 : RangeOk getRow 2051521 484556 484624 := by
  decide +kernel

private theorem r_484624 : RangeOk getRow 2051521 484624 484695 := by
  decide +kernel

private theorem r_484695 : RangeOk getRow 2051521 484695 484762 := by
  decide +kernel

private theorem r_484762 : RangeOk getRow 2051521 484762 484826 := by
  decide +kernel

private theorem r_484826 : RangeOk getRow 2051521 484826 484881 := by
  decide +kernel

private theorem r_484881 : RangeOk getRow 2051521 484881 484945 := by
  decide +kernel

private theorem s_482571 : RangeOk getRow 2051521 482503 482571 := r_482503
private theorem s_482641 : RangeOk getRow 2051521 482503 482641 :=
  s_482571.append (by norm_num) r_482571
private theorem s_482712 : RangeOk getRow 2051521 482503 482712 :=
  s_482641.append (by norm_num) r_482641
private theorem s_482781 : RangeOk getRow 2051521 482503 482781 :=
  s_482712.append (by norm_num) r_482712
private theorem s_482850 : RangeOk getRow 2051521 482503 482850 :=
  s_482781.append (by norm_num) r_482781
private theorem s_482918 : RangeOk getRow 2051521 482503 482918 :=
  s_482850.append (by norm_num) r_482850
private theorem s_482986 : RangeOk getRow 2051521 482503 482986 :=
  s_482918.append (by norm_num) r_482918
private theorem s_483054 : RangeOk getRow 2051521 482503 483054 :=
  s_482986.append (by norm_num) r_482986
private theorem s_483123 : RangeOk getRow 2051521 482503 483123 :=
  s_483054.append (by norm_num) r_483054
private theorem s_483193 : RangeOk getRow 2051521 482503 483193 :=
  s_483123.append (by norm_num) r_483123
private theorem s_483263 : RangeOk getRow 2051521 482503 483263 :=
  s_483193.append (by norm_num) r_483193
private theorem s_483332 : RangeOk getRow 2051521 482503 483332 :=
  s_483263.append (by norm_num) r_483263
private theorem s_483401 : RangeOk getRow 2051521 482503 483401 :=
  s_483332.append (by norm_num) r_483332
private theorem s_483468 : RangeOk getRow 2051521 482503 483468 :=
  s_483401.append (by norm_num) r_483401
private theorem s_483535 : RangeOk getRow 2051521 482503 483535 :=
  s_483468.append (by norm_num) r_483468
private theorem s_483602 : RangeOk getRow 2051521 482503 483602 :=
  s_483535.append (by norm_num) r_483535
private theorem s_483671 : RangeOk getRow 2051521 482503 483671 :=
  s_483602.append (by norm_num) r_483602
private theorem s_483740 : RangeOk getRow 2051521 482503 483740 :=
  s_483671.append (by norm_num) r_483671
private theorem s_483809 : RangeOk getRow 2051521 482503 483809 :=
  s_483740.append (by norm_num) r_483740
private theorem s_483877 : RangeOk getRow 2051521 482503 483877 :=
  s_483809.append (by norm_num) r_483809
private theorem s_483944 : RangeOk getRow 2051521 482503 483944 :=
  s_483877.append (by norm_num) r_483877
private theorem s_484013 : RangeOk getRow 2051521 482503 484013 :=
  s_483944.append (by norm_num) r_483944
private theorem s_484081 : RangeOk getRow 2051521 482503 484081 :=
  s_484013.append (by norm_num) r_484013
private theorem s_484150 : RangeOk getRow 2051521 482503 484150 :=
  s_484081.append (by norm_num) r_484081
private theorem s_484219 : RangeOk getRow 2051521 482503 484219 :=
  s_484150.append (by norm_num) r_484150
private theorem s_484284 : RangeOk getRow 2051521 482503 484284 :=
  s_484219.append (by norm_num) r_484219
private theorem s_484348 : RangeOk getRow 2051521 482503 484348 :=
  s_484284.append (by norm_num) r_484284
private theorem s_484417 : RangeOk getRow 2051521 482503 484417 :=
  s_484348.append (by norm_num) r_484348
private theorem s_484488 : RangeOk getRow 2051521 482503 484488 :=
  s_484417.append (by norm_num) r_484417
private theorem s_484556 : RangeOk getRow 2051521 482503 484556 :=
  s_484488.append (by norm_num) r_484488
private theorem s_484624 : RangeOk getRow 2051521 482503 484624 :=
  s_484556.append (by norm_num) r_484556
private theorem s_484695 : RangeOk getRow 2051521 482503 484695 :=
  s_484624.append (by norm_num) r_484624
private theorem s_484762 : RangeOk getRow 2051521 482503 484762 :=
  s_484695.append (by norm_num) r_484695
private theorem s_484826 : RangeOk getRow 2051521 482503 484826 :=
  s_484762.append (by norm_num) r_484762
private theorem s_484881 : RangeOk getRow 2051521 482503 484881 :=
  s_484826.append (by norm_num) r_484826
private theorem s_484945 : RangeOk getRow 2051521 482503 484945 :=
  s_484881.append (by norm_num) r_484881

/-- Rows `[482503, 484945)` are valid. -/
theorem rangeOk_482503_484945 : RangeOk getRow 2051521 482503 484945 := s_484945

end Noperthedron.Solution
