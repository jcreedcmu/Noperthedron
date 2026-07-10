import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[557493, 559704). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_557493 : RangeOk getRow 2051521 557493 557559 := by
  decide +kernel

private theorem r_557559 : RangeOk getRow 2051521 557559 557626 := by
  decide +kernel

private theorem r_557626 : RangeOk getRow 2051521 557626 557694 := by
  decide +kernel

private theorem r_557694 : RangeOk getRow 2051521 557694 557762 := by
  decide +kernel

private theorem r_557762 : RangeOk getRow 2051521 557762 557831 := by
  decide +kernel

private theorem r_557831 : RangeOk getRow 2051521 557831 557897 := by
  decide +kernel

private theorem r_557897 : RangeOk getRow 2051521 557897 557961 := by
  decide +kernel

private theorem r_557961 : RangeOk getRow 2051521 557961 558029 := by
  decide +kernel

private theorem r_558029 : RangeOk getRow 2051521 558029 558098 := by
  decide +kernel

private theorem r_558098 : RangeOk getRow 2051521 558098 558165 := by
  decide +kernel

private theorem r_558165 : RangeOk getRow 2051521 558165 558231 := by
  decide +kernel

private theorem r_558231 : RangeOk getRow 2051521 558231 558295 := by
  decide +kernel

private theorem r_558295 : RangeOk getRow 2051521 558295 558362 := by
  decide +kernel

private theorem r_558362 : RangeOk getRow 2051521 558362 558430 := by
  decide +kernel

private theorem r_558430 : RangeOk getRow 2051521 558430 558499 := by
  decide +kernel

private theorem r_558499 : RangeOk getRow 2051521 558499 558566 := by
  decide +kernel

private theorem r_558566 : RangeOk getRow 2051521 558566 558631 := by
  decide +kernel

private theorem r_558631 : RangeOk getRow 2051521 558631 558696 := by
  decide +kernel

private theorem r_558696 : RangeOk getRow 2051521 558696 558764 := by
  decide +kernel

private theorem r_558764 : RangeOk getRow 2051521 558764 558831 := by
  decide +kernel

private theorem r_558831 : RangeOk getRow 2051521 558831 558897 := by
  decide +kernel

private theorem r_558897 : RangeOk getRow 2051521 558897 558961 := by
  decide +kernel

private theorem r_558961 : RangeOk getRow 2051521 558961 559029 := by
  decide +kernel

private theorem r_559029 : RangeOk getRow 2051521 559029 559095 := by
  decide +kernel

private theorem r_559095 : RangeOk getRow 2051521 559095 559162 := by
  decide +kernel

private theorem r_559162 : RangeOk getRow 2051521 559162 559231 := by
  decide +kernel

private theorem r_559231 : RangeOk getRow 2051521 559231 559299 := by
  decide +kernel

private theorem r_559299 : RangeOk getRow 2051521 559299 559366 := by
  decide +kernel

private theorem r_559366 : RangeOk getRow 2051521 559366 559433 := by
  decide +kernel

private theorem r_559433 : RangeOk getRow 2051521 559433 559499 := by
  decide +kernel

private theorem r_559499 : RangeOk getRow 2051521 559499 559566 := by
  decide +kernel

private theorem r_559566 : RangeOk getRow 2051521 559566 559635 := by
  decide +kernel

private theorem r_559635 : RangeOk getRow 2051521 559635 559704 := by
  decide +kernel

private theorem s_557559 : RangeOk getRow 2051521 557493 557559 := r_557493
private theorem s_557626 : RangeOk getRow 2051521 557493 557626 :=
  s_557559.append (by norm_num) r_557559
private theorem s_557694 : RangeOk getRow 2051521 557493 557694 :=
  s_557626.append (by norm_num) r_557626
private theorem s_557762 : RangeOk getRow 2051521 557493 557762 :=
  s_557694.append (by norm_num) r_557694
private theorem s_557831 : RangeOk getRow 2051521 557493 557831 :=
  s_557762.append (by norm_num) r_557762
private theorem s_557897 : RangeOk getRow 2051521 557493 557897 :=
  s_557831.append (by norm_num) r_557831
private theorem s_557961 : RangeOk getRow 2051521 557493 557961 :=
  s_557897.append (by norm_num) r_557897
private theorem s_558029 : RangeOk getRow 2051521 557493 558029 :=
  s_557961.append (by norm_num) r_557961
private theorem s_558098 : RangeOk getRow 2051521 557493 558098 :=
  s_558029.append (by norm_num) r_558029
private theorem s_558165 : RangeOk getRow 2051521 557493 558165 :=
  s_558098.append (by norm_num) r_558098
private theorem s_558231 : RangeOk getRow 2051521 557493 558231 :=
  s_558165.append (by norm_num) r_558165
private theorem s_558295 : RangeOk getRow 2051521 557493 558295 :=
  s_558231.append (by norm_num) r_558231
private theorem s_558362 : RangeOk getRow 2051521 557493 558362 :=
  s_558295.append (by norm_num) r_558295
private theorem s_558430 : RangeOk getRow 2051521 557493 558430 :=
  s_558362.append (by norm_num) r_558362
private theorem s_558499 : RangeOk getRow 2051521 557493 558499 :=
  s_558430.append (by norm_num) r_558430
private theorem s_558566 : RangeOk getRow 2051521 557493 558566 :=
  s_558499.append (by norm_num) r_558499
private theorem s_558631 : RangeOk getRow 2051521 557493 558631 :=
  s_558566.append (by norm_num) r_558566
private theorem s_558696 : RangeOk getRow 2051521 557493 558696 :=
  s_558631.append (by norm_num) r_558631
private theorem s_558764 : RangeOk getRow 2051521 557493 558764 :=
  s_558696.append (by norm_num) r_558696
private theorem s_558831 : RangeOk getRow 2051521 557493 558831 :=
  s_558764.append (by norm_num) r_558764
private theorem s_558897 : RangeOk getRow 2051521 557493 558897 :=
  s_558831.append (by norm_num) r_558831
private theorem s_558961 : RangeOk getRow 2051521 557493 558961 :=
  s_558897.append (by norm_num) r_558897
private theorem s_559029 : RangeOk getRow 2051521 557493 559029 :=
  s_558961.append (by norm_num) r_558961
private theorem s_559095 : RangeOk getRow 2051521 557493 559095 :=
  s_559029.append (by norm_num) r_559029
private theorem s_559162 : RangeOk getRow 2051521 557493 559162 :=
  s_559095.append (by norm_num) r_559095
private theorem s_559231 : RangeOk getRow 2051521 557493 559231 :=
  s_559162.append (by norm_num) r_559162
private theorem s_559299 : RangeOk getRow 2051521 557493 559299 :=
  s_559231.append (by norm_num) r_559231
private theorem s_559366 : RangeOk getRow 2051521 557493 559366 :=
  s_559299.append (by norm_num) r_559299
private theorem s_559433 : RangeOk getRow 2051521 557493 559433 :=
  s_559366.append (by norm_num) r_559366
private theorem s_559499 : RangeOk getRow 2051521 557493 559499 :=
  s_559433.append (by norm_num) r_559433
private theorem s_559566 : RangeOk getRow 2051521 557493 559566 :=
  s_559499.append (by norm_num) r_559499
private theorem s_559635 : RangeOk getRow 2051521 557493 559635 :=
  s_559566.append (by norm_num) r_559566
private theorem s_559704 : RangeOk getRow 2051521 557493 559704 :=
  s_559635.append (by norm_num) r_559635

/-- Rows `[557493, 559704)` are valid. -/
theorem rangeOk_557493_559704 : RangeOk getRow 2051521 557493 559704 := s_559704

end Noperthedron.Solution
