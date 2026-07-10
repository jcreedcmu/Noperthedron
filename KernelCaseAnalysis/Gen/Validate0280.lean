import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[676000, 678371). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_676000 : RangeOk getRow 2051521 676000 676069 := by
  decide +kernel

private theorem r_676069 : RangeOk getRow 2051521 676069 676138 := by
  decide +kernel

private theorem r_676138 : RangeOk getRow 2051521 676138 676206 := by
  decide +kernel

private theorem r_676206 : RangeOk getRow 2051521 676206 676272 := by
  decide +kernel

private theorem r_676272 : RangeOk getRow 2051521 676272 676339 := by
  decide +kernel

private theorem r_676339 : RangeOk getRow 2051521 676339 676405 := by
  decide +kernel

private theorem r_676405 : RangeOk getRow 2051521 676405 676472 := by
  decide +kernel

private theorem r_676472 : RangeOk getRow 2051521 676472 676540 := by
  decide +kernel

private theorem r_676540 : RangeOk getRow 2051521 676540 676608 := by
  decide +kernel

private theorem r_676608 : RangeOk getRow 2051521 676608 676677 := by
  decide +kernel

private theorem r_676677 : RangeOk getRow 2051521 676677 676746 := by
  decide +kernel

private theorem r_676746 : RangeOk getRow 2051521 676746 676813 := by
  decide +kernel

private theorem r_676813 : RangeOk getRow 2051521 676813 676879 := by
  decide +kernel

private theorem r_676879 : RangeOk getRow 2051521 676879 676947 := by
  decide +kernel

private theorem r_676947 : RangeOk getRow 2051521 676947 677015 := by
  decide +kernel

private theorem r_677015 : RangeOk getRow 2051521 677015 677084 := by
  decide +kernel

private theorem r_677084 : RangeOk getRow 2051521 677084 677152 := by
  decide +kernel

private theorem r_677152 : RangeOk getRow 2051521 677152 677220 := by
  decide +kernel

private theorem r_677220 : RangeOk getRow 2051521 677220 677287 := by
  decide +kernel

private theorem r_677287 : RangeOk getRow 2051521 677287 677355 := by
  decide +kernel

private theorem r_677355 : RangeOk getRow 2051521 677355 677421 := by
  decide +kernel

private theorem r_677421 : RangeOk getRow 2051521 677421 677487 := by
  decide +kernel

private theorem r_677487 : RangeOk getRow 2051521 677487 677554 := by
  decide +kernel

private theorem r_677554 : RangeOk getRow 2051521 677554 677623 := by
  decide +kernel

private theorem r_677623 : RangeOk getRow 2051521 677623 677692 := by
  decide +kernel

private theorem r_677692 : RangeOk getRow 2051521 677692 677760 := by
  decide +kernel

private theorem r_677760 : RangeOk getRow 2051521 677760 677829 := by
  decide +kernel

private theorem r_677829 : RangeOk getRow 2051521 677829 677896 := by
  decide +kernel

private theorem r_677896 : RangeOk getRow 2051521 677896 677964 := by
  decide +kernel

private theorem r_677964 : RangeOk getRow 2051521 677964 678030 := by
  decide +kernel

private theorem r_678030 : RangeOk getRow 2051521 678030 678097 := by
  decide +kernel

private theorem r_678097 : RangeOk getRow 2051521 678097 678166 := by
  decide +kernel

private theorem r_678166 : RangeOk getRow 2051521 678166 678235 := by
  decide +kernel

private theorem r_678235 : RangeOk getRow 2051521 678235 678303 := by
  decide +kernel

private theorem r_678303 : RangeOk getRow 2051521 678303 678371 := by
  decide +kernel

private theorem s_676069 : RangeOk getRow 2051521 676000 676069 := r_676000
private theorem s_676138 : RangeOk getRow 2051521 676000 676138 :=
  s_676069.append (by norm_num) r_676069
private theorem s_676206 : RangeOk getRow 2051521 676000 676206 :=
  s_676138.append (by norm_num) r_676138
private theorem s_676272 : RangeOk getRow 2051521 676000 676272 :=
  s_676206.append (by norm_num) r_676206
private theorem s_676339 : RangeOk getRow 2051521 676000 676339 :=
  s_676272.append (by norm_num) r_676272
private theorem s_676405 : RangeOk getRow 2051521 676000 676405 :=
  s_676339.append (by norm_num) r_676339
private theorem s_676472 : RangeOk getRow 2051521 676000 676472 :=
  s_676405.append (by norm_num) r_676405
private theorem s_676540 : RangeOk getRow 2051521 676000 676540 :=
  s_676472.append (by norm_num) r_676472
private theorem s_676608 : RangeOk getRow 2051521 676000 676608 :=
  s_676540.append (by norm_num) r_676540
private theorem s_676677 : RangeOk getRow 2051521 676000 676677 :=
  s_676608.append (by norm_num) r_676608
private theorem s_676746 : RangeOk getRow 2051521 676000 676746 :=
  s_676677.append (by norm_num) r_676677
private theorem s_676813 : RangeOk getRow 2051521 676000 676813 :=
  s_676746.append (by norm_num) r_676746
private theorem s_676879 : RangeOk getRow 2051521 676000 676879 :=
  s_676813.append (by norm_num) r_676813
private theorem s_676947 : RangeOk getRow 2051521 676000 676947 :=
  s_676879.append (by norm_num) r_676879
private theorem s_677015 : RangeOk getRow 2051521 676000 677015 :=
  s_676947.append (by norm_num) r_676947
private theorem s_677084 : RangeOk getRow 2051521 676000 677084 :=
  s_677015.append (by norm_num) r_677015
private theorem s_677152 : RangeOk getRow 2051521 676000 677152 :=
  s_677084.append (by norm_num) r_677084
private theorem s_677220 : RangeOk getRow 2051521 676000 677220 :=
  s_677152.append (by norm_num) r_677152
private theorem s_677287 : RangeOk getRow 2051521 676000 677287 :=
  s_677220.append (by norm_num) r_677220
private theorem s_677355 : RangeOk getRow 2051521 676000 677355 :=
  s_677287.append (by norm_num) r_677287
private theorem s_677421 : RangeOk getRow 2051521 676000 677421 :=
  s_677355.append (by norm_num) r_677355
private theorem s_677487 : RangeOk getRow 2051521 676000 677487 :=
  s_677421.append (by norm_num) r_677421
private theorem s_677554 : RangeOk getRow 2051521 676000 677554 :=
  s_677487.append (by norm_num) r_677487
private theorem s_677623 : RangeOk getRow 2051521 676000 677623 :=
  s_677554.append (by norm_num) r_677554
private theorem s_677692 : RangeOk getRow 2051521 676000 677692 :=
  s_677623.append (by norm_num) r_677623
private theorem s_677760 : RangeOk getRow 2051521 676000 677760 :=
  s_677692.append (by norm_num) r_677692
private theorem s_677829 : RangeOk getRow 2051521 676000 677829 :=
  s_677760.append (by norm_num) r_677760
private theorem s_677896 : RangeOk getRow 2051521 676000 677896 :=
  s_677829.append (by norm_num) r_677829
private theorem s_677964 : RangeOk getRow 2051521 676000 677964 :=
  s_677896.append (by norm_num) r_677896
private theorem s_678030 : RangeOk getRow 2051521 676000 678030 :=
  s_677964.append (by norm_num) r_677964
private theorem s_678097 : RangeOk getRow 2051521 676000 678097 :=
  s_678030.append (by norm_num) r_678030
private theorem s_678166 : RangeOk getRow 2051521 676000 678166 :=
  s_678097.append (by norm_num) r_678097
private theorem s_678235 : RangeOk getRow 2051521 676000 678235 :=
  s_678166.append (by norm_num) r_678166
private theorem s_678303 : RangeOk getRow 2051521 676000 678303 :=
  s_678235.append (by norm_num) r_678235
private theorem s_678371 : RangeOk getRow 2051521 676000 678371 :=
  s_678303.append (by norm_num) r_678303

/-- Rows `[676000, 678371)` are valid. -/
theorem rangeOk_676000_678371 : RangeOk getRow 2051521 676000 678371 := s_678371

end Noperthedron.Solution
