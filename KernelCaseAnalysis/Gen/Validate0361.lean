import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[869144, 871513). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_869144 : RangeOk getRow 2051521 869144 869210 := by
  decide +kernel

private theorem r_869210 : RangeOk getRow 2051521 869210 869276 := by
  decide +kernel

private theorem r_869276 : RangeOk getRow 2051521 869276 869343 := by
  decide +kernel

private theorem r_869343 : RangeOk getRow 2051521 869343 869409 := by
  decide +kernel

private theorem r_869409 : RangeOk getRow 2051521 869409 869479 := by
  decide +kernel

private theorem r_869479 : RangeOk getRow 2051521 869479 869548 := by
  decide +kernel

private theorem r_869548 : RangeOk getRow 2051521 869548 869615 := by
  decide +kernel

private theorem r_869615 : RangeOk getRow 2051521 869615 869684 := by
  decide +kernel

private theorem r_869684 : RangeOk getRow 2051521 869684 869751 := by
  decide +kernel

private theorem r_869751 : RangeOk getRow 2051521 869751 869822 := by
  decide +kernel

private theorem r_869822 : RangeOk getRow 2051521 869822 869891 := by
  decide +kernel

private theorem r_869891 : RangeOk getRow 2051521 869891 869960 := by
  decide +kernel

private theorem r_869960 : RangeOk getRow 2051521 869960 870027 := by
  decide +kernel

private theorem r_870027 : RangeOk getRow 2051521 870027 870093 := by
  decide +kernel

private theorem r_870093 : RangeOk getRow 2051521 870093 870160 := by
  decide +kernel

private theorem r_870160 : RangeOk getRow 2051521 870160 870226 := by
  decide +kernel

private theorem r_870226 : RangeOk getRow 2051521 870226 870294 := by
  decide +kernel

private theorem r_870294 : RangeOk getRow 2051521 870294 870360 := by
  decide +kernel

private theorem r_870360 : RangeOk getRow 2051521 870360 870428 := by
  decide +kernel

private theorem r_870428 : RangeOk getRow 2051521 870428 870497 := by
  decide +kernel

private theorem r_870497 : RangeOk getRow 2051521 870497 870566 := by
  decide +kernel

private theorem r_870566 : RangeOk getRow 2051521 870566 870634 := by
  decide +kernel

private theorem r_870634 : RangeOk getRow 2051521 870634 870699 := by
  decide +kernel

private theorem r_870699 : RangeOk getRow 2051521 870699 870766 := by
  decide +kernel

private theorem r_870766 : RangeOk getRow 2051521 870766 870835 := by
  decide +kernel

private theorem r_870835 : RangeOk getRow 2051521 870835 870903 := by
  decide +kernel

private theorem r_870903 : RangeOk getRow 2051521 870903 870971 := by
  decide +kernel

private theorem r_870971 : RangeOk getRow 2051521 870971 871037 := by
  decide +kernel

private theorem r_871037 : RangeOk getRow 2051521 871037 871106 := by
  decide +kernel

private theorem r_871106 : RangeOk getRow 2051521 871106 871176 := by
  decide +kernel

private theorem r_871176 : RangeOk getRow 2051521 871176 871243 := by
  decide +kernel

private theorem r_871243 : RangeOk getRow 2051521 871243 871310 := by
  decide +kernel

private theorem r_871310 : RangeOk getRow 2051521 871310 871377 := by
  decide +kernel

private theorem r_871377 : RangeOk getRow 2051521 871377 871445 := by
  decide +kernel

private theorem r_871445 : RangeOk getRow 2051521 871445 871513 := by
  decide +kernel

private theorem s_869210 : RangeOk getRow 2051521 869144 869210 := r_869144
private theorem s_869276 : RangeOk getRow 2051521 869144 869276 :=
  s_869210.append (by norm_num) r_869210
private theorem s_869343 : RangeOk getRow 2051521 869144 869343 :=
  s_869276.append (by norm_num) r_869276
private theorem s_869409 : RangeOk getRow 2051521 869144 869409 :=
  s_869343.append (by norm_num) r_869343
private theorem s_869479 : RangeOk getRow 2051521 869144 869479 :=
  s_869409.append (by norm_num) r_869409
private theorem s_869548 : RangeOk getRow 2051521 869144 869548 :=
  s_869479.append (by norm_num) r_869479
private theorem s_869615 : RangeOk getRow 2051521 869144 869615 :=
  s_869548.append (by norm_num) r_869548
private theorem s_869684 : RangeOk getRow 2051521 869144 869684 :=
  s_869615.append (by norm_num) r_869615
private theorem s_869751 : RangeOk getRow 2051521 869144 869751 :=
  s_869684.append (by norm_num) r_869684
private theorem s_869822 : RangeOk getRow 2051521 869144 869822 :=
  s_869751.append (by norm_num) r_869751
private theorem s_869891 : RangeOk getRow 2051521 869144 869891 :=
  s_869822.append (by norm_num) r_869822
private theorem s_869960 : RangeOk getRow 2051521 869144 869960 :=
  s_869891.append (by norm_num) r_869891
private theorem s_870027 : RangeOk getRow 2051521 869144 870027 :=
  s_869960.append (by norm_num) r_869960
private theorem s_870093 : RangeOk getRow 2051521 869144 870093 :=
  s_870027.append (by norm_num) r_870027
private theorem s_870160 : RangeOk getRow 2051521 869144 870160 :=
  s_870093.append (by norm_num) r_870093
private theorem s_870226 : RangeOk getRow 2051521 869144 870226 :=
  s_870160.append (by norm_num) r_870160
private theorem s_870294 : RangeOk getRow 2051521 869144 870294 :=
  s_870226.append (by norm_num) r_870226
private theorem s_870360 : RangeOk getRow 2051521 869144 870360 :=
  s_870294.append (by norm_num) r_870294
private theorem s_870428 : RangeOk getRow 2051521 869144 870428 :=
  s_870360.append (by norm_num) r_870360
private theorem s_870497 : RangeOk getRow 2051521 869144 870497 :=
  s_870428.append (by norm_num) r_870428
private theorem s_870566 : RangeOk getRow 2051521 869144 870566 :=
  s_870497.append (by norm_num) r_870497
private theorem s_870634 : RangeOk getRow 2051521 869144 870634 :=
  s_870566.append (by norm_num) r_870566
private theorem s_870699 : RangeOk getRow 2051521 869144 870699 :=
  s_870634.append (by norm_num) r_870634
private theorem s_870766 : RangeOk getRow 2051521 869144 870766 :=
  s_870699.append (by norm_num) r_870699
private theorem s_870835 : RangeOk getRow 2051521 869144 870835 :=
  s_870766.append (by norm_num) r_870766
private theorem s_870903 : RangeOk getRow 2051521 869144 870903 :=
  s_870835.append (by norm_num) r_870835
private theorem s_870971 : RangeOk getRow 2051521 869144 870971 :=
  s_870903.append (by norm_num) r_870903
private theorem s_871037 : RangeOk getRow 2051521 869144 871037 :=
  s_870971.append (by norm_num) r_870971
private theorem s_871106 : RangeOk getRow 2051521 869144 871106 :=
  s_871037.append (by norm_num) r_871037
private theorem s_871176 : RangeOk getRow 2051521 869144 871176 :=
  s_871106.append (by norm_num) r_871106
private theorem s_871243 : RangeOk getRow 2051521 869144 871243 :=
  s_871176.append (by norm_num) r_871176
private theorem s_871310 : RangeOk getRow 2051521 869144 871310 :=
  s_871243.append (by norm_num) r_871243
private theorem s_871377 : RangeOk getRow 2051521 869144 871377 :=
  s_871310.append (by norm_num) r_871310
private theorem s_871445 : RangeOk getRow 2051521 869144 871445 :=
  s_871377.append (by norm_num) r_871377
private theorem s_871513 : RangeOk getRow 2051521 869144 871513 :=
  s_871445.append (by norm_num) r_871445

/-- Rows `[869144, 871513)` are valid. -/
theorem rangeOk_869144_871513 : RangeOk getRow 2051521 869144 871513 := s_871513

end Noperthedron.Solution
