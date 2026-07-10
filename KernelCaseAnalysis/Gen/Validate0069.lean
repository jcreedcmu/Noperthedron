import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[149359, 151084). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_149359 : RangeOk getRow 2051521 149359 149423 := by
  decide +kernel

private theorem r_149423 : RangeOk getRow 2051521 149423 149483 := by
  decide +kernel

private theorem r_149483 : RangeOk getRow 2051521 149483 149547 := by
  decide +kernel

private theorem r_149547 : RangeOk getRow 2051521 149547 149611 := by
  decide +kernel

private theorem r_149611 : RangeOk getRow 2051521 149611 149675 := by
  decide +kernel

private theorem r_149675 : RangeOk getRow 2051521 149675 149739 := by
  decide +kernel

private theorem r_149739 : RangeOk getRow 2051521 149739 149803 := by
  decide +kernel

private theorem r_149803 : RangeOk getRow 2051521 149803 149867 := by
  decide +kernel

private theorem r_149867 : RangeOk getRow 2051521 149867 149932 := by
  decide +kernel

private theorem r_149932 : RangeOk getRow 2051521 149932 149996 := by
  decide +kernel

private theorem r_149996 : RangeOk getRow 2051521 149996 150060 := by
  decide +kernel

private theorem r_150060 : RangeOk getRow 2051521 150060 150124 := by
  decide +kernel

private theorem r_150124 : RangeOk getRow 2051521 150124 150188 := by
  decide +kernel

private theorem r_150188 : RangeOk getRow 2051521 150188 150252 := by
  decide +kernel

private theorem r_150252 : RangeOk getRow 2051521 150252 150316 := by
  decide +kernel

private theorem r_150316 : RangeOk getRow 2051521 150316 150380 := by
  decide +kernel

private theorem r_150380 : RangeOk getRow 2051521 150380 150444 := by
  decide +kernel

private theorem r_150444 : RangeOk getRow 2051521 150444 150508 := by
  decide +kernel

private theorem r_150508 : RangeOk getRow 2051521 150508 150572 := by
  decide +kernel

private theorem r_150572 : RangeOk getRow 2051521 150572 150636 := by
  decide +kernel

private theorem r_150636 : RangeOk getRow 2051521 150636 150700 := by
  decide +kernel

private theorem r_150700 : RangeOk getRow 2051521 150700 150764 := by
  decide +kernel

private theorem r_150764 : RangeOk getRow 2051521 150764 150828 := by
  decide +kernel

private theorem r_150828 : RangeOk getRow 2051521 150828 150892 := by
  decide +kernel

private theorem r_150892 : RangeOk getRow 2051521 150892 150956 := by
  decide +kernel

private theorem r_150956 : RangeOk getRow 2051521 150956 151020 := by
  decide +kernel

private theorem r_151020 : RangeOk getRow 2051521 151020 151084 := by
  decide +kernel

private theorem s_149423 : RangeOk getRow 2051521 149359 149423 := r_149359
private theorem s_149483 : RangeOk getRow 2051521 149359 149483 :=
  s_149423.append (by norm_num) r_149423
private theorem s_149547 : RangeOk getRow 2051521 149359 149547 :=
  s_149483.append (by norm_num) r_149483
private theorem s_149611 : RangeOk getRow 2051521 149359 149611 :=
  s_149547.append (by norm_num) r_149547
private theorem s_149675 : RangeOk getRow 2051521 149359 149675 :=
  s_149611.append (by norm_num) r_149611
private theorem s_149739 : RangeOk getRow 2051521 149359 149739 :=
  s_149675.append (by norm_num) r_149675
private theorem s_149803 : RangeOk getRow 2051521 149359 149803 :=
  s_149739.append (by norm_num) r_149739
private theorem s_149867 : RangeOk getRow 2051521 149359 149867 :=
  s_149803.append (by norm_num) r_149803
private theorem s_149932 : RangeOk getRow 2051521 149359 149932 :=
  s_149867.append (by norm_num) r_149867
private theorem s_149996 : RangeOk getRow 2051521 149359 149996 :=
  s_149932.append (by norm_num) r_149932
private theorem s_150060 : RangeOk getRow 2051521 149359 150060 :=
  s_149996.append (by norm_num) r_149996
private theorem s_150124 : RangeOk getRow 2051521 149359 150124 :=
  s_150060.append (by norm_num) r_150060
private theorem s_150188 : RangeOk getRow 2051521 149359 150188 :=
  s_150124.append (by norm_num) r_150124
private theorem s_150252 : RangeOk getRow 2051521 149359 150252 :=
  s_150188.append (by norm_num) r_150188
private theorem s_150316 : RangeOk getRow 2051521 149359 150316 :=
  s_150252.append (by norm_num) r_150252
private theorem s_150380 : RangeOk getRow 2051521 149359 150380 :=
  s_150316.append (by norm_num) r_150316
private theorem s_150444 : RangeOk getRow 2051521 149359 150444 :=
  s_150380.append (by norm_num) r_150380
private theorem s_150508 : RangeOk getRow 2051521 149359 150508 :=
  s_150444.append (by norm_num) r_150444
private theorem s_150572 : RangeOk getRow 2051521 149359 150572 :=
  s_150508.append (by norm_num) r_150508
private theorem s_150636 : RangeOk getRow 2051521 149359 150636 :=
  s_150572.append (by norm_num) r_150572
private theorem s_150700 : RangeOk getRow 2051521 149359 150700 :=
  s_150636.append (by norm_num) r_150636
private theorem s_150764 : RangeOk getRow 2051521 149359 150764 :=
  s_150700.append (by norm_num) r_150700
private theorem s_150828 : RangeOk getRow 2051521 149359 150828 :=
  s_150764.append (by norm_num) r_150764
private theorem s_150892 : RangeOk getRow 2051521 149359 150892 :=
  s_150828.append (by norm_num) r_150828
private theorem s_150956 : RangeOk getRow 2051521 149359 150956 :=
  s_150892.append (by norm_num) r_150892
private theorem s_151020 : RangeOk getRow 2051521 149359 151020 :=
  s_150956.append (by norm_num) r_150956
private theorem s_151084 : RangeOk getRow 2051521 149359 151084 :=
  s_151020.append (by norm_num) r_151020

/-- Rows `[149359, 151084)` are valid. -/
theorem rangeOk_149359_151084 : RangeOk getRow 2051521 149359 151084 := s_151084

end Noperthedron.Solution
