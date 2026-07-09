import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[616175, 618712). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_616175 : RangeOk getRow 2051521 616175 616242 := by
  decide +kernel

private theorem r_616242 : RangeOk getRow 2051521 616242 616310 := by
  decide +kernel

private theorem r_616310 : RangeOk getRow 2051521 616310 616376 := by
  decide +kernel

private theorem r_616376 : RangeOk getRow 2051521 616376 616440 := by
  decide +kernel

private theorem r_616440 : RangeOk getRow 2051521 616440 616507 := by
  decide +kernel

private theorem r_616507 : RangeOk getRow 2051521 616507 616576 := by
  decide +kernel

private theorem r_616576 : RangeOk getRow 2051521 616576 616643 := by
  decide +kernel

private theorem r_616643 : RangeOk getRow 2051521 616643 616707 := by
  decide +kernel

private theorem r_616707 : RangeOk getRow 2051521 616707 616772 := by
  decide +kernel

private theorem r_616772 : RangeOk getRow 2051521 616772 616840 := by
  decide +kernel

private theorem r_616840 : RangeOk getRow 2051521 616840 616907 := by
  decide +kernel

private theorem r_616907 : RangeOk getRow 2051521 616907 616973 := by
  decide +kernel

private theorem r_616973 : RangeOk getRow 2051521 616973 617037 := by
  decide +kernel

private theorem r_617037 : RangeOk getRow 2051521 617037 617102 := by
  decide +kernel

private theorem r_617102 : RangeOk getRow 2051521 617102 617171 := by
  decide +kernel

private theorem r_617171 : RangeOk getRow 2051521 617171 617237 := by
  decide +kernel

private theorem r_617237 : RangeOk getRow 2051521 617237 617306 := by
  decide +kernel

private theorem r_617306 : RangeOk getRow 2051521 617306 617381 := by
  decide +kernel

private theorem r_617381 : RangeOk getRow 2051521 617381 617456 := by
  decide +kernel

private theorem r_617456 : RangeOk getRow 2051521 617456 617529 := by
  decide +kernel

private theorem r_617529 : RangeOk getRow 2051521 617529 617599 := by
  decide +kernel

private theorem r_617599 : RangeOk getRow 2051521 617599 617670 := by
  decide +kernel

private theorem r_617670 : RangeOk getRow 2051521 617670 617740 := by
  decide +kernel

private theorem r_617740 : RangeOk getRow 2051521 617740 617809 := by
  decide +kernel

private theorem r_617809 : RangeOk getRow 2051521 617809 617879 := by
  decide +kernel

private theorem r_617879 : RangeOk getRow 2051521 617879 617949 := by
  decide +kernel

private theorem r_617949 : RangeOk getRow 2051521 617949 618017 := by
  decide +kernel

private theorem r_618017 : RangeOk getRow 2051521 618017 618088 := by
  decide +kernel

private theorem r_618088 : RangeOk getRow 2051521 618088 618159 := by
  decide +kernel

private theorem r_618159 : RangeOk getRow 2051521 618159 618230 := by
  decide +kernel

private theorem r_618230 : RangeOk getRow 2051521 618230 618299 := by
  decide +kernel

private theorem r_618299 : RangeOk getRow 2051521 618299 618365 := by
  decide +kernel

private theorem r_618365 : RangeOk getRow 2051521 618365 618432 := by
  decide +kernel

private theorem r_618432 : RangeOk getRow 2051521 618432 618499 := by
  decide +kernel

private theorem r_618499 : RangeOk getRow 2051521 618499 618564 := by
  decide +kernel

private theorem r_618564 : RangeOk getRow 2051521 618564 618637 := by
  decide +kernel

private theorem r_618637 : RangeOk getRow 2051521 618637 618712 := by
  decide +kernel

private theorem s_616242 : RangeOk getRow 2051521 616175 616242 := r_616175
private theorem s_616310 : RangeOk getRow 2051521 616175 616310 :=
  s_616242.append (by norm_num) r_616242
private theorem s_616376 : RangeOk getRow 2051521 616175 616376 :=
  s_616310.append (by norm_num) r_616310
private theorem s_616440 : RangeOk getRow 2051521 616175 616440 :=
  s_616376.append (by norm_num) r_616376
private theorem s_616507 : RangeOk getRow 2051521 616175 616507 :=
  s_616440.append (by norm_num) r_616440
private theorem s_616576 : RangeOk getRow 2051521 616175 616576 :=
  s_616507.append (by norm_num) r_616507
private theorem s_616643 : RangeOk getRow 2051521 616175 616643 :=
  s_616576.append (by norm_num) r_616576
private theorem s_616707 : RangeOk getRow 2051521 616175 616707 :=
  s_616643.append (by norm_num) r_616643
private theorem s_616772 : RangeOk getRow 2051521 616175 616772 :=
  s_616707.append (by norm_num) r_616707
private theorem s_616840 : RangeOk getRow 2051521 616175 616840 :=
  s_616772.append (by norm_num) r_616772
private theorem s_616907 : RangeOk getRow 2051521 616175 616907 :=
  s_616840.append (by norm_num) r_616840
private theorem s_616973 : RangeOk getRow 2051521 616175 616973 :=
  s_616907.append (by norm_num) r_616907
private theorem s_617037 : RangeOk getRow 2051521 616175 617037 :=
  s_616973.append (by norm_num) r_616973
private theorem s_617102 : RangeOk getRow 2051521 616175 617102 :=
  s_617037.append (by norm_num) r_617037
private theorem s_617171 : RangeOk getRow 2051521 616175 617171 :=
  s_617102.append (by norm_num) r_617102
private theorem s_617237 : RangeOk getRow 2051521 616175 617237 :=
  s_617171.append (by norm_num) r_617171
private theorem s_617306 : RangeOk getRow 2051521 616175 617306 :=
  s_617237.append (by norm_num) r_617237
private theorem s_617381 : RangeOk getRow 2051521 616175 617381 :=
  s_617306.append (by norm_num) r_617306
private theorem s_617456 : RangeOk getRow 2051521 616175 617456 :=
  s_617381.append (by norm_num) r_617381
private theorem s_617529 : RangeOk getRow 2051521 616175 617529 :=
  s_617456.append (by norm_num) r_617456
private theorem s_617599 : RangeOk getRow 2051521 616175 617599 :=
  s_617529.append (by norm_num) r_617529
private theorem s_617670 : RangeOk getRow 2051521 616175 617670 :=
  s_617599.append (by norm_num) r_617599
private theorem s_617740 : RangeOk getRow 2051521 616175 617740 :=
  s_617670.append (by norm_num) r_617670
private theorem s_617809 : RangeOk getRow 2051521 616175 617809 :=
  s_617740.append (by norm_num) r_617740
private theorem s_617879 : RangeOk getRow 2051521 616175 617879 :=
  s_617809.append (by norm_num) r_617809
private theorem s_617949 : RangeOk getRow 2051521 616175 617949 :=
  s_617879.append (by norm_num) r_617879
private theorem s_618017 : RangeOk getRow 2051521 616175 618017 :=
  s_617949.append (by norm_num) r_617949
private theorem s_618088 : RangeOk getRow 2051521 616175 618088 :=
  s_618017.append (by norm_num) r_618017
private theorem s_618159 : RangeOk getRow 2051521 616175 618159 :=
  s_618088.append (by norm_num) r_618088
private theorem s_618230 : RangeOk getRow 2051521 616175 618230 :=
  s_618159.append (by norm_num) r_618159
private theorem s_618299 : RangeOk getRow 2051521 616175 618299 :=
  s_618230.append (by norm_num) r_618230
private theorem s_618365 : RangeOk getRow 2051521 616175 618365 :=
  s_618299.append (by norm_num) r_618299
private theorem s_618432 : RangeOk getRow 2051521 616175 618432 :=
  s_618365.append (by norm_num) r_618365
private theorem s_618499 : RangeOk getRow 2051521 616175 618499 :=
  s_618432.append (by norm_num) r_618432
private theorem s_618564 : RangeOk getRow 2051521 616175 618564 :=
  s_618499.append (by norm_num) r_618499
private theorem s_618637 : RangeOk getRow 2051521 616175 618637 :=
  s_618564.append (by norm_num) r_618564
private theorem s_618712 : RangeOk getRow 2051521 616175 618712 :=
  s_618637.append (by norm_num) r_618637

/-- Rows `[616175, 618712)` are valid. -/
theorem rangeOk_616175_618712 : RangeOk getRow 2051521 616175 618712 := s_618712

end Noperthedron.Solution
