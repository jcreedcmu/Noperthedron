import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[794572, 796865). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_794572 : RangeOk getRow 2051521 794572 794641 := by
  decide +kernel

private theorem r_794641 : RangeOk getRow 2051521 794641 794710 := by
  decide +kernel

private theorem r_794710 : RangeOk getRow 2051521 794710 794777 := by
  decide +kernel

private theorem r_794777 : RangeOk getRow 2051521 794777 794843 := by
  decide +kernel

private theorem r_794843 : RangeOk getRow 2051521 794843 794908 := by
  decide +kernel

private theorem r_794908 : RangeOk getRow 2051521 794908 794975 := by
  decide +kernel

private theorem r_794975 : RangeOk getRow 2051521 794975 795043 := by
  decide +kernel

private theorem r_795043 : RangeOk getRow 2051521 795043 795111 := by
  decide +kernel

private theorem r_795111 : RangeOk getRow 2051521 795111 795179 := by
  decide +kernel

private theorem r_795179 : RangeOk getRow 2051521 795179 795247 := by
  decide +kernel

private theorem r_795247 : RangeOk getRow 2051521 795247 795314 := by
  decide +kernel

private theorem r_795314 : RangeOk getRow 2051521 795314 795383 := by
  decide +kernel

private theorem r_795383 : RangeOk getRow 2051521 795383 795453 := by
  decide +kernel

private theorem r_795453 : RangeOk getRow 2051521 795453 795521 := by
  decide +kernel

private theorem r_795521 : RangeOk getRow 2051521 795521 795587 := by
  decide +kernel

private theorem r_795587 : RangeOk getRow 2051521 795587 795652 := by
  decide +kernel

private theorem r_795652 : RangeOk getRow 2051521 795652 795722 := by
  decide +kernel

private theorem r_795722 : RangeOk getRow 2051521 795722 795791 := by
  decide +kernel

private theorem r_795791 : RangeOk getRow 2051521 795791 795860 := by
  decide +kernel

private theorem r_795860 : RangeOk getRow 2051521 795860 795926 := by
  decide +kernel

private theorem r_795926 : RangeOk getRow 2051521 795926 795995 := by
  decide +kernel

private theorem r_795995 : RangeOk getRow 2051521 795995 796061 := by
  decide +kernel

private theorem r_796061 : RangeOk getRow 2051521 796061 796126 := by
  decide +kernel

private theorem r_796126 : RangeOk getRow 2051521 796126 796193 := by
  decide +kernel

private theorem r_796193 : RangeOk getRow 2051521 796193 796258 := by
  decide +kernel

private theorem r_796258 : RangeOk getRow 2051521 796258 796327 := by
  decide +kernel

private theorem r_796327 : RangeOk getRow 2051521 796327 796395 := by
  decide +kernel

private theorem r_796395 : RangeOk getRow 2051521 796395 796464 := by
  decide +kernel

private theorem r_796464 : RangeOk getRow 2051521 796464 796531 := by
  decide +kernel

private theorem r_796531 : RangeOk getRow 2051521 796531 796596 := by
  decide +kernel

private theorem r_796596 : RangeOk getRow 2051521 796596 796664 := by
  decide +kernel

private theorem r_796664 : RangeOk getRow 2051521 796664 796732 := by
  decide +kernel

private theorem r_796732 : RangeOk getRow 2051521 796732 796799 := by
  decide +kernel

private theorem r_796799 : RangeOk getRow 2051521 796799 796865 := by
  decide +kernel

private theorem s_794641 : RangeOk getRow 2051521 794572 794641 := r_794572
private theorem s_794710 : RangeOk getRow 2051521 794572 794710 :=
  s_794641.append (by norm_num) r_794641
private theorem s_794777 : RangeOk getRow 2051521 794572 794777 :=
  s_794710.append (by norm_num) r_794710
private theorem s_794843 : RangeOk getRow 2051521 794572 794843 :=
  s_794777.append (by norm_num) r_794777
private theorem s_794908 : RangeOk getRow 2051521 794572 794908 :=
  s_794843.append (by norm_num) r_794843
private theorem s_794975 : RangeOk getRow 2051521 794572 794975 :=
  s_794908.append (by norm_num) r_794908
private theorem s_795043 : RangeOk getRow 2051521 794572 795043 :=
  s_794975.append (by norm_num) r_794975
private theorem s_795111 : RangeOk getRow 2051521 794572 795111 :=
  s_795043.append (by norm_num) r_795043
private theorem s_795179 : RangeOk getRow 2051521 794572 795179 :=
  s_795111.append (by norm_num) r_795111
private theorem s_795247 : RangeOk getRow 2051521 794572 795247 :=
  s_795179.append (by norm_num) r_795179
private theorem s_795314 : RangeOk getRow 2051521 794572 795314 :=
  s_795247.append (by norm_num) r_795247
private theorem s_795383 : RangeOk getRow 2051521 794572 795383 :=
  s_795314.append (by norm_num) r_795314
private theorem s_795453 : RangeOk getRow 2051521 794572 795453 :=
  s_795383.append (by norm_num) r_795383
private theorem s_795521 : RangeOk getRow 2051521 794572 795521 :=
  s_795453.append (by norm_num) r_795453
private theorem s_795587 : RangeOk getRow 2051521 794572 795587 :=
  s_795521.append (by norm_num) r_795521
private theorem s_795652 : RangeOk getRow 2051521 794572 795652 :=
  s_795587.append (by norm_num) r_795587
private theorem s_795722 : RangeOk getRow 2051521 794572 795722 :=
  s_795652.append (by norm_num) r_795652
private theorem s_795791 : RangeOk getRow 2051521 794572 795791 :=
  s_795722.append (by norm_num) r_795722
private theorem s_795860 : RangeOk getRow 2051521 794572 795860 :=
  s_795791.append (by norm_num) r_795791
private theorem s_795926 : RangeOk getRow 2051521 794572 795926 :=
  s_795860.append (by norm_num) r_795860
private theorem s_795995 : RangeOk getRow 2051521 794572 795995 :=
  s_795926.append (by norm_num) r_795926
private theorem s_796061 : RangeOk getRow 2051521 794572 796061 :=
  s_795995.append (by norm_num) r_795995
private theorem s_796126 : RangeOk getRow 2051521 794572 796126 :=
  s_796061.append (by norm_num) r_796061
private theorem s_796193 : RangeOk getRow 2051521 794572 796193 :=
  s_796126.append (by norm_num) r_796126
private theorem s_796258 : RangeOk getRow 2051521 794572 796258 :=
  s_796193.append (by norm_num) r_796193
private theorem s_796327 : RangeOk getRow 2051521 794572 796327 :=
  s_796258.append (by norm_num) r_796258
private theorem s_796395 : RangeOk getRow 2051521 794572 796395 :=
  s_796327.append (by norm_num) r_796327
private theorem s_796464 : RangeOk getRow 2051521 794572 796464 :=
  s_796395.append (by norm_num) r_796395
private theorem s_796531 : RangeOk getRow 2051521 794572 796531 :=
  s_796464.append (by norm_num) r_796464
private theorem s_796596 : RangeOk getRow 2051521 794572 796596 :=
  s_796531.append (by norm_num) r_796531
private theorem s_796664 : RangeOk getRow 2051521 794572 796664 :=
  s_796596.append (by norm_num) r_796596
private theorem s_796732 : RangeOk getRow 2051521 794572 796732 :=
  s_796664.append (by norm_num) r_796664
private theorem s_796799 : RangeOk getRow 2051521 794572 796799 :=
  s_796732.append (by norm_num) r_796732
private theorem s_796865 : RangeOk getRow 2051521 794572 796865 :=
  s_796799.append (by norm_num) r_796799

/-- Rows `[794572, 796865)` are valid. -/
theorem rangeOk_794572_796865 : RangeOk getRow 2051521 794572 796865 := s_796865

end Noperthedron.Solution
