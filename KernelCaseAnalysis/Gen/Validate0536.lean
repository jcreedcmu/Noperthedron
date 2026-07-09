import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1303243, 1306168). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1303243 : RangeOk getRow 2051521 1303243 1303312 := by
  decide +kernel

private theorem r_1303312 : RangeOk getRow 2051521 1303312 1303382 := by
  decide +kernel

private theorem r_1303382 : RangeOk getRow 2051521 1303382 1303453 := by
  decide +kernel

private theorem r_1303453 : RangeOk getRow 2051521 1303453 1303525 := by
  decide +kernel

private theorem r_1303525 : RangeOk getRow 2051521 1303525 1303597 := by
  decide +kernel

private theorem r_1303597 : RangeOk getRow 2051521 1303597 1303671 := by
  decide +kernel

private theorem r_1303671 : RangeOk getRow 2051521 1303671 1303741 := by
  decide +kernel

private theorem r_1303741 : RangeOk getRow 2051521 1303741 1303814 := by
  decide +kernel

private theorem r_1303814 : RangeOk getRow 2051521 1303814 1303885 := by
  decide +kernel

private theorem r_1303885 : RangeOk getRow 2051521 1303885 1303954 := by
  decide +kernel

private theorem r_1303954 : RangeOk getRow 2051521 1303954 1304024 := by
  decide +kernel

private theorem r_1304024 : RangeOk getRow 2051521 1304024 1304095 := by
  decide +kernel

private theorem r_1304095 : RangeOk getRow 2051521 1304095 1304164 := by
  decide +kernel

private theorem r_1304164 : RangeOk getRow 2051521 1304164 1304233 := by
  decide +kernel

private theorem r_1304233 : RangeOk getRow 2051521 1304233 1304302 := by
  decide +kernel

private theorem r_1304302 : RangeOk getRow 2051521 1304302 1304371 := by
  decide +kernel

private theorem r_1304371 : RangeOk getRow 2051521 1304371 1304440 := by
  decide +kernel

private theorem r_1304440 : RangeOk getRow 2051521 1304440 1304509 := by
  decide +kernel

private theorem r_1304509 : RangeOk getRow 2051521 1304509 1304578 := by
  decide +kernel

private theorem r_1304578 : RangeOk getRow 2051521 1304578 1304634 := by
  decide +kernel

private theorem r_1304634 : RangeOk getRow 2051521 1304634 1304703 := by
  decide +kernel

private theorem r_1304703 : RangeOk getRow 2051521 1304703 1304772 := by
  decide +kernel

private theorem r_1304772 : RangeOk getRow 2051521 1304772 1304841 := by
  decide +kernel

private theorem r_1304841 : RangeOk getRow 2051521 1304841 1304910 := by
  decide +kernel

private theorem r_1304910 : RangeOk getRow 2051521 1304910 1304979 := by
  decide +kernel

private theorem r_1304979 : RangeOk getRow 2051521 1304979 1305048 := by
  decide +kernel

private theorem r_1305048 : RangeOk getRow 2051521 1305048 1305117 := by
  decide +kernel

private theorem r_1305117 : RangeOk getRow 2051521 1305117 1305186 := by
  decide +kernel

private theorem r_1305186 : RangeOk getRow 2051521 1305186 1305255 := by
  decide +kernel

private theorem r_1305255 : RangeOk getRow 2051521 1305255 1305324 := by
  decide +kernel

private theorem r_1305324 : RangeOk getRow 2051521 1305324 1305393 := by
  decide +kernel

private theorem r_1305393 : RangeOk getRow 2051521 1305393 1305461 := by
  decide +kernel

private theorem r_1305461 : RangeOk getRow 2051521 1305461 1305529 := by
  decide +kernel

private theorem r_1305529 : RangeOk getRow 2051521 1305529 1305600 := by
  decide +kernel

private theorem r_1305600 : RangeOk getRow 2051521 1305600 1305672 := by
  decide +kernel

private theorem r_1305672 : RangeOk getRow 2051521 1305672 1305744 := by
  decide +kernel

private theorem r_1305744 : RangeOk getRow 2051521 1305744 1305816 := by
  decide +kernel

private theorem r_1305816 : RangeOk getRow 2051521 1305816 1305886 := by
  decide +kernel

private theorem r_1305886 : RangeOk getRow 2051521 1305886 1305957 := by
  decide +kernel

private theorem r_1305957 : RangeOk getRow 2051521 1305957 1306030 := by
  decide +kernel

private theorem r_1306030 : RangeOk getRow 2051521 1306030 1306099 := by
  decide +kernel

private theorem r_1306099 : RangeOk getRow 2051521 1306099 1306168 := by
  decide +kernel

private theorem s_1303312 : RangeOk getRow 2051521 1303243 1303312 := r_1303243
private theorem s_1303382 : RangeOk getRow 2051521 1303243 1303382 :=
  s_1303312.append (by norm_num) r_1303312
private theorem s_1303453 : RangeOk getRow 2051521 1303243 1303453 :=
  s_1303382.append (by norm_num) r_1303382
private theorem s_1303525 : RangeOk getRow 2051521 1303243 1303525 :=
  s_1303453.append (by norm_num) r_1303453
private theorem s_1303597 : RangeOk getRow 2051521 1303243 1303597 :=
  s_1303525.append (by norm_num) r_1303525
private theorem s_1303671 : RangeOk getRow 2051521 1303243 1303671 :=
  s_1303597.append (by norm_num) r_1303597
private theorem s_1303741 : RangeOk getRow 2051521 1303243 1303741 :=
  s_1303671.append (by norm_num) r_1303671
private theorem s_1303814 : RangeOk getRow 2051521 1303243 1303814 :=
  s_1303741.append (by norm_num) r_1303741
private theorem s_1303885 : RangeOk getRow 2051521 1303243 1303885 :=
  s_1303814.append (by norm_num) r_1303814
private theorem s_1303954 : RangeOk getRow 2051521 1303243 1303954 :=
  s_1303885.append (by norm_num) r_1303885
private theorem s_1304024 : RangeOk getRow 2051521 1303243 1304024 :=
  s_1303954.append (by norm_num) r_1303954
private theorem s_1304095 : RangeOk getRow 2051521 1303243 1304095 :=
  s_1304024.append (by norm_num) r_1304024
private theorem s_1304164 : RangeOk getRow 2051521 1303243 1304164 :=
  s_1304095.append (by norm_num) r_1304095
private theorem s_1304233 : RangeOk getRow 2051521 1303243 1304233 :=
  s_1304164.append (by norm_num) r_1304164
private theorem s_1304302 : RangeOk getRow 2051521 1303243 1304302 :=
  s_1304233.append (by norm_num) r_1304233
private theorem s_1304371 : RangeOk getRow 2051521 1303243 1304371 :=
  s_1304302.append (by norm_num) r_1304302
private theorem s_1304440 : RangeOk getRow 2051521 1303243 1304440 :=
  s_1304371.append (by norm_num) r_1304371
private theorem s_1304509 : RangeOk getRow 2051521 1303243 1304509 :=
  s_1304440.append (by norm_num) r_1304440
private theorem s_1304578 : RangeOk getRow 2051521 1303243 1304578 :=
  s_1304509.append (by norm_num) r_1304509
private theorem s_1304634 : RangeOk getRow 2051521 1303243 1304634 :=
  s_1304578.append (by norm_num) r_1304578
private theorem s_1304703 : RangeOk getRow 2051521 1303243 1304703 :=
  s_1304634.append (by norm_num) r_1304634
private theorem s_1304772 : RangeOk getRow 2051521 1303243 1304772 :=
  s_1304703.append (by norm_num) r_1304703
private theorem s_1304841 : RangeOk getRow 2051521 1303243 1304841 :=
  s_1304772.append (by norm_num) r_1304772
private theorem s_1304910 : RangeOk getRow 2051521 1303243 1304910 :=
  s_1304841.append (by norm_num) r_1304841
private theorem s_1304979 : RangeOk getRow 2051521 1303243 1304979 :=
  s_1304910.append (by norm_num) r_1304910
private theorem s_1305048 : RangeOk getRow 2051521 1303243 1305048 :=
  s_1304979.append (by norm_num) r_1304979
private theorem s_1305117 : RangeOk getRow 2051521 1303243 1305117 :=
  s_1305048.append (by norm_num) r_1305048
private theorem s_1305186 : RangeOk getRow 2051521 1303243 1305186 :=
  s_1305117.append (by norm_num) r_1305117
private theorem s_1305255 : RangeOk getRow 2051521 1303243 1305255 :=
  s_1305186.append (by norm_num) r_1305186
private theorem s_1305324 : RangeOk getRow 2051521 1303243 1305324 :=
  s_1305255.append (by norm_num) r_1305255
private theorem s_1305393 : RangeOk getRow 2051521 1303243 1305393 :=
  s_1305324.append (by norm_num) r_1305324
private theorem s_1305461 : RangeOk getRow 2051521 1303243 1305461 :=
  s_1305393.append (by norm_num) r_1305393
private theorem s_1305529 : RangeOk getRow 2051521 1303243 1305529 :=
  s_1305461.append (by norm_num) r_1305461
private theorem s_1305600 : RangeOk getRow 2051521 1303243 1305600 :=
  s_1305529.append (by norm_num) r_1305529
private theorem s_1305672 : RangeOk getRow 2051521 1303243 1305672 :=
  s_1305600.append (by norm_num) r_1305600
private theorem s_1305744 : RangeOk getRow 2051521 1303243 1305744 :=
  s_1305672.append (by norm_num) r_1305672
private theorem s_1305816 : RangeOk getRow 2051521 1303243 1305816 :=
  s_1305744.append (by norm_num) r_1305744
private theorem s_1305886 : RangeOk getRow 2051521 1303243 1305886 :=
  s_1305816.append (by norm_num) r_1305816
private theorem s_1305957 : RangeOk getRow 2051521 1303243 1305957 :=
  s_1305886.append (by norm_num) r_1305886
private theorem s_1306030 : RangeOk getRow 2051521 1303243 1306030 :=
  s_1305957.append (by norm_num) r_1305957
private theorem s_1306099 : RangeOk getRow 2051521 1303243 1306099 :=
  s_1306030.append (by norm_num) r_1306030
private theorem s_1306168 : RangeOk getRow 2051521 1303243 1306168 :=
  s_1306099.append (by norm_num) r_1306099

/-- Rows `[1303243, 1306168)` are valid. -/
theorem rangeOk_1303243_1306168 : RangeOk getRow 2051521 1303243 1306168 := s_1306168

end Noperthedron.Solution
