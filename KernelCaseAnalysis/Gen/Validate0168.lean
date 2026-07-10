import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[402035, 404646). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_402035 : RangeOk getRow 2051521 402035 402102 := by
  decide +kernel

private theorem r_402102 : RangeOk getRow 2051521 402102 402170 := by
  decide +kernel

private theorem r_402170 : RangeOk getRow 2051521 402170 402238 := by
  decide +kernel

private theorem r_402238 : RangeOk getRow 2051521 402238 402307 := by
  decide +kernel

private theorem r_402307 : RangeOk getRow 2051521 402307 402377 := by
  decide +kernel

private theorem r_402377 : RangeOk getRow 2051521 402377 402446 := by
  decide +kernel

private theorem r_402446 : RangeOk getRow 2051521 402446 402514 := by
  decide +kernel

private theorem r_402514 : RangeOk getRow 2051521 402514 402582 := by
  decide +kernel

private theorem r_402582 : RangeOk getRow 2051521 402582 402650 := by
  decide +kernel

private theorem r_402650 : RangeOk getRow 2051521 402650 402719 := by
  decide +kernel

private theorem r_402719 : RangeOk getRow 2051521 402719 402787 := by
  decide +kernel

private theorem r_402787 : RangeOk getRow 2051521 402787 402856 := by
  decide +kernel

private theorem r_402856 : RangeOk getRow 2051521 402856 402927 := by
  decide +kernel

private theorem r_402927 : RangeOk getRow 2051521 402927 402997 := by
  decide +kernel

private theorem r_402997 : RangeOk getRow 2051521 402997 403066 := by
  decide +kernel

private theorem r_403066 : RangeOk getRow 2051521 403066 403135 := by
  decide +kernel

private theorem r_403135 : RangeOk getRow 2051521 403135 403204 := by
  decide +kernel

private theorem r_403204 : RangeOk getRow 2051521 403204 403272 := by
  decide +kernel

private theorem r_403272 : RangeOk getRow 2051521 403272 403340 := by
  decide +kernel

private theorem r_403340 : RangeOk getRow 2051521 403340 403409 := by
  decide +kernel

private theorem r_403409 : RangeOk getRow 2051521 403409 403479 := by
  decide +kernel

private theorem r_403479 : RangeOk getRow 2051521 403479 403550 := by
  decide +kernel

private theorem r_403550 : RangeOk getRow 2051521 403550 403619 := by
  decide +kernel

private theorem r_403619 : RangeOk getRow 2051521 403619 403688 := by
  decide +kernel

private theorem r_403688 : RangeOk getRow 2051521 403688 403757 := by
  decide +kernel

private theorem r_403757 : RangeOk getRow 2051521 403757 403824 := by
  decide +kernel

private theorem r_403824 : RangeOk getRow 2051521 403824 403893 := by
  decide +kernel

private theorem r_403893 : RangeOk getRow 2051521 403893 403962 := by
  decide +kernel

private theorem r_403962 : RangeOk getRow 2051521 403962 404031 := by
  decide +kernel

private theorem r_404031 : RangeOk getRow 2051521 404031 404100 := by
  decide +kernel

private theorem r_404100 : RangeOk getRow 2051521 404100 404168 := by
  decide +kernel

private theorem r_404168 : RangeOk getRow 2051521 404168 404235 := by
  decide +kernel

private theorem r_404235 : RangeOk getRow 2051521 404235 404303 := by
  decide +kernel

private theorem r_404303 : RangeOk getRow 2051521 404303 404371 := by
  decide +kernel

private theorem r_404371 : RangeOk getRow 2051521 404371 404440 := by
  decide +kernel

private theorem r_404440 : RangeOk getRow 2051521 404440 404509 := by
  decide +kernel

private theorem r_404509 : RangeOk getRow 2051521 404509 404578 := by
  decide +kernel

private theorem r_404578 : RangeOk getRow 2051521 404578 404646 := by
  decide +kernel

private theorem s_402102 : RangeOk getRow 2051521 402035 402102 := r_402035
private theorem s_402170 : RangeOk getRow 2051521 402035 402170 :=
  s_402102.append (by norm_num) r_402102
private theorem s_402238 : RangeOk getRow 2051521 402035 402238 :=
  s_402170.append (by norm_num) r_402170
private theorem s_402307 : RangeOk getRow 2051521 402035 402307 :=
  s_402238.append (by norm_num) r_402238
private theorem s_402377 : RangeOk getRow 2051521 402035 402377 :=
  s_402307.append (by norm_num) r_402307
private theorem s_402446 : RangeOk getRow 2051521 402035 402446 :=
  s_402377.append (by norm_num) r_402377
private theorem s_402514 : RangeOk getRow 2051521 402035 402514 :=
  s_402446.append (by norm_num) r_402446
private theorem s_402582 : RangeOk getRow 2051521 402035 402582 :=
  s_402514.append (by norm_num) r_402514
private theorem s_402650 : RangeOk getRow 2051521 402035 402650 :=
  s_402582.append (by norm_num) r_402582
private theorem s_402719 : RangeOk getRow 2051521 402035 402719 :=
  s_402650.append (by norm_num) r_402650
private theorem s_402787 : RangeOk getRow 2051521 402035 402787 :=
  s_402719.append (by norm_num) r_402719
private theorem s_402856 : RangeOk getRow 2051521 402035 402856 :=
  s_402787.append (by norm_num) r_402787
private theorem s_402927 : RangeOk getRow 2051521 402035 402927 :=
  s_402856.append (by norm_num) r_402856
private theorem s_402997 : RangeOk getRow 2051521 402035 402997 :=
  s_402927.append (by norm_num) r_402927
private theorem s_403066 : RangeOk getRow 2051521 402035 403066 :=
  s_402997.append (by norm_num) r_402997
private theorem s_403135 : RangeOk getRow 2051521 402035 403135 :=
  s_403066.append (by norm_num) r_403066
private theorem s_403204 : RangeOk getRow 2051521 402035 403204 :=
  s_403135.append (by norm_num) r_403135
private theorem s_403272 : RangeOk getRow 2051521 402035 403272 :=
  s_403204.append (by norm_num) r_403204
private theorem s_403340 : RangeOk getRow 2051521 402035 403340 :=
  s_403272.append (by norm_num) r_403272
private theorem s_403409 : RangeOk getRow 2051521 402035 403409 :=
  s_403340.append (by norm_num) r_403340
private theorem s_403479 : RangeOk getRow 2051521 402035 403479 :=
  s_403409.append (by norm_num) r_403409
private theorem s_403550 : RangeOk getRow 2051521 402035 403550 :=
  s_403479.append (by norm_num) r_403479
private theorem s_403619 : RangeOk getRow 2051521 402035 403619 :=
  s_403550.append (by norm_num) r_403550
private theorem s_403688 : RangeOk getRow 2051521 402035 403688 :=
  s_403619.append (by norm_num) r_403619
private theorem s_403757 : RangeOk getRow 2051521 402035 403757 :=
  s_403688.append (by norm_num) r_403688
private theorem s_403824 : RangeOk getRow 2051521 402035 403824 :=
  s_403757.append (by norm_num) r_403757
private theorem s_403893 : RangeOk getRow 2051521 402035 403893 :=
  s_403824.append (by norm_num) r_403824
private theorem s_403962 : RangeOk getRow 2051521 402035 403962 :=
  s_403893.append (by norm_num) r_403893
private theorem s_404031 : RangeOk getRow 2051521 402035 404031 :=
  s_403962.append (by norm_num) r_403962
private theorem s_404100 : RangeOk getRow 2051521 402035 404100 :=
  s_404031.append (by norm_num) r_404031
private theorem s_404168 : RangeOk getRow 2051521 402035 404168 :=
  s_404100.append (by norm_num) r_404100
private theorem s_404235 : RangeOk getRow 2051521 402035 404235 :=
  s_404168.append (by norm_num) r_404168
private theorem s_404303 : RangeOk getRow 2051521 402035 404303 :=
  s_404235.append (by norm_num) r_404235
private theorem s_404371 : RangeOk getRow 2051521 402035 404371 :=
  s_404303.append (by norm_num) r_404303
private theorem s_404440 : RangeOk getRow 2051521 402035 404440 :=
  s_404371.append (by norm_num) r_404371
private theorem s_404509 : RangeOk getRow 2051521 402035 404509 :=
  s_404440.append (by norm_num) r_404440
private theorem s_404578 : RangeOk getRow 2051521 402035 404578 :=
  s_404509.append (by norm_num) r_404509
private theorem s_404646 : RangeOk getRow 2051521 402035 404646 :=
  s_404578.append (by norm_num) r_404578

/-- Rows `[402035, 404646)` are valid. -/
theorem rangeOk_402035_404646 : RangeOk getRow 2051521 402035 404646 := s_404646

end Noperthedron.Solution
