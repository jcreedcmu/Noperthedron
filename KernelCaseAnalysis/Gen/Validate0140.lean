import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[328001, 330513). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_328001 : RangeOk getRow 2051521 328001 328070 := by
  decide +kernel

private theorem r_328070 : RangeOk getRow 2051521 328070 328140 := by
  decide +kernel

private theorem r_328140 : RangeOk getRow 2051521 328140 328208 := by
  decide +kernel

private theorem r_328208 : RangeOk getRow 2051521 328208 328277 := by
  decide +kernel

private theorem r_328277 : RangeOk getRow 2051521 328277 328346 := by
  decide +kernel

private theorem r_328346 : RangeOk getRow 2051521 328346 328414 := by
  decide +kernel

private theorem r_328414 : RangeOk getRow 2051521 328414 328481 := by
  decide +kernel

private theorem r_328481 : RangeOk getRow 2051521 328481 328550 := by
  decide +kernel

private theorem r_328550 : RangeOk getRow 2051521 328550 328620 := by
  decide +kernel

private theorem r_328620 : RangeOk getRow 2051521 328620 328689 := by
  decide +kernel

private theorem r_328689 : RangeOk getRow 2051521 328689 328757 := by
  decide +kernel

private theorem r_328757 : RangeOk getRow 2051521 328757 328809 := by
  decide +kernel

private theorem r_328809 : RangeOk getRow 2051521 328809 328878 := by
  decide +kernel

private theorem r_328878 : RangeOk getRow 2051521 328878 328948 := by
  decide +kernel

private theorem r_328948 : RangeOk getRow 2051521 328948 329015 := by
  decide +kernel

private theorem r_329015 : RangeOk getRow 2051521 329015 329083 := by
  decide +kernel

private theorem r_329083 : RangeOk getRow 2051521 329083 329153 := by
  decide +kernel

private theorem r_329153 : RangeOk getRow 2051521 329153 329222 := by
  decide +kernel

private theorem r_329222 : RangeOk getRow 2051521 329222 329289 := by
  decide +kernel

private theorem r_329289 : RangeOk getRow 2051521 329289 329354 := by
  decide +kernel

private theorem r_329354 : RangeOk getRow 2051521 329354 329422 := by
  decide +kernel

private theorem r_329422 : RangeOk getRow 2051521 329422 329491 := by
  decide +kernel

private theorem r_329491 : RangeOk getRow 2051521 329491 329558 := by
  decide +kernel

private theorem r_329558 : RangeOk getRow 2051521 329558 329627 := by
  decide +kernel

private theorem r_329627 : RangeOk getRow 2051521 329627 329697 := by
  decide +kernel

private theorem r_329697 : RangeOk getRow 2051521 329697 329766 := by
  decide +kernel

private theorem r_329766 : RangeOk getRow 2051521 329766 329833 := by
  decide +kernel

private theorem r_329833 : RangeOk getRow 2051521 329833 329899 := by
  decide +kernel

private theorem r_329899 : RangeOk getRow 2051521 329899 329966 := by
  decide +kernel

private theorem r_329966 : RangeOk getRow 2051521 329966 330035 := by
  decide +kernel

private theorem r_330035 : RangeOk getRow 2051521 330035 330103 := by
  decide +kernel

private theorem r_330103 : RangeOk getRow 2051521 330103 330173 := by
  decide +kernel

private theorem r_330173 : RangeOk getRow 2051521 330173 330242 := by
  decide +kernel

private theorem r_330242 : RangeOk getRow 2051521 330242 330309 := by
  decide +kernel

private theorem r_330309 : RangeOk getRow 2051521 330309 330377 := by
  decide +kernel

private theorem r_330377 : RangeOk getRow 2051521 330377 330446 := by
  decide +kernel

private theorem r_330446 : RangeOk getRow 2051521 330446 330513 := by
  decide +kernel

private theorem s_328070 : RangeOk getRow 2051521 328001 328070 := r_328001
private theorem s_328140 : RangeOk getRow 2051521 328001 328140 :=
  s_328070.append (by norm_num) r_328070
private theorem s_328208 : RangeOk getRow 2051521 328001 328208 :=
  s_328140.append (by norm_num) r_328140
private theorem s_328277 : RangeOk getRow 2051521 328001 328277 :=
  s_328208.append (by norm_num) r_328208
private theorem s_328346 : RangeOk getRow 2051521 328001 328346 :=
  s_328277.append (by norm_num) r_328277
private theorem s_328414 : RangeOk getRow 2051521 328001 328414 :=
  s_328346.append (by norm_num) r_328346
private theorem s_328481 : RangeOk getRow 2051521 328001 328481 :=
  s_328414.append (by norm_num) r_328414
private theorem s_328550 : RangeOk getRow 2051521 328001 328550 :=
  s_328481.append (by norm_num) r_328481
private theorem s_328620 : RangeOk getRow 2051521 328001 328620 :=
  s_328550.append (by norm_num) r_328550
private theorem s_328689 : RangeOk getRow 2051521 328001 328689 :=
  s_328620.append (by norm_num) r_328620
private theorem s_328757 : RangeOk getRow 2051521 328001 328757 :=
  s_328689.append (by norm_num) r_328689
private theorem s_328809 : RangeOk getRow 2051521 328001 328809 :=
  s_328757.append (by norm_num) r_328757
private theorem s_328878 : RangeOk getRow 2051521 328001 328878 :=
  s_328809.append (by norm_num) r_328809
private theorem s_328948 : RangeOk getRow 2051521 328001 328948 :=
  s_328878.append (by norm_num) r_328878
private theorem s_329015 : RangeOk getRow 2051521 328001 329015 :=
  s_328948.append (by norm_num) r_328948
private theorem s_329083 : RangeOk getRow 2051521 328001 329083 :=
  s_329015.append (by norm_num) r_329015
private theorem s_329153 : RangeOk getRow 2051521 328001 329153 :=
  s_329083.append (by norm_num) r_329083
private theorem s_329222 : RangeOk getRow 2051521 328001 329222 :=
  s_329153.append (by norm_num) r_329153
private theorem s_329289 : RangeOk getRow 2051521 328001 329289 :=
  s_329222.append (by norm_num) r_329222
private theorem s_329354 : RangeOk getRow 2051521 328001 329354 :=
  s_329289.append (by norm_num) r_329289
private theorem s_329422 : RangeOk getRow 2051521 328001 329422 :=
  s_329354.append (by norm_num) r_329354
private theorem s_329491 : RangeOk getRow 2051521 328001 329491 :=
  s_329422.append (by norm_num) r_329422
private theorem s_329558 : RangeOk getRow 2051521 328001 329558 :=
  s_329491.append (by norm_num) r_329491
private theorem s_329627 : RangeOk getRow 2051521 328001 329627 :=
  s_329558.append (by norm_num) r_329558
private theorem s_329697 : RangeOk getRow 2051521 328001 329697 :=
  s_329627.append (by norm_num) r_329627
private theorem s_329766 : RangeOk getRow 2051521 328001 329766 :=
  s_329697.append (by norm_num) r_329697
private theorem s_329833 : RangeOk getRow 2051521 328001 329833 :=
  s_329766.append (by norm_num) r_329766
private theorem s_329899 : RangeOk getRow 2051521 328001 329899 :=
  s_329833.append (by norm_num) r_329833
private theorem s_329966 : RangeOk getRow 2051521 328001 329966 :=
  s_329899.append (by norm_num) r_329899
private theorem s_330035 : RangeOk getRow 2051521 328001 330035 :=
  s_329966.append (by norm_num) r_329966
private theorem s_330103 : RangeOk getRow 2051521 328001 330103 :=
  s_330035.append (by norm_num) r_330035
private theorem s_330173 : RangeOk getRow 2051521 328001 330173 :=
  s_330103.append (by norm_num) r_330103
private theorem s_330242 : RangeOk getRow 2051521 328001 330242 :=
  s_330173.append (by norm_num) r_330173
private theorem s_330309 : RangeOk getRow 2051521 328001 330309 :=
  s_330242.append (by norm_num) r_330242
private theorem s_330377 : RangeOk getRow 2051521 328001 330377 :=
  s_330309.append (by norm_num) r_330309
private theorem s_330446 : RangeOk getRow 2051521 328001 330446 :=
  s_330377.append (by norm_num) r_330377
private theorem s_330513 : RangeOk getRow 2051521 328001 330513 :=
  s_330446.append (by norm_num) r_330446

/-- Rows `[328001, 330513)` are valid. -/
theorem rangeOk_328001_330513 : RangeOk getRow 2051521 328001 330513 := s_330513

end Noperthedron.Solution
