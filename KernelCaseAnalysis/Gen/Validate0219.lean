import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[529817, 532358). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_529817 : RangeOk getRow 2051521 529817 529886 := by
  decide +kernel

private theorem r_529886 : RangeOk getRow 2051521 529886 529956 := by
  decide +kernel

private theorem r_529956 : RangeOk getRow 2051521 529956 530025 := by
  decide +kernel

private theorem r_530025 : RangeOk getRow 2051521 530025 530091 := by
  decide +kernel

private theorem r_530091 : RangeOk getRow 2051521 530091 530159 := by
  decide +kernel

private theorem r_530159 : RangeOk getRow 2051521 530159 530228 := by
  decide +kernel

private theorem r_530228 : RangeOk getRow 2051521 530228 530297 := by
  decide +kernel

private theorem r_530297 : RangeOk getRow 2051521 530297 530367 := by
  decide +kernel

private theorem r_530367 : RangeOk getRow 2051521 530367 530436 := by
  decide +kernel

private theorem r_530436 : RangeOk getRow 2051521 530436 530503 := by
  decide +kernel

private theorem r_530503 : RangeOk getRow 2051521 530503 530571 := by
  decide +kernel

private theorem r_530571 : RangeOk getRow 2051521 530571 530639 := by
  decide +kernel

private theorem r_530639 : RangeOk getRow 2051521 530639 530707 := by
  decide +kernel

private theorem r_530707 : RangeOk getRow 2051521 530707 530775 := by
  decide +kernel

private theorem r_530775 : RangeOk getRow 2051521 530775 530844 := by
  decide +kernel

private theorem r_530844 : RangeOk getRow 2051521 530844 530912 := by
  decide +kernel

private theorem r_530912 : RangeOk getRow 2051521 530912 530981 := by
  decide +kernel

private theorem r_530981 : RangeOk getRow 2051521 530981 531050 := by
  decide +kernel

private theorem r_531050 : RangeOk getRow 2051521 531050 531118 := by
  decide +kernel

private theorem r_531118 : RangeOk getRow 2051521 531118 531188 := by
  decide +kernel

private theorem r_531188 : RangeOk getRow 2051521 531188 531255 := by
  decide +kernel

private theorem r_531255 : RangeOk getRow 2051521 531255 531324 := by
  decide +kernel

private theorem r_531324 : RangeOk getRow 2051521 531324 531394 := by
  decide +kernel

private theorem r_531394 : RangeOk getRow 2051521 531394 531464 := by
  decide +kernel

private theorem r_531464 : RangeOk getRow 2051521 531464 531533 := by
  decide +kernel

private theorem r_531533 : RangeOk getRow 2051521 531533 531602 := by
  decide +kernel

private theorem r_531602 : RangeOk getRow 2051521 531602 531671 := by
  decide +kernel

private theorem r_531671 : RangeOk getRow 2051521 531671 531741 := by
  decide +kernel

private theorem r_531741 : RangeOk getRow 2051521 531741 531809 := by
  decide +kernel

private theorem r_531809 : RangeOk getRow 2051521 531809 531877 := by
  decide +kernel

private theorem r_531877 : RangeOk getRow 2051521 531877 531945 := by
  decide +kernel

private theorem r_531945 : RangeOk getRow 2051521 531945 532015 := by
  decide +kernel

private theorem r_532015 : RangeOk getRow 2051521 532015 532085 := by
  decide +kernel

private theorem r_532085 : RangeOk getRow 2051521 532085 532154 := by
  decide +kernel

private theorem r_532154 : RangeOk getRow 2051521 532154 532222 := by
  decide +kernel

private theorem r_532222 : RangeOk getRow 2051521 532222 532291 := by
  decide +kernel

private theorem r_532291 : RangeOk getRow 2051521 532291 532358 := by
  decide +kernel

private theorem s_529886 : RangeOk getRow 2051521 529817 529886 := r_529817
private theorem s_529956 : RangeOk getRow 2051521 529817 529956 :=
  s_529886.append (by norm_num) r_529886
private theorem s_530025 : RangeOk getRow 2051521 529817 530025 :=
  s_529956.append (by norm_num) r_529956
private theorem s_530091 : RangeOk getRow 2051521 529817 530091 :=
  s_530025.append (by norm_num) r_530025
private theorem s_530159 : RangeOk getRow 2051521 529817 530159 :=
  s_530091.append (by norm_num) r_530091
private theorem s_530228 : RangeOk getRow 2051521 529817 530228 :=
  s_530159.append (by norm_num) r_530159
private theorem s_530297 : RangeOk getRow 2051521 529817 530297 :=
  s_530228.append (by norm_num) r_530228
private theorem s_530367 : RangeOk getRow 2051521 529817 530367 :=
  s_530297.append (by norm_num) r_530297
private theorem s_530436 : RangeOk getRow 2051521 529817 530436 :=
  s_530367.append (by norm_num) r_530367
private theorem s_530503 : RangeOk getRow 2051521 529817 530503 :=
  s_530436.append (by norm_num) r_530436
private theorem s_530571 : RangeOk getRow 2051521 529817 530571 :=
  s_530503.append (by norm_num) r_530503
private theorem s_530639 : RangeOk getRow 2051521 529817 530639 :=
  s_530571.append (by norm_num) r_530571
private theorem s_530707 : RangeOk getRow 2051521 529817 530707 :=
  s_530639.append (by norm_num) r_530639
private theorem s_530775 : RangeOk getRow 2051521 529817 530775 :=
  s_530707.append (by norm_num) r_530707
private theorem s_530844 : RangeOk getRow 2051521 529817 530844 :=
  s_530775.append (by norm_num) r_530775
private theorem s_530912 : RangeOk getRow 2051521 529817 530912 :=
  s_530844.append (by norm_num) r_530844
private theorem s_530981 : RangeOk getRow 2051521 529817 530981 :=
  s_530912.append (by norm_num) r_530912
private theorem s_531050 : RangeOk getRow 2051521 529817 531050 :=
  s_530981.append (by norm_num) r_530981
private theorem s_531118 : RangeOk getRow 2051521 529817 531118 :=
  s_531050.append (by norm_num) r_531050
private theorem s_531188 : RangeOk getRow 2051521 529817 531188 :=
  s_531118.append (by norm_num) r_531118
private theorem s_531255 : RangeOk getRow 2051521 529817 531255 :=
  s_531188.append (by norm_num) r_531188
private theorem s_531324 : RangeOk getRow 2051521 529817 531324 :=
  s_531255.append (by norm_num) r_531255
private theorem s_531394 : RangeOk getRow 2051521 529817 531394 :=
  s_531324.append (by norm_num) r_531324
private theorem s_531464 : RangeOk getRow 2051521 529817 531464 :=
  s_531394.append (by norm_num) r_531394
private theorem s_531533 : RangeOk getRow 2051521 529817 531533 :=
  s_531464.append (by norm_num) r_531464
private theorem s_531602 : RangeOk getRow 2051521 529817 531602 :=
  s_531533.append (by norm_num) r_531533
private theorem s_531671 : RangeOk getRow 2051521 529817 531671 :=
  s_531602.append (by norm_num) r_531602
private theorem s_531741 : RangeOk getRow 2051521 529817 531741 :=
  s_531671.append (by norm_num) r_531671
private theorem s_531809 : RangeOk getRow 2051521 529817 531809 :=
  s_531741.append (by norm_num) r_531741
private theorem s_531877 : RangeOk getRow 2051521 529817 531877 :=
  s_531809.append (by norm_num) r_531809
private theorem s_531945 : RangeOk getRow 2051521 529817 531945 :=
  s_531877.append (by norm_num) r_531877
private theorem s_532015 : RangeOk getRow 2051521 529817 532015 :=
  s_531945.append (by norm_num) r_531945
private theorem s_532085 : RangeOk getRow 2051521 529817 532085 :=
  s_532015.append (by norm_num) r_532015
private theorem s_532154 : RangeOk getRow 2051521 529817 532154 :=
  s_532085.append (by norm_num) r_532085
private theorem s_532222 : RangeOk getRow 2051521 529817 532222 :=
  s_532154.append (by norm_num) r_532154
private theorem s_532291 : RangeOk getRow 2051521 529817 532291 :=
  s_532222.append (by norm_num) r_532222
private theorem s_532358 : RangeOk getRow 2051521 529817 532358 :=
  s_532291.append (by norm_num) r_532291

/-- Rows `[529817, 532358)` are valid. -/
theorem rangeOk_529817_532358 : RangeOk getRow 2051521 529817 532358 := s_532358

end Noperthedron.Solution
