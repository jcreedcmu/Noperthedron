import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[541943, 544484). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_541943 : RangeOk getRow 2051521 541943 542010 := by
  decide +kernel

private theorem r_542010 : RangeOk getRow 2051521 542010 542077 := by
  decide +kernel

private theorem r_542077 : RangeOk getRow 2051521 542077 542144 := by
  decide +kernel

private theorem r_542144 : RangeOk getRow 2051521 542144 542212 := by
  decide +kernel

private theorem r_542212 : RangeOk getRow 2051521 542212 542278 := by
  decide +kernel

private theorem r_542278 : RangeOk getRow 2051521 542278 542344 := by
  decide +kernel

private theorem r_542344 : RangeOk getRow 2051521 542344 542409 := by
  decide +kernel

private theorem r_542409 : RangeOk getRow 2051521 542409 542477 := by
  decide +kernel

private theorem r_542477 : RangeOk getRow 2051521 542477 542542 := by
  decide +kernel

private theorem r_542542 : RangeOk getRow 2051521 542542 542609 := by
  decide +kernel

private theorem r_542609 : RangeOk getRow 2051521 542609 542676 := by
  decide +kernel

private theorem r_542676 : RangeOk getRow 2051521 542676 542743 := by
  decide +kernel

private theorem r_542743 : RangeOk getRow 2051521 542743 542809 := by
  decide +kernel

private theorem r_542809 : RangeOk getRow 2051521 542809 542874 := by
  decide +kernel

private theorem r_542874 : RangeOk getRow 2051521 542874 542940 := by
  decide +kernel

private theorem r_542940 : RangeOk getRow 2051521 542940 543008 := by
  decide +kernel

private theorem r_543008 : RangeOk getRow 2051521 543008 543075 := by
  decide +kernel

private theorem r_543075 : RangeOk getRow 2051521 543075 543142 := by
  decide +kernel

private theorem r_543142 : RangeOk getRow 2051521 543142 543208 := by
  decide +kernel

private theorem r_543208 : RangeOk getRow 2051521 543208 543273 := by
  decide +kernel

private theorem r_543273 : RangeOk getRow 2051521 543273 543338 := by
  decide +kernel

private theorem r_543338 : RangeOk getRow 2051521 543338 543406 := by
  decide +kernel

private theorem r_543406 : RangeOk getRow 2051521 543406 543482 := by
  decide +kernel

private theorem r_543482 : RangeOk getRow 2051521 543482 543556 := by
  decide +kernel

private theorem r_543556 : RangeOk getRow 2051521 543556 543629 := by
  decide +kernel

private theorem r_543629 : RangeOk getRow 2051521 543629 543702 := by
  decide +kernel

private theorem r_543702 : RangeOk getRow 2051521 543702 543774 := by
  decide +kernel

private theorem r_543774 : RangeOk getRow 2051521 543774 543848 := by
  decide +kernel

private theorem r_543848 : RangeOk getRow 2051521 543848 543921 := by
  decide +kernel

private theorem r_543921 : RangeOk getRow 2051521 543921 543992 := by
  decide +kernel

private theorem r_543992 : RangeOk getRow 2051521 543992 544063 := by
  decide +kernel

private theorem r_544063 : RangeOk getRow 2051521 544063 544131 := by
  decide +kernel

private theorem r_544131 : RangeOk getRow 2051521 544131 544199 := by
  decide +kernel

private theorem r_544199 : RangeOk getRow 2051521 544199 544267 := by
  decide +kernel

private theorem r_544267 : RangeOk getRow 2051521 544267 544335 := by
  decide +kernel

private theorem r_544335 : RangeOk getRow 2051521 544335 544409 := by
  decide +kernel

private theorem r_544409 : RangeOk getRow 2051521 544409 544484 := by
  decide +kernel

private theorem s_542010 : RangeOk getRow 2051521 541943 542010 := r_541943
private theorem s_542077 : RangeOk getRow 2051521 541943 542077 :=
  s_542010.append (by norm_num) r_542010
private theorem s_542144 : RangeOk getRow 2051521 541943 542144 :=
  s_542077.append (by norm_num) r_542077
private theorem s_542212 : RangeOk getRow 2051521 541943 542212 :=
  s_542144.append (by norm_num) r_542144
private theorem s_542278 : RangeOk getRow 2051521 541943 542278 :=
  s_542212.append (by norm_num) r_542212
private theorem s_542344 : RangeOk getRow 2051521 541943 542344 :=
  s_542278.append (by norm_num) r_542278
private theorem s_542409 : RangeOk getRow 2051521 541943 542409 :=
  s_542344.append (by norm_num) r_542344
private theorem s_542477 : RangeOk getRow 2051521 541943 542477 :=
  s_542409.append (by norm_num) r_542409
private theorem s_542542 : RangeOk getRow 2051521 541943 542542 :=
  s_542477.append (by norm_num) r_542477
private theorem s_542609 : RangeOk getRow 2051521 541943 542609 :=
  s_542542.append (by norm_num) r_542542
private theorem s_542676 : RangeOk getRow 2051521 541943 542676 :=
  s_542609.append (by norm_num) r_542609
private theorem s_542743 : RangeOk getRow 2051521 541943 542743 :=
  s_542676.append (by norm_num) r_542676
private theorem s_542809 : RangeOk getRow 2051521 541943 542809 :=
  s_542743.append (by norm_num) r_542743
private theorem s_542874 : RangeOk getRow 2051521 541943 542874 :=
  s_542809.append (by norm_num) r_542809
private theorem s_542940 : RangeOk getRow 2051521 541943 542940 :=
  s_542874.append (by norm_num) r_542874
private theorem s_543008 : RangeOk getRow 2051521 541943 543008 :=
  s_542940.append (by norm_num) r_542940
private theorem s_543075 : RangeOk getRow 2051521 541943 543075 :=
  s_543008.append (by norm_num) r_543008
private theorem s_543142 : RangeOk getRow 2051521 541943 543142 :=
  s_543075.append (by norm_num) r_543075
private theorem s_543208 : RangeOk getRow 2051521 541943 543208 :=
  s_543142.append (by norm_num) r_543142
private theorem s_543273 : RangeOk getRow 2051521 541943 543273 :=
  s_543208.append (by norm_num) r_543208
private theorem s_543338 : RangeOk getRow 2051521 541943 543338 :=
  s_543273.append (by norm_num) r_543273
private theorem s_543406 : RangeOk getRow 2051521 541943 543406 :=
  s_543338.append (by norm_num) r_543338
private theorem s_543482 : RangeOk getRow 2051521 541943 543482 :=
  s_543406.append (by norm_num) r_543406
private theorem s_543556 : RangeOk getRow 2051521 541943 543556 :=
  s_543482.append (by norm_num) r_543482
private theorem s_543629 : RangeOk getRow 2051521 541943 543629 :=
  s_543556.append (by norm_num) r_543556
private theorem s_543702 : RangeOk getRow 2051521 541943 543702 :=
  s_543629.append (by norm_num) r_543629
private theorem s_543774 : RangeOk getRow 2051521 541943 543774 :=
  s_543702.append (by norm_num) r_543702
private theorem s_543848 : RangeOk getRow 2051521 541943 543848 :=
  s_543774.append (by norm_num) r_543774
private theorem s_543921 : RangeOk getRow 2051521 541943 543921 :=
  s_543848.append (by norm_num) r_543848
private theorem s_543992 : RangeOk getRow 2051521 541943 543992 :=
  s_543921.append (by norm_num) r_543921
private theorem s_544063 : RangeOk getRow 2051521 541943 544063 :=
  s_543992.append (by norm_num) r_543992
private theorem s_544131 : RangeOk getRow 2051521 541943 544131 :=
  s_544063.append (by norm_num) r_544063
private theorem s_544199 : RangeOk getRow 2051521 541943 544199 :=
  s_544131.append (by norm_num) r_544131
private theorem s_544267 : RangeOk getRow 2051521 541943 544267 :=
  s_544199.append (by norm_num) r_544199
private theorem s_544335 : RangeOk getRow 2051521 541943 544335 :=
  s_544267.append (by norm_num) r_544267
private theorem s_544409 : RangeOk getRow 2051521 541943 544409 :=
  s_544335.append (by norm_num) r_544335
private theorem s_544484 : RangeOk getRow 2051521 541943 544484 :=
  s_544409.append (by norm_num) r_544409

/-- Rows `[541943, 544484)` are valid. -/
theorem rangeOk_541943_544484 : RangeOk getRow 2051521 541943 544484 := s_544484

end Noperthedron.Solution
