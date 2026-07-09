import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[468255, 470380). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_468255 : RangeOk getRow 2051521 468255 468320 := by
  decide +kernel

private theorem r_468320 : RangeOk getRow 2051521 468320 468387 := by
  decide +kernel

private theorem r_468387 : RangeOk getRow 2051521 468387 468454 := by
  decide +kernel

private theorem r_468454 : RangeOk getRow 2051521 468454 468520 := by
  decide +kernel

private theorem r_468520 : RangeOk getRow 2051521 468520 468586 := by
  decide +kernel

private theorem r_468586 : RangeOk getRow 2051521 468586 468651 := by
  decide +kernel

private theorem r_468651 : RangeOk getRow 2051521 468651 468718 := by
  decide +kernel

private theorem r_468718 : RangeOk getRow 2051521 468718 468785 := by
  decide +kernel

private theorem r_468785 : RangeOk getRow 2051521 468785 468851 := by
  decide +kernel

private theorem r_468851 : RangeOk getRow 2051521 468851 468918 := by
  decide +kernel

private theorem r_468918 : RangeOk getRow 2051521 468918 468986 := by
  decide +kernel

private theorem r_468986 : RangeOk getRow 2051521 468986 469052 := by
  decide +kernel

private theorem r_469052 : RangeOk getRow 2051521 469052 469118 := by
  decide +kernel

private theorem r_469118 : RangeOk getRow 2051521 469118 469183 := by
  decide +kernel

private theorem r_469183 : RangeOk getRow 2051521 469183 469250 := by
  decide +kernel

private theorem r_469250 : RangeOk getRow 2051521 469250 469318 := by
  decide +kernel

private theorem r_469318 : RangeOk getRow 2051521 469318 469385 := by
  decide +kernel

private theorem r_469385 : RangeOk getRow 2051521 469385 469451 := by
  decide +kernel

private theorem r_469451 : RangeOk getRow 2051521 469451 469517 := by
  decide +kernel

private theorem r_469517 : RangeOk getRow 2051521 469517 469583 := by
  decide +kernel

private theorem r_469583 : RangeOk getRow 2051521 469583 469649 := by
  decide +kernel

private theorem r_469649 : RangeOk getRow 2051521 469649 469715 := by
  decide +kernel

private theorem r_469715 : RangeOk getRow 2051521 469715 469782 := by
  decide +kernel

private theorem r_469782 : RangeOk getRow 2051521 469782 469848 := by
  decide +kernel

private theorem r_469848 : RangeOk getRow 2051521 469848 469915 := by
  decide +kernel

private theorem r_469915 : RangeOk getRow 2051521 469915 469982 := by
  decide +kernel

private theorem r_469982 : RangeOk getRow 2051521 469982 470048 := by
  decide +kernel

private theorem r_470048 : RangeOk getRow 2051521 470048 470114 := by
  decide +kernel

private theorem r_470114 : RangeOk getRow 2051521 470114 470179 := by
  decide +kernel

private theorem r_470179 : RangeOk getRow 2051521 470179 470246 := by
  decide +kernel

private theorem r_470246 : RangeOk getRow 2051521 470246 470312 := by
  decide +kernel

private theorem r_470312 : RangeOk getRow 2051521 470312 470380 := by
  decide +kernel

private theorem s_468320 : RangeOk getRow 2051521 468255 468320 := r_468255
private theorem s_468387 : RangeOk getRow 2051521 468255 468387 :=
  s_468320.append (by norm_num) r_468320
private theorem s_468454 : RangeOk getRow 2051521 468255 468454 :=
  s_468387.append (by norm_num) r_468387
private theorem s_468520 : RangeOk getRow 2051521 468255 468520 :=
  s_468454.append (by norm_num) r_468454
private theorem s_468586 : RangeOk getRow 2051521 468255 468586 :=
  s_468520.append (by norm_num) r_468520
private theorem s_468651 : RangeOk getRow 2051521 468255 468651 :=
  s_468586.append (by norm_num) r_468586
private theorem s_468718 : RangeOk getRow 2051521 468255 468718 :=
  s_468651.append (by norm_num) r_468651
private theorem s_468785 : RangeOk getRow 2051521 468255 468785 :=
  s_468718.append (by norm_num) r_468718
private theorem s_468851 : RangeOk getRow 2051521 468255 468851 :=
  s_468785.append (by norm_num) r_468785
private theorem s_468918 : RangeOk getRow 2051521 468255 468918 :=
  s_468851.append (by norm_num) r_468851
private theorem s_468986 : RangeOk getRow 2051521 468255 468986 :=
  s_468918.append (by norm_num) r_468918
private theorem s_469052 : RangeOk getRow 2051521 468255 469052 :=
  s_468986.append (by norm_num) r_468986
private theorem s_469118 : RangeOk getRow 2051521 468255 469118 :=
  s_469052.append (by norm_num) r_469052
private theorem s_469183 : RangeOk getRow 2051521 468255 469183 :=
  s_469118.append (by norm_num) r_469118
private theorem s_469250 : RangeOk getRow 2051521 468255 469250 :=
  s_469183.append (by norm_num) r_469183
private theorem s_469318 : RangeOk getRow 2051521 468255 469318 :=
  s_469250.append (by norm_num) r_469250
private theorem s_469385 : RangeOk getRow 2051521 468255 469385 :=
  s_469318.append (by norm_num) r_469318
private theorem s_469451 : RangeOk getRow 2051521 468255 469451 :=
  s_469385.append (by norm_num) r_469385
private theorem s_469517 : RangeOk getRow 2051521 468255 469517 :=
  s_469451.append (by norm_num) r_469451
private theorem s_469583 : RangeOk getRow 2051521 468255 469583 :=
  s_469517.append (by norm_num) r_469517
private theorem s_469649 : RangeOk getRow 2051521 468255 469649 :=
  s_469583.append (by norm_num) r_469583
private theorem s_469715 : RangeOk getRow 2051521 468255 469715 :=
  s_469649.append (by norm_num) r_469649
private theorem s_469782 : RangeOk getRow 2051521 468255 469782 :=
  s_469715.append (by norm_num) r_469715
private theorem s_469848 : RangeOk getRow 2051521 468255 469848 :=
  s_469782.append (by norm_num) r_469782
private theorem s_469915 : RangeOk getRow 2051521 468255 469915 :=
  s_469848.append (by norm_num) r_469848
private theorem s_469982 : RangeOk getRow 2051521 468255 469982 :=
  s_469915.append (by norm_num) r_469915
private theorem s_470048 : RangeOk getRow 2051521 468255 470048 :=
  s_469982.append (by norm_num) r_469982
private theorem s_470114 : RangeOk getRow 2051521 468255 470114 :=
  s_470048.append (by norm_num) r_470048
private theorem s_470179 : RangeOk getRow 2051521 468255 470179 :=
  s_470114.append (by norm_num) r_470114
private theorem s_470246 : RangeOk getRow 2051521 468255 470246 :=
  s_470179.append (by norm_num) r_470179
private theorem s_470312 : RangeOk getRow 2051521 468255 470312 :=
  s_470246.append (by norm_num) r_470246
private theorem s_470380 : RangeOk getRow 2051521 468255 470380 :=
  s_470312.append (by norm_num) r_470312

/-- Rows `[468255, 470380)` are valid. -/
theorem rangeOk_468255_470380 : RangeOk getRow 2051521 468255 470380 := s_470380

end Noperthedron.Solution
