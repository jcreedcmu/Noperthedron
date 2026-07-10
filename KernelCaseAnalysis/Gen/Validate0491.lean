import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1211140, 1213127). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1211140 : RangeOk getRow 2051521 1211140 1211163 := by
  decide +kernel

private theorem r_1211163 : RangeOk getRow 2051521 1211163 1211178 := by
  decide +kernel

private theorem r_1211178 : RangeOk getRow 2051521 1211178 1211206 := by
  decide +kernel

private theorem r_1211206 : RangeOk getRow 2051521 1211206 1211222 := by
  decide +kernel

private theorem r_1211222 : RangeOk getRow 2051521 1211222 1211244 := by
  decide +kernel

private theorem r_1211244 : RangeOk getRow 2051521 1211244 1211312 := by
  decide +kernel

private theorem r_1211312 : RangeOk getRow 2051521 1211312 1211380 := by
  decide +kernel

private theorem r_1211380 : RangeOk getRow 2051521 1211380 1211444 := by
  decide +kernel

private theorem r_1211444 : RangeOk getRow 2051521 1211444 1211495 := by
  decide +kernel

private theorem r_1211495 : RangeOk getRow 2051521 1211495 1211529 := by
  decide +kernel

private theorem r_1211529 : RangeOk getRow 2051521 1211529 1211539 := by
  decide +kernel

private theorem r_1211539 : RangeOk getRow 2051521 1211539 1211549 := by
  decide +kernel

private theorem r_1211549 : RangeOk getRow 2051521 1211549 1211561 := by
  decide +kernel

private theorem r_1211561 : RangeOk getRow 2051521 1211561 1211572 := by
  decide +kernel

private theorem r_1211572 : RangeOk getRow 2051521 1211572 1211582 := by
  decide +kernel

private theorem r_1211582 : RangeOk getRow 2051521 1211582 1211598 := by
  decide +kernel

private theorem r_1211598 : RangeOk getRow 2051521 1211598 1211614 := by
  decide +kernel

private theorem r_1211614 : RangeOk getRow 2051521 1211614 1211679 := by
  decide +kernel

private theorem r_1211679 : RangeOk getRow 2051521 1211679 1211709 := by
  decide +kernel

private theorem r_1211709 : RangeOk getRow 2051521 1211709 1211721 := by
  decide +kernel

private theorem r_1211721 : RangeOk getRow 2051521 1211721 1211734 := by
  decide +kernel

private theorem r_1211734 : RangeOk getRow 2051521 1211734 1211752 := by
  decide +kernel

private theorem r_1211752 : RangeOk getRow 2051521 1211752 1211761 := by
  decide +kernel

private theorem r_1211761 : RangeOk getRow 2051521 1211761 1211777 := by
  decide +kernel

private theorem r_1211777 : RangeOk getRow 2051521 1211777 1211838 := by
  decide +kernel

private theorem r_1211838 : RangeOk getRow 2051521 1211838 1211891 := by
  decide +kernel

private theorem r_1211891 : RangeOk getRow 2051521 1211891 1211901 := by
  decide +kernel

private theorem r_1211901 : RangeOk getRow 2051521 1211901 1211949 := by
  decide +kernel

private theorem r_1211949 : RangeOk getRow 2051521 1211949 1211970 := by
  decide +kernel

private theorem r_1211970 : RangeOk getRow 2051521 1211970 1212004 := by
  decide +kernel

private theorem r_1212004 : RangeOk getRow 2051521 1212004 1212014 := by
  decide +kernel

private theorem r_1212014 : RangeOk getRow 2051521 1212014 1212083 := by
  decide +kernel

private theorem r_1212083 : RangeOk getRow 2051521 1212083 1212152 := by
  decide +kernel

private theorem r_1212152 : RangeOk getRow 2051521 1212152 1212221 := by
  decide +kernel

private theorem r_1212221 : RangeOk getRow 2051521 1212221 1212290 := by
  decide +kernel

private theorem r_1212290 : RangeOk getRow 2051521 1212290 1212359 := by
  decide +kernel

private theorem r_1212359 : RangeOk getRow 2051521 1212359 1212428 := by
  decide +kernel

private theorem r_1212428 : RangeOk getRow 2051521 1212428 1212498 := by
  decide +kernel

private theorem r_1212498 : RangeOk getRow 2051521 1212498 1212567 := by
  decide +kernel

private theorem r_1212567 : RangeOk getRow 2051521 1212567 1212636 := by
  decide +kernel

private theorem r_1212636 : RangeOk getRow 2051521 1212636 1212705 := by
  decide +kernel

private theorem r_1212705 : RangeOk getRow 2051521 1212705 1212775 := by
  decide +kernel

private theorem r_1212775 : RangeOk getRow 2051521 1212775 1212845 := by
  decide +kernel

private theorem r_1212845 : RangeOk getRow 2051521 1212845 1212914 := by
  decide +kernel

private theorem r_1212914 : RangeOk getRow 2051521 1212914 1212984 := by
  decide +kernel

private theorem r_1212984 : RangeOk getRow 2051521 1212984 1213056 := by
  decide +kernel

private theorem r_1213056 : RangeOk getRow 2051521 1213056 1213127 := by
  decide +kernel

private theorem s_1211163 : RangeOk getRow 2051521 1211140 1211163 := r_1211140
private theorem s_1211178 : RangeOk getRow 2051521 1211140 1211178 :=
  s_1211163.append (by norm_num) r_1211163
private theorem s_1211206 : RangeOk getRow 2051521 1211140 1211206 :=
  s_1211178.append (by norm_num) r_1211178
private theorem s_1211222 : RangeOk getRow 2051521 1211140 1211222 :=
  s_1211206.append (by norm_num) r_1211206
private theorem s_1211244 : RangeOk getRow 2051521 1211140 1211244 :=
  s_1211222.append (by norm_num) r_1211222
private theorem s_1211312 : RangeOk getRow 2051521 1211140 1211312 :=
  s_1211244.append (by norm_num) r_1211244
private theorem s_1211380 : RangeOk getRow 2051521 1211140 1211380 :=
  s_1211312.append (by norm_num) r_1211312
private theorem s_1211444 : RangeOk getRow 2051521 1211140 1211444 :=
  s_1211380.append (by norm_num) r_1211380
private theorem s_1211495 : RangeOk getRow 2051521 1211140 1211495 :=
  s_1211444.append (by norm_num) r_1211444
private theorem s_1211529 : RangeOk getRow 2051521 1211140 1211529 :=
  s_1211495.append (by norm_num) r_1211495
private theorem s_1211539 : RangeOk getRow 2051521 1211140 1211539 :=
  s_1211529.append (by norm_num) r_1211529
private theorem s_1211549 : RangeOk getRow 2051521 1211140 1211549 :=
  s_1211539.append (by norm_num) r_1211539
private theorem s_1211561 : RangeOk getRow 2051521 1211140 1211561 :=
  s_1211549.append (by norm_num) r_1211549
private theorem s_1211572 : RangeOk getRow 2051521 1211140 1211572 :=
  s_1211561.append (by norm_num) r_1211561
private theorem s_1211582 : RangeOk getRow 2051521 1211140 1211582 :=
  s_1211572.append (by norm_num) r_1211572
private theorem s_1211598 : RangeOk getRow 2051521 1211140 1211598 :=
  s_1211582.append (by norm_num) r_1211582
private theorem s_1211614 : RangeOk getRow 2051521 1211140 1211614 :=
  s_1211598.append (by norm_num) r_1211598
private theorem s_1211679 : RangeOk getRow 2051521 1211140 1211679 :=
  s_1211614.append (by norm_num) r_1211614
private theorem s_1211709 : RangeOk getRow 2051521 1211140 1211709 :=
  s_1211679.append (by norm_num) r_1211679
private theorem s_1211721 : RangeOk getRow 2051521 1211140 1211721 :=
  s_1211709.append (by norm_num) r_1211709
private theorem s_1211734 : RangeOk getRow 2051521 1211140 1211734 :=
  s_1211721.append (by norm_num) r_1211721
private theorem s_1211752 : RangeOk getRow 2051521 1211140 1211752 :=
  s_1211734.append (by norm_num) r_1211734
private theorem s_1211761 : RangeOk getRow 2051521 1211140 1211761 :=
  s_1211752.append (by norm_num) r_1211752
private theorem s_1211777 : RangeOk getRow 2051521 1211140 1211777 :=
  s_1211761.append (by norm_num) r_1211761
private theorem s_1211838 : RangeOk getRow 2051521 1211140 1211838 :=
  s_1211777.append (by norm_num) r_1211777
private theorem s_1211891 : RangeOk getRow 2051521 1211140 1211891 :=
  s_1211838.append (by norm_num) r_1211838
private theorem s_1211901 : RangeOk getRow 2051521 1211140 1211901 :=
  s_1211891.append (by norm_num) r_1211891
private theorem s_1211949 : RangeOk getRow 2051521 1211140 1211949 :=
  s_1211901.append (by norm_num) r_1211901
private theorem s_1211970 : RangeOk getRow 2051521 1211140 1211970 :=
  s_1211949.append (by norm_num) r_1211949
private theorem s_1212004 : RangeOk getRow 2051521 1211140 1212004 :=
  s_1211970.append (by norm_num) r_1211970
private theorem s_1212014 : RangeOk getRow 2051521 1211140 1212014 :=
  s_1212004.append (by norm_num) r_1212004
private theorem s_1212083 : RangeOk getRow 2051521 1211140 1212083 :=
  s_1212014.append (by norm_num) r_1212014
private theorem s_1212152 : RangeOk getRow 2051521 1211140 1212152 :=
  s_1212083.append (by norm_num) r_1212083
private theorem s_1212221 : RangeOk getRow 2051521 1211140 1212221 :=
  s_1212152.append (by norm_num) r_1212152
private theorem s_1212290 : RangeOk getRow 2051521 1211140 1212290 :=
  s_1212221.append (by norm_num) r_1212221
private theorem s_1212359 : RangeOk getRow 2051521 1211140 1212359 :=
  s_1212290.append (by norm_num) r_1212290
private theorem s_1212428 : RangeOk getRow 2051521 1211140 1212428 :=
  s_1212359.append (by norm_num) r_1212359
private theorem s_1212498 : RangeOk getRow 2051521 1211140 1212498 :=
  s_1212428.append (by norm_num) r_1212428
private theorem s_1212567 : RangeOk getRow 2051521 1211140 1212567 :=
  s_1212498.append (by norm_num) r_1212498
private theorem s_1212636 : RangeOk getRow 2051521 1211140 1212636 :=
  s_1212567.append (by norm_num) r_1212567
private theorem s_1212705 : RangeOk getRow 2051521 1211140 1212705 :=
  s_1212636.append (by norm_num) r_1212636
private theorem s_1212775 : RangeOk getRow 2051521 1211140 1212775 :=
  s_1212705.append (by norm_num) r_1212705
private theorem s_1212845 : RangeOk getRow 2051521 1211140 1212845 :=
  s_1212775.append (by norm_num) r_1212775
private theorem s_1212914 : RangeOk getRow 2051521 1211140 1212914 :=
  s_1212845.append (by norm_num) r_1212845
private theorem s_1212984 : RangeOk getRow 2051521 1211140 1212984 :=
  s_1212914.append (by norm_num) r_1212914
private theorem s_1213056 : RangeOk getRow 2051521 1211140 1213056 :=
  s_1212984.append (by norm_num) r_1212984
private theorem s_1213127 : RangeOk getRow 2051521 1211140 1213127 :=
  s_1213056.append (by norm_num) r_1213056

/-- Rows `[1211140, 1213127)` are valid. -/
theorem rangeOk_1211140_1213127 : RangeOk getRow 2051521 1211140 1213127 := s_1213127

end Noperthedron.Solution
