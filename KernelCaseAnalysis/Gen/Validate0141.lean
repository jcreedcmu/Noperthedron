import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[330513, 333127). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_330513 : RangeOk getRow 2051521 330513 330582 := by
  decide +kernel

private theorem r_330582 : RangeOk getRow 2051521 330582 330653 := by
  decide +kernel

private theorem r_330653 : RangeOk getRow 2051521 330653 330723 := by
  decide +kernel

private theorem r_330723 : RangeOk getRow 2051521 330723 330789 := by
  decide +kernel

private theorem r_330789 : RangeOk getRow 2051521 330789 330857 := by
  decide +kernel

private theorem r_330857 : RangeOk getRow 2051521 330857 330926 := by
  decide +kernel

private theorem r_330926 : RangeOk getRow 2051521 330926 330993 := by
  decide +kernel

private theorem r_330993 : RangeOk getRow 2051521 330993 331061 := by
  decide +kernel

private theorem r_331061 : RangeOk getRow 2051521 331061 331131 := by
  decide +kernel

private theorem r_331131 : RangeOk getRow 2051521 331131 331200 := by
  decide +kernel

private theorem r_331200 : RangeOk getRow 2051521 331200 331265 := by
  decide +kernel

private theorem r_331265 : RangeOk getRow 2051521 331265 331333 := by
  decide +kernel

private theorem r_331333 : RangeOk getRow 2051521 331333 331401 := by
  decide +kernel

private theorem r_331401 : RangeOk getRow 2051521 331401 331468 := by
  decide +kernel

private theorem r_331468 : RangeOk getRow 2051521 331468 331536 := by
  decide +kernel

private theorem r_331536 : RangeOk getRow 2051521 331536 331606 := by
  decide +kernel

private theorem r_331606 : RangeOk getRow 2051521 331606 331672 := by
  decide +kernel

private theorem r_331672 : RangeOk getRow 2051521 331672 331738 := by
  decide +kernel

private theorem r_331738 : RangeOk getRow 2051521 331738 331804 := by
  decide +kernel

private theorem r_331804 : RangeOk getRow 2051521 331804 331876 := by
  decide +kernel

private theorem r_331876 : RangeOk getRow 2051521 331876 331946 := by
  decide +kernel

private theorem r_331946 : RangeOk getRow 2051521 331946 332016 := by
  decide +kernel

private theorem r_332016 : RangeOk getRow 2051521 332016 332088 := by
  decide +kernel

private theorem r_332088 : RangeOk getRow 2051521 332088 332160 := by
  decide +kernel

private theorem r_332160 : RangeOk getRow 2051521 332160 332226 := by
  decide +kernel

private theorem r_332226 : RangeOk getRow 2051521 332226 332289 := by
  decide +kernel

private theorem r_332289 : RangeOk getRow 2051521 332289 332357 := by
  decide +kernel

private theorem r_332357 : RangeOk getRow 2051521 332357 332428 := by
  decide +kernel

private theorem r_332428 : RangeOk getRow 2051521 332428 332500 := by
  decide +kernel

private theorem r_332500 : RangeOk getRow 2051521 332500 332570 := by
  decide +kernel

private theorem r_332570 : RangeOk getRow 2051521 332570 332642 := by
  decide +kernel

private theorem r_332642 : RangeOk getRow 2051521 332642 332715 := by
  decide +kernel

private theorem r_332715 : RangeOk getRow 2051521 332715 332783 := by
  decide +kernel

private theorem r_332783 : RangeOk getRow 2051521 332783 332850 := by
  decide +kernel

private theorem r_332850 : RangeOk getRow 2051521 332850 332917 := by
  decide +kernel

private theorem r_332917 : RangeOk getRow 2051521 332917 332985 := by
  decide +kernel

private theorem r_332985 : RangeOk getRow 2051521 332985 333055 := by
  decide +kernel

private theorem r_333055 : RangeOk getRow 2051521 333055 333127 := by
  decide +kernel

private theorem s_330582 : RangeOk getRow 2051521 330513 330582 := r_330513
private theorem s_330653 : RangeOk getRow 2051521 330513 330653 :=
  s_330582.append (by norm_num) r_330582
private theorem s_330723 : RangeOk getRow 2051521 330513 330723 :=
  s_330653.append (by norm_num) r_330653
private theorem s_330789 : RangeOk getRow 2051521 330513 330789 :=
  s_330723.append (by norm_num) r_330723
private theorem s_330857 : RangeOk getRow 2051521 330513 330857 :=
  s_330789.append (by norm_num) r_330789
private theorem s_330926 : RangeOk getRow 2051521 330513 330926 :=
  s_330857.append (by norm_num) r_330857
private theorem s_330993 : RangeOk getRow 2051521 330513 330993 :=
  s_330926.append (by norm_num) r_330926
private theorem s_331061 : RangeOk getRow 2051521 330513 331061 :=
  s_330993.append (by norm_num) r_330993
private theorem s_331131 : RangeOk getRow 2051521 330513 331131 :=
  s_331061.append (by norm_num) r_331061
private theorem s_331200 : RangeOk getRow 2051521 330513 331200 :=
  s_331131.append (by norm_num) r_331131
private theorem s_331265 : RangeOk getRow 2051521 330513 331265 :=
  s_331200.append (by norm_num) r_331200
private theorem s_331333 : RangeOk getRow 2051521 330513 331333 :=
  s_331265.append (by norm_num) r_331265
private theorem s_331401 : RangeOk getRow 2051521 330513 331401 :=
  s_331333.append (by norm_num) r_331333
private theorem s_331468 : RangeOk getRow 2051521 330513 331468 :=
  s_331401.append (by norm_num) r_331401
private theorem s_331536 : RangeOk getRow 2051521 330513 331536 :=
  s_331468.append (by norm_num) r_331468
private theorem s_331606 : RangeOk getRow 2051521 330513 331606 :=
  s_331536.append (by norm_num) r_331536
private theorem s_331672 : RangeOk getRow 2051521 330513 331672 :=
  s_331606.append (by norm_num) r_331606
private theorem s_331738 : RangeOk getRow 2051521 330513 331738 :=
  s_331672.append (by norm_num) r_331672
private theorem s_331804 : RangeOk getRow 2051521 330513 331804 :=
  s_331738.append (by norm_num) r_331738
private theorem s_331876 : RangeOk getRow 2051521 330513 331876 :=
  s_331804.append (by norm_num) r_331804
private theorem s_331946 : RangeOk getRow 2051521 330513 331946 :=
  s_331876.append (by norm_num) r_331876
private theorem s_332016 : RangeOk getRow 2051521 330513 332016 :=
  s_331946.append (by norm_num) r_331946
private theorem s_332088 : RangeOk getRow 2051521 330513 332088 :=
  s_332016.append (by norm_num) r_332016
private theorem s_332160 : RangeOk getRow 2051521 330513 332160 :=
  s_332088.append (by norm_num) r_332088
private theorem s_332226 : RangeOk getRow 2051521 330513 332226 :=
  s_332160.append (by norm_num) r_332160
private theorem s_332289 : RangeOk getRow 2051521 330513 332289 :=
  s_332226.append (by norm_num) r_332226
private theorem s_332357 : RangeOk getRow 2051521 330513 332357 :=
  s_332289.append (by norm_num) r_332289
private theorem s_332428 : RangeOk getRow 2051521 330513 332428 :=
  s_332357.append (by norm_num) r_332357
private theorem s_332500 : RangeOk getRow 2051521 330513 332500 :=
  s_332428.append (by norm_num) r_332428
private theorem s_332570 : RangeOk getRow 2051521 330513 332570 :=
  s_332500.append (by norm_num) r_332500
private theorem s_332642 : RangeOk getRow 2051521 330513 332642 :=
  s_332570.append (by norm_num) r_332570
private theorem s_332715 : RangeOk getRow 2051521 330513 332715 :=
  s_332642.append (by norm_num) r_332642
private theorem s_332783 : RangeOk getRow 2051521 330513 332783 :=
  s_332715.append (by norm_num) r_332715
private theorem s_332850 : RangeOk getRow 2051521 330513 332850 :=
  s_332783.append (by norm_num) r_332783
private theorem s_332917 : RangeOk getRow 2051521 330513 332917 :=
  s_332850.append (by norm_num) r_332850
private theorem s_332985 : RangeOk getRow 2051521 330513 332985 :=
  s_332917.append (by norm_num) r_332917
private theorem s_333055 : RangeOk getRow 2051521 330513 333055 :=
  s_332985.append (by norm_num) r_332985
private theorem s_333127 : RangeOk getRow 2051521 330513 333127 :=
  s_333055.append (by norm_num) r_333055

/-- Rows `[330513, 333127)` are valid. -/
theorem rangeOk_330513_333127 : RangeOk getRow 2051521 330513 333127 := s_333127

end Noperthedron.Solution
