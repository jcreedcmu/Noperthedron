import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[653845, 656376). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_653845 : RangeOk getRow 2051521 653845 653914 := by
  decide +kernel

private theorem r_653914 : RangeOk getRow 2051521 653914 653982 := by
  decide +kernel

private theorem r_653982 : RangeOk getRow 2051521 653982 654049 := by
  decide +kernel

private theorem r_654049 : RangeOk getRow 2051521 654049 654117 := by
  decide +kernel

private theorem r_654117 : RangeOk getRow 2051521 654117 654184 := by
  decide +kernel

private theorem r_654184 : RangeOk getRow 2051521 654184 654251 := by
  decide +kernel

private theorem r_654251 : RangeOk getRow 2051521 654251 654318 := by
  decide +kernel

private theorem r_654318 : RangeOk getRow 2051521 654318 654384 := by
  decide +kernel

private theorem r_654384 : RangeOk getRow 2051521 654384 654448 := by
  decide +kernel

private theorem r_654448 : RangeOk getRow 2051521 654448 654514 := by
  decide +kernel

private theorem r_654514 : RangeOk getRow 2051521 654514 654582 := by
  decide +kernel

private theorem r_654582 : RangeOk getRow 2051521 654582 654649 := by
  decide +kernel

private theorem r_654649 : RangeOk getRow 2051521 654649 654714 := by
  decide +kernel

private theorem r_654714 : RangeOk getRow 2051521 654714 654781 := by
  decide +kernel

private theorem r_654781 : RangeOk getRow 2051521 654781 654850 := by
  decide +kernel

private theorem r_654850 : RangeOk getRow 2051521 654850 654915 := by
  decide +kernel

private theorem r_654915 : RangeOk getRow 2051521 654915 654979 := by
  decide +kernel

private theorem r_654979 : RangeOk getRow 2051521 654979 655047 := by
  decide +kernel

private theorem r_655047 : RangeOk getRow 2051521 655047 655115 := by
  decide +kernel

private theorem r_655115 : RangeOk getRow 2051521 655115 655180 := by
  decide +kernel

private theorem r_655180 : RangeOk getRow 2051521 655180 655254 := by
  decide +kernel

private theorem r_655254 : RangeOk getRow 2051521 655254 655329 := by
  decide +kernel

private theorem r_655329 : RangeOk getRow 2051521 655329 655404 := by
  decide +kernel

private theorem r_655404 : RangeOk getRow 2051521 655404 655474 := by
  decide +kernel

private theorem r_655474 : RangeOk getRow 2051521 655474 655545 := by
  decide +kernel

private theorem r_655545 : RangeOk getRow 2051521 655545 655615 := by
  decide +kernel

private theorem r_655615 : RangeOk getRow 2051521 655615 655685 := by
  decide +kernel

private theorem r_655685 : RangeOk getRow 2051521 655685 655753 := by
  decide +kernel

private theorem r_655753 : RangeOk getRow 2051521 655753 655823 := by
  decide +kernel

private theorem r_655823 : RangeOk getRow 2051521 655823 655892 := by
  decide +kernel

private theorem r_655892 : RangeOk getRow 2051521 655892 655962 := by
  decide +kernel

private theorem r_655962 : RangeOk getRow 2051521 655962 656033 := by
  decide +kernel

private theorem r_656033 : RangeOk getRow 2051521 656033 656103 := by
  decide +kernel

private theorem r_656103 : RangeOk getRow 2051521 656103 656174 := by
  decide +kernel

private theorem r_656174 : RangeOk getRow 2051521 656174 656242 := by
  decide +kernel

private theorem r_656242 : RangeOk getRow 2051521 656242 656310 := by
  decide +kernel

private theorem r_656310 : RangeOk getRow 2051521 656310 656376 := by
  decide +kernel

private theorem s_653914 : RangeOk getRow 2051521 653845 653914 := r_653845
private theorem s_653982 : RangeOk getRow 2051521 653845 653982 :=
  s_653914.append (by norm_num) r_653914
private theorem s_654049 : RangeOk getRow 2051521 653845 654049 :=
  s_653982.append (by norm_num) r_653982
private theorem s_654117 : RangeOk getRow 2051521 653845 654117 :=
  s_654049.append (by norm_num) r_654049
private theorem s_654184 : RangeOk getRow 2051521 653845 654184 :=
  s_654117.append (by norm_num) r_654117
private theorem s_654251 : RangeOk getRow 2051521 653845 654251 :=
  s_654184.append (by norm_num) r_654184
private theorem s_654318 : RangeOk getRow 2051521 653845 654318 :=
  s_654251.append (by norm_num) r_654251
private theorem s_654384 : RangeOk getRow 2051521 653845 654384 :=
  s_654318.append (by norm_num) r_654318
private theorem s_654448 : RangeOk getRow 2051521 653845 654448 :=
  s_654384.append (by norm_num) r_654384
private theorem s_654514 : RangeOk getRow 2051521 653845 654514 :=
  s_654448.append (by norm_num) r_654448
private theorem s_654582 : RangeOk getRow 2051521 653845 654582 :=
  s_654514.append (by norm_num) r_654514
private theorem s_654649 : RangeOk getRow 2051521 653845 654649 :=
  s_654582.append (by norm_num) r_654582
private theorem s_654714 : RangeOk getRow 2051521 653845 654714 :=
  s_654649.append (by norm_num) r_654649
private theorem s_654781 : RangeOk getRow 2051521 653845 654781 :=
  s_654714.append (by norm_num) r_654714
private theorem s_654850 : RangeOk getRow 2051521 653845 654850 :=
  s_654781.append (by norm_num) r_654781
private theorem s_654915 : RangeOk getRow 2051521 653845 654915 :=
  s_654850.append (by norm_num) r_654850
private theorem s_654979 : RangeOk getRow 2051521 653845 654979 :=
  s_654915.append (by norm_num) r_654915
private theorem s_655047 : RangeOk getRow 2051521 653845 655047 :=
  s_654979.append (by norm_num) r_654979
private theorem s_655115 : RangeOk getRow 2051521 653845 655115 :=
  s_655047.append (by norm_num) r_655047
private theorem s_655180 : RangeOk getRow 2051521 653845 655180 :=
  s_655115.append (by norm_num) r_655115
private theorem s_655254 : RangeOk getRow 2051521 653845 655254 :=
  s_655180.append (by norm_num) r_655180
private theorem s_655329 : RangeOk getRow 2051521 653845 655329 :=
  s_655254.append (by norm_num) r_655254
private theorem s_655404 : RangeOk getRow 2051521 653845 655404 :=
  s_655329.append (by norm_num) r_655329
private theorem s_655474 : RangeOk getRow 2051521 653845 655474 :=
  s_655404.append (by norm_num) r_655404
private theorem s_655545 : RangeOk getRow 2051521 653845 655545 :=
  s_655474.append (by norm_num) r_655474
private theorem s_655615 : RangeOk getRow 2051521 653845 655615 :=
  s_655545.append (by norm_num) r_655545
private theorem s_655685 : RangeOk getRow 2051521 653845 655685 :=
  s_655615.append (by norm_num) r_655615
private theorem s_655753 : RangeOk getRow 2051521 653845 655753 :=
  s_655685.append (by norm_num) r_655685
private theorem s_655823 : RangeOk getRow 2051521 653845 655823 :=
  s_655753.append (by norm_num) r_655753
private theorem s_655892 : RangeOk getRow 2051521 653845 655892 :=
  s_655823.append (by norm_num) r_655823
private theorem s_655962 : RangeOk getRow 2051521 653845 655962 :=
  s_655892.append (by norm_num) r_655892
private theorem s_656033 : RangeOk getRow 2051521 653845 656033 :=
  s_655962.append (by norm_num) r_655962
private theorem s_656103 : RangeOk getRow 2051521 653845 656103 :=
  s_656033.append (by norm_num) r_656033
private theorem s_656174 : RangeOk getRow 2051521 653845 656174 :=
  s_656103.append (by norm_num) r_656103
private theorem s_656242 : RangeOk getRow 2051521 653845 656242 :=
  s_656174.append (by norm_num) r_656174
private theorem s_656310 : RangeOk getRow 2051521 653845 656310 :=
  s_656242.append (by norm_num) r_656242
private theorem s_656376 : RangeOk getRow 2051521 653845 656376 :=
  s_656310.append (by norm_num) r_656310

/-- Rows `[653845, 656376)` are valid. -/
theorem rangeOk_653845_656376 : RangeOk getRow 2051521 653845 656376 := s_656376

end Noperthedron.Solution
