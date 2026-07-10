import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[958464, 960761). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_958464 : RangeOk getRow 2051521 958464 958531 := by
  decide +kernel

private theorem r_958531 : RangeOk getRow 2051521 958531 958599 := by
  decide +kernel

private theorem r_958599 : RangeOk getRow 2051521 958599 958665 := by
  decide +kernel

private theorem r_958665 : RangeOk getRow 2051521 958665 958732 := by
  decide +kernel

private theorem r_958732 : RangeOk getRow 2051521 958732 958797 := by
  decide +kernel

private theorem r_958797 : RangeOk getRow 2051521 958797 958865 := by
  decide +kernel

private theorem r_958865 : RangeOk getRow 2051521 958865 958932 := by
  decide +kernel

private theorem r_958932 : RangeOk getRow 2051521 958932 959000 := by
  decide +kernel

private theorem r_959000 : RangeOk getRow 2051521 959000 959068 := by
  decide +kernel

private theorem r_959068 : RangeOk getRow 2051521 959068 959134 := by
  decide +kernel

private theorem r_959134 : RangeOk getRow 2051521 959134 959201 := by
  decide +kernel

private theorem r_959201 : RangeOk getRow 2051521 959201 959269 := by
  decide +kernel

private theorem r_959269 : RangeOk getRow 2051521 959269 959334 := by
  decide +kernel

private theorem r_959334 : RangeOk getRow 2051521 959334 959400 := by
  decide +kernel

private theorem r_959400 : RangeOk getRow 2051521 959400 959467 := by
  decide +kernel

private theorem r_959467 : RangeOk getRow 2051521 959467 959537 := by
  decide +kernel

private theorem r_959537 : RangeOk getRow 2051521 959537 959605 := by
  decide +kernel

private theorem r_959605 : RangeOk getRow 2051521 959605 959673 := by
  decide +kernel

private theorem r_959673 : RangeOk getRow 2051521 959673 959739 := by
  decide +kernel

private theorem r_959739 : RangeOk getRow 2051521 959739 959808 := by
  decide +kernel

private theorem r_959808 : RangeOk getRow 2051521 959808 959878 := by
  decide +kernel

private theorem r_959878 : RangeOk getRow 2051521 959878 959946 := by
  decide +kernel

private theorem r_959946 : RangeOk getRow 2051521 959946 960012 := by
  decide +kernel

private theorem r_960012 : RangeOk getRow 2051521 960012 960078 := by
  decide +kernel

private theorem r_960078 : RangeOk getRow 2051521 960078 960145 := by
  decide +kernel

private theorem r_960145 : RangeOk getRow 2051521 960145 960213 := by
  decide +kernel

private theorem r_960213 : RangeOk getRow 2051521 960213 960282 := by
  decide +kernel

private theorem r_960282 : RangeOk getRow 2051521 960282 960351 := by
  decide +kernel

private theorem r_960351 : RangeOk getRow 2051521 960351 960418 := by
  decide +kernel

private theorem r_960418 : RangeOk getRow 2051521 960418 960484 := by
  decide +kernel

private theorem r_960484 : RangeOk getRow 2051521 960484 960552 := by
  decide +kernel

private theorem r_960552 : RangeOk getRow 2051521 960552 960622 := by
  decide +kernel

private theorem r_960622 : RangeOk getRow 2051521 960622 960694 := by
  decide +kernel

private theorem r_960694 : RangeOk getRow 2051521 960694 960761 := by
  decide +kernel

private theorem s_958531 : RangeOk getRow 2051521 958464 958531 := r_958464
private theorem s_958599 : RangeOk getRow 2051521 958464 958599 :=
  s_958531.append (by norm_num) r_958531
private theorem s_958665 : RangeOk getRow 2051521 958464 958665 :=
  s_958599.append (by norm_num) r_958599
private theorem s_958732 : RangeOk getRow 2051521 958464 958732 :=
  s_958665.append (by norm_num) r_958665
private theorem s_958797 : RangeOk getRow 2051521 958464 958797 :=
  s_958732.append (by norm_num) r_958732
private theorem s_958865 : RangeOk getRow 2051521 958464 958865 :=
  s_958797.append (by norm_num) r_958797
private theorem s_958932 : RangeOk getRow 2051521 958464 958932 :=
  s_958865.append (by norm_num) r_958865
private theorem s_959000 : RangeOk getRow 2051521 958464 959000 :=
  s_958932.append (by norm_num) r_958932
private theorem s_959068 : RangeOk getRow 2051521 958464 959068 :=
  s_959000.append (by norm_num) r_959000
private theorem s_959134 : RangeOk getRow 2051521 958464 959134 :=
  s_959068.append (by norm_num) r_959068
private theorem s_959201 : RangeOk getRow 2051521 958464 959201 :=
  s_959134.append (by norm_num) r_959134
private theorem s_959269 : RangeOk getRow 2051521 958464 959269 :=
  s_959201.append (by norm_num) r_959201
private theorem s_959334 : RangeOk getRow 2051521 958464 959334 :=
  s_959269.append (by norm_num) r_959269
private theorem s_959400 : RangeOk getRow 2051521 958464 959400 :=
  s_959334.append (by norm_num) r_959334
private theorem s_959467 : RangeOk getRow 2051521 958464 959467 :=
  s_959400.append (by norm_num) r_959400
private theorem s_959537 : RangeOk getRow 2051521 958464 959537 :=
  s_959467.append (by norm_num) r_959467
private theorem s_959605 : RangeOk getRow 2051521 958464 959605 :=
  s_959537.append (by norm_num) r_959537
private theorem s_959673 : RangeOk getRow 2051521 958464 959673 :=
  s_959605.append (by norm_num) r_959605
private theorem s_959739 : RangeOk getRow 2051521 958464 959739 :=
  s_959673.append (by norm_num) r_959673
private theorem s_959808 : RangeOk getRow 2051521 958464 959808 :=
  s_959739.append (by norm_num) r_959739
private theorem s_959878 : RangeOk getRow 2051521 958464 959878 :=
  s_959808.append (by norm_num) r_959808
private theorem s_959946 : RangeOk getRow 2051521 958464 959946 :=
  s_959878.append (by norm_num) r_959878
private theorem s_960012 : RangeOk getRow 2051521 958464 960012 :=
  s_959946.append (by norm_num) r_959946
private theorem s_960078 : RangeOk getRow 2051521 958464 960078 :=
  s_960012.append (by norm_num) r_960012
private theorem s_960145 : RangeOk getRow 2051521 958464 960145 :=
  s_960078.append (by norm_num) r_960078
private theorem s_960213 : RangeOk getRow 2051521 958464 960213 :=
  s_960145.append (by norm_num) r_960145
private theorem s_960282 : RangeOk getRow 2051521 958464 960282 :=
  s_960213.append (by norm_num) r_960213
private theorem s_960351 : RangeOk getRow 2051521 958464 960351 :=
  s_960282.append (by norm_num) r_960282
private theorem s_960418 : RangeOk getRow 2051521 958464 960418 :=
  s_960351.append (by norm_num) r_960351
private theorem s_960484 : RangeOk getRow 2051521 958464 960484 :=
  s_960418.append (by norm_num) r_960418
private theorem s_960552 : RangeOk getRow 2051521 958464 960552 :=
  s_960484.append (by norm_num) r_960484
private theorem s_960622 : RangeOk getRow 2051521 958464 960622 :=
  s_960552.append (by norm_num) r_960552
private theorem s_960694 : RangeOk getRow 2051521 958464 960694 :=
  s_960622.append (by norm_num) r_960622
private theorem s_960761 : RangeOk getRow 2051521 958464 960761 :=
  s_960694.append (by norm_num) r_960694

/-- Rows `[958464, 960761)` are valid. -/
theorem rangeOk_958464_960761 : RangeOk getRow 2051521 958464 960761 := s_960761

end Noperthedron.Solution
