import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[189715, 191443). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_189715 : RangeOk getRow 2051521 189715 189779 := by
  decide +kernel

private theorem r_189779 : RangeOk getRow 2051521 189779 189843 := by
  decide +kernel

private theorem r_189843 : RangeOk getRow 2051521 189843 189907 := by
  decide +kernel

private theorem r_189907 : RangeOk getRow 2051521 189907 189971 := by
  decide +kernel

private theorem r_189971 : RangeOk getRow 2051521 189971 190035 := by
  decide +kernel

private theorem r_190035 : RangeOk getRow 2051521 190035 190099 := by
  decide +kernel

private theorem r_190099 : RangeOk getRow 2051521 190099 190163 := by
  decide +kernel

private theorem r_190163 : RangeOk getRow 2051521 190163 190227 := by
  decide +kernel

private theorem r_190227 : RangeOk getRow 2051521 190227 190291 := by
  decide +kernel

private theorem r_190291 : RangeOk getRow 2051521 190291 190355 := by
  decide +kernel

private theorem r_190355 : RangeOk getRow 2051521 190355 190419 := by
  decide +kernel

private theorem r_190419 : RangeOk getRow 2051521 190419 190483 := by
  decide +kernel

private theorem r_190483 : RangeOk getRow 2051521 190483 190547 := by
  decide +kernel

private theorem r_190547 : RangeOk getRow 2051521 190547 190611 := by
  decide +kernel

private theorem r_190611 : RangeOk getRow 2051521 190611 190675 := by
  decide +kernel

private theorem r_190675 : RangeOk getRow 2051521 190675 190739 := by
  decide +kernel

private theorem r_190739 : RangeOk getRow 2051521 190739 190803 := by
  decide +kernel

private theorem r_190803 : RangeOk getRow 2051521 190803 190867 := by
  decide +kernel

private theorem r_190867 : RangeOk getRow 2051521 190867 190931 := by
  decide +kernel

private theorem r_190931 : RangeOk getRow 2051521 190931 190995 := by
  decide +kernel

private theorem r_190995 : RangeOk getRow 2051521 190995 191059 := by
  decide +kernel

private theorem r_191059 : RangeOk getRow 2051521 191059 191123 := by
  decide +kernel

private theorem r_191123 : RangeOk getRow 2051521 191123 191187 := by
  decide +kernel

private theorem r_191187 : RangeOk getRow 2051521 191187 191251 := by
  decide +kernel

private theorem r_191251 : RangeOk getRow 2051521 191251 191315 := by
  decide +kernel

private theorem r_191315 : RangeOk getRow 2051521 191315 191379 := by
  decide +kernel

private theorem r_191379 : RangeOk getRow 2051521 191379 191443 := by
  decide +kernel

private theorem s_189779 : RangeOk getRow 2051521 189715 189779 := r_189715
private theorem s_189843 : RangeOk getRow 2051521 189715 189843 :=
  s_189779.append (by norm_num) r_189779
private theorem s_189907 : RangeOk getRow 2051521 189715 189907 :=
  s_189843.append (by norm_num) r_189843
private theorem s_189971 : RangeOk getRow 2051521 189715 189971 :=
  s_189907.append (by norm_num) r_189907
private theorem s_190035 : RangeOk getRow 2051521 189715 190035 :=
  s_189971.append (by norm_num) r_189971
private theorem s_190099 : RangeOk getRow 2051521 189715 190099 :=
  s_190035.append (by norm_num) r_190035
private theorem s_190163 : RangeOk getRow 2051521 189715 190163 :=
  s_190099.append (by norm_num) r_190099
private theorem s_190227 : RangeOk getRow 2051521 189715 190227 :=
  s_190163.append (by norm_num) r_190163
private theorem s_190291 : RangeOk getRow 2051521 189715 190291 :=
  s_190227.append (by norm_num) r_190227
private theorem s_190355 : RangeOk getRow 2051521 189715 190355 :=
  s_190291.append (by norm_num) r_190291
private theorem s_190419 : RangeOk getRow 2051521 189715 190419 :=
  s_190355.append (by norm_num) r_190355
private theorem s_190483 : RangeOk getRow 2051521 189715 190483 :=
  s_190419.append (by norm_num) r_190419
private theorem s_190547 : RangeOk getRow 2051521 189715 190547 :=
  s_190483.append (by norm_num) r_190483
private theorem s_190611 : RangeOk getRow 2051521 189715 190611 :=
  s_190547.append (by norm_num) r_190547
private theorem s_190675 : RangeOk getRow 2051521 189715 190675 :=
  s_190611.append (by norm_num) r_190611
private theorem s_190739 : RangeOk getRow 2051521 189715 190739 :=
  s_190675.append (by norm_num) r_190675
private theorem s_190803 : RangeOk getRow 2051521 189715 190803 :=
  s_190739.append (by norm_num) r_190739
private theorem s_190867 : RangeOk getRow 2051521 189715 190867 :=
  s_190803.append (by norm_num) r_190803
private theorem s_190931 : RangeOk getRow 2051521 189715 190931 :=
  s_190867.append (by norm_num) r_190867
private theorem s_190995 : RangeOk getRow 2051521 189715 190995 :=
  s_190931.append (by norm_num) r_190931
private theorem s_191059 : RangeOk getRow 2051521 189715 191059 :=
  s_190995.append (by norm_num) r_190995
private theorem s_191123 : RangeOk getRow 2051521 189715 191123 :=
  s_191059.append (by norm_num) r_191059
private theorem s_191187 : RangeOk getRow 2051521 189715 191187 :=
  s_191123.append (by norm_num) r_191123
private theorem s_191251 : RangeOk getRow 2051521 189715 191251 :=
  s_191187.append (by norm_num) r_191187
private theorem s_191315 : RangeOk getRow 2051521 189715 191315 :=
  s_191251.append (by norm_num) r_191251
private theorem s_191379 : RangeOk getRow 2051521 189715 191379 :=
  s_191315.append (by norm_num) r_191315
private theorem s_191443 : RangeOk getRow 2051521 189715 191443 :=
  s_191379.append (by norm_num) r_191379

/-- Rows `[189715, 191443)` are valid. -/
theorem rangeOk_189715_191443 : RangeOk getRow 2051521 189715 191443 := s_191443

end Noperthedron.Solution
