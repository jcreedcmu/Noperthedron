import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[184521, 186255). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_184521 : RangeOk getRow 2051521 184521 184585 := by
  decide +kernel

private theorem r_184585 : RangeOk getRow 2051521 184585 184649 := by
  decide +kernel

private theorem r_184649 : RangeOk getRow 2051521 184649 184713 := by
  decide +kernel

private theorem r_184713 : RangeOk getRow 2051521 184713 184777 := by
  decide +kernel

private theorem r_184777 : RangeOk getRow 2051521 184777 184841 := by
  decide +kernel

private theorem r_184841 : RangeOk getRow 2051521 184841 184905 := by
  decide +kernel

private theorem r_184905 : RangeOk getRow 2051521 184905 184971 := by
  decide +kernel

private theorem r_184971 : RangeOk getRow 2051521 184971 185035 := by
  decide +kernel

private theorem r_185035 : RangeOk getRow 2051521 185035 185099 := by
  decide +kernel

private theorem r_185099 : RangeOk getRow 2051521 185099 185163 := by
  decide +kernel

private theorem r_185163 : RangeOk getRow 2051521 185163 185227 := by
  decide +kernel

private theorem r_185227 : RangeOk getRow 2051521 185227 185291 := by
  decide +kernel

private theorem r_185291 : RangeOk getRow 2051521 185291 185355 := by
  decide +kernel

private theorem r_185355 : RangeOk getRow 2051521 185355 185421 := by
  decide +kernel

private theorem r_185421 : RangeOk getRow 2051521 185421 185485 := by
  decide +kernel

private theorem r_185485 : RangeOk getRow 2051521 185485 185549 := by
  decide +kernel

private theorem r_185549 : RangeOk getRow 2051521 185549 185613 := by
  decide +kernel

private theorem r_185613 : RangeOk getRow 2051521 185613 185677 := by
  decide +kernel

private theorem r_185677 : RangeOk getRow 2051521 185677 185741 := by
  decide +kernel

private theorem r_185741 : RangeOk getRow 2051521 185741 185805 := by
  decide +kernel

private theorem r_185805 : RangeOk getRow 2051521 185805 185871 := by
  decide +kernel

private theorem r_185871 : RangeOk getRow 2051521 185871 185935 := by
  decide +kernel

private theorem r_185935 : RangeOk getRow 2051521 185935 185999 := by
  decide +kernel

private theorem r_185999 : RangeOk getRow 2051521 185999 186063 := by
  decide +kernel

private theorem r_186063 : RangeOk getRow 2051521 186063 186127 := by
  decide +kernel

private theorem r_186127 : RangeOk getRow 2051521 186127 186191 := by
  decide +kernel

private theorem r_186191 : RangeOk getRow 2051521 186191 186255 := by
  decide +kernel

private theorem s_184585 : RangeOk getRow 2051521 184521 184585 := r_184521
private theorem s_184649 : RangeOk getRow 2051521 184521 184649 :=
  s_184585.append (by norm_num) r_184585
private theorem s_184713 : RangeOk getRow 2051521 184521 184713 :=
  s_184649.append (by norm_num) r_184649
private theorem s_184777 : RangeOk getRow 2051521 184521 184777 :=
  s_184713.append (by norm_num) r_184713
private theorem s_184841 : RangeOk getRow 2051521 184521 184841 :=
  s_184777.append (by norm_num) r_184777
private theorem s_184905 : RangeOk getRow 2051521 184521 184905 :=
  s_184841.append (by norm_num) r_184841
private theorem s_184971 : RangeOk getRow 2051521 184521 184971 :=
  s_184905.append (by norm_num) r_184905
private theorem s_185035 : RangeOk getRow 2051521 184521 185035 :=
  s_184971.append (by norm_num) r_184971
private theorem s_185099 : RangeOk getRow 2051521 184521 185099 :=
  s_185035.append (by norm_num) r_185035
private theorem s_185163 : RangeOk getRow 2051521 184521 185163 :=
  s_185099.append (by norm_num) r_185099
private theorem s_185227 : RangeOk getRow 2051521 184521 185227 :=
  s_185163.append (by norm_num) r_185163
private theorem s_185291 : RangeOk getRow 2051521 184521 185291 :=
  s_185227.append (by norm_num) r_185227
private theorem s_185355 : RangeOk getRow 2051521 184521 185355 :=
  s_185291.append (by norm_num) r_185291
private theorem s_185421 : RangeOk getRow 2051521 184521 185421 :=
  s_185355.append (by norm_num) r_185355
private theorem s_185485 : RangeOk getRow 2051521 184521 185485 :=
  s_185421.append (by norm_num) r_185421
private theorem s_185549 : RangeOk getRow 2051521 184521 185549 :=
  s_185485.append (by norm_num) r_185485
private theorem s_185613 : RangeOk getRow 2051521 184521 185613 :=
  s_185549.append (by norm_num) r_185549
private theorem s_185677 : RangeOk getRow 2051521 184521 185677 :=
  s_185613.append (by norm_num) r_185613
private theorem s_185741 : RangeOk getRow 2051521 184521 185741 :=
  s_185677.append (by norm_num) r_185677
private theorem s_185805 : RangeOk getRow 2051521 184521 185805 :=
  s_185741.append (by norm_num) r_185741
private theorem s_185871 : RangeOk getRow 2051521 184521 185871 :=
  s_185805.append (by norm_num) r_185805
private theorem s_185935 : RangeOk getRow 2051521 184521 185935 :=
  s_185871.append (by norm_num) r_185871
private theorem s_185999 : RangeOk getRow 2051521 184521 185999 :=
  s_185935.append (by norm_num) r_185935
private theorem s_186063 : RangeOk getRow 2051521 184521 186063 :=
  s_185999.append (by norm_num) r_185999
private theorem s_186127 : RangeOk getRow 2051521 184521 186127 :=
  s_186063.append (by norm_num) r_186063
private theorem s_186191 : RangeOk getRow 2051521 184521 186191 :=
  s_186127.append (by norm_num) r_186127
private theorem s_186255 : RangeOk getRow 2051521 184521 186255 :=
  s_186191.append (by norm_num) r_186191

/-- Rows `[184521, 186255)` are valid. -/
theorem rangeOk_184521_186255 : RangeOk getRow 2051521 184521 186255 := s_186255

end Noperthedron.Solution
