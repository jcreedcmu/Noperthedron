import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[32529, 34257). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_32529 : RangeOk getRow 2051521 32529 32593 := by
  decide +kernel

private theorem r_32593 : RangeOk getRow 2051521 32593 32657 := by
  decide +kernel

private theorem r_32657 : RangeOk getRow 2051521 32657 32721 := by
  decide +kernel

private theorem r_32721 : RangeOk getRow 2051521 32721 32785 := by
  decide +kernel

private theorem r_32785 : RangeOk getRow 2051521 32785 32849 := by
  decide +kernel

private theorem r_32849 : RangeOk getRow 2051521 32849 32913 := by
  decide +kernel

private theorem r_32913 : RangeOk getRow 2051521 32913 32977 := by
  decide +kernel

private theorem r_32977 : RangeOk getRow 2051521 32977 33041 := by
  decide +kernel

private theorem r_33041 : RangeOk getRow 2051521 33041 33105 := by
  decide +kernel

private theorem r_33105 : RangeOk getRow 2051521 33105 33169 := by
  decide +kernel

private theorem r_33169 : RangeOk getRow 2051521 33169 33233 := by
  decide +kernel

private theorem r_33233 : RangeOk getRow 2051521 33233 33297 := by
  decide +kernel

private theorem r_33297 : RangeOk getRow 2051521 33297 33361 := by
  decide +kernel

private theorem r_33361 : RangeOk getRow 2051521 33361 33425 := by
  decide +kernel

private theorem r_33425 : RangeOk getRow 2051521 33425 33489 := by
  decide +kernel

private theorem r_33489 : RangeOk getRow 2051521 33489 33553 := by
  decide +kernel

private theorem r_33553 : RangeOk getRow 2051521 33553 33617 := by
  decide +kernel

private theorem r_33617 : RangeOk getRow 2051521 33617 33681 := by
  decide +kernel

private theorem r_33681 : RangeOk getRow 2051521 33681 33745 := by
  decide +kernel

private theorem r_33745 : RangeOk getRow 2051521 33745 33809 := by
  decide +kernel

private theorem r_33809 : RangeOk getRow 2051521 33809 33873 := by
  decide +kernel

private theorem r_33873 : RangeOk getRow 2051521 33873 33937 := by
  decide +kernel

private theorem r_33937 : RangeOk getRow 2051521 33937 34001 := by
  decide +kernel

private theorem r_34001 : RangeOk getRow 2051521 34001 34065 := by
  decide +kernel

private theorem r_34065 : RangeOk getRow 2051521 34065 34129 := by
  decide +kernel

private theorem r_34129 : RangeOk getRow 2051521 34129 34193 := by
  decide +kernel

private theorem r_34193 : RangeOk getRow 2051521 34193 34257 := by
  decide +kernel

private theorem s_32593 : RangeOk getRow 2051521 32529 32593 := r_32529
private theorem s_32657 : RangeOk getRow 2051521 32529 32657 :=
  s_32593.append (by norm_num) r_32593
private theorem s_32721 : RangeOk getRow 2051521 32529 32721 :=
  s_32657.append (by norm_num) r_32657
private theorem s_32785 : RangeOk getRow 2051521 32529 32785 :=
  s_32721.append (by norm_num) r_32721
private theorem s_32849 : RangeOk getRow 2051521 32529 32849 :=
  s_32785.append (by norm_num) r_32785
private theorem s_32913 : RangeOk getRow 2051521 32529 32913 :=
  s_32849.append (by norm_num) r_32849
private theorem s_32977 : RangeOk getRow 2051521 32529 32977 :=
  s_32913.append (by norm_num) r_32913
private theorem s_33041 : RangeOk getRow 2051521 32529 33041 :=
  s_32977.append (by norm_num) r_32977
private theorem s_33105 : RangeOk getRow 2051521 32529 33105 :=
  s_33041.append (by norm_num) r_33041
private theorem s_33169 : RangeOk getRow 2051521 32529 33169 :=
  s_33105.append (by norm_num) r_33105
private theorem s_33233 : RangeOk getRow 2051521 32529 33233 :=
  s_33169.append (by norm_num) r_33169
private theorem s_33297 : RangeOk getRow 2051521 32529 33297 :=
  s_33233.append (by norm_num) r_33233
private theorem s_33361 : RangeOk getRow 2051521 32529 33361 :=
  s_33297.append (by norm_num) r_33297
private theorem s_33425 : RangeOk getRow 2051521 32529 33425 :=
  s_33361.append (by norm_num) r_33361
private theorem s_33489 : RangeOk getRow 2051521 32529 33489 :=
  s_33425.append (by norm_num) r_33425
private theorem s_33553 : RangeOk getRow 2051521 32529 33553 :=
  s_33489.append (by norm_num) r_33489
private theorem s_33617 : RangeOk getRow 2051521 32529 33617 :=
  s_33553.append (by norm_num) r_33553
private theorem s_33681 : RangeOk getRow 2051521 32529 33681 :=
  s_33617.append (by norm_num) r_33617
private theorem s_33745 : RangeOk getRow 2051521 32529 33745 :=
  s_33681.append (by norm_num) r_33681
private theorem s_33809 : RangeOk getRow 2051521 32529 33809 :=
  s_33745.append (by norm_num) r_33745
private theorem s_33873 : RangeOk getRow 2051521 32529 33873 :=
  s_33809.append (by norm_num) r_33809
private theorem s_33937 : RangeOk getRow 2051521 32529 33937 :=
  s_33873.append (by norm_num) r_33873
private theorem s_34001 : RangeOk getRow 2051521 32529 34001 :=
  s_33937.append (by norm_num) r_33937
private theorem s_34065 : RangeOk getRow 2051521 32529 34065 :=
  s_34001.append (by norm_num) r_34001
private theorem s_34129 : RangeOk getRow 2051521 32529 34129 :=
  s_34065.append (by norm_num) r_34065
private theorem s_34193 : RangeOk getRow 2051521 32529 34193 :=
  s_34129.append (by norm_num) r_34129
private theorem s_34257 : RangeOk getRow 2051521 32529 34257 :=
  s_34193.append (by norm_num) r_34193

/-- Rows `[32529, 34257)` are valid. -/
theorem rangeOk_32529_34257 : RangeOk getRow 2051521 32529 34257 := s_34257

end Noperthedron.Solution
