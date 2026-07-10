import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[23893, 25618). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_23893 : RangeOk getRow 2051521 23893 23957 := by
  decide +kernel

private theorem r_23957 : RangeOk getRow 2051521 23957 24021 := by
  decide +kernel

private theorem r_24021 : RangeOk getRow 2051521 24021 24085 := by
  decide +kernel

private theorem r_24085 : RangeOk getRow 2051521 24085 24149 := by
  decide +kernel

private theorem r_24149 : RangeOk getRow 2051521 24149 24213 := by
  decide +kernel

private theorem r_24213 : RangeOk getRow 2051521 24213 24277 := by
  decide +kernel

private theorem r_24277 : RangeOk getRow 2051521 24277 24337 := by
  decide +kernel

private theorem r_24337 : RangeOk getRow 2051521 24337 24401 := by
  decide +kernel

private theorem r_24401 : RangeOk getRow 2051521 24401 24465 := by
  decide +kernel

private theorem r_24465 : RangeOk getRow 2051521 24465 24529 := by
  decide +kernel

private theorem r_24529 : RangeOk getRow 2051521 24529 24593 := by
  decide +kernel

private theorem r_24593 : RangeOk getRow 2051521 24593 24657 := by
  decide +kernel

private theorem r_24657 : RangeOk getRow 2051521 24657 24721 := by
  decide +kernel

private theorem r_24721 : RangeOk getRow 2051521 24721 24785 := by
  decide +kernel

private theorem r_24785 : RangeOk getRow 2051521 24785 24849 := by
  decide +kernel

private theorem r_24849 : RangeOk getRow 2051521 24849 24913 := by
  decide +kernel

private theorem r_24913 : RangeOk getRow 2051521 24913 24977 := by
  decide +kernel

private theorem r_24977 : RangeOk getRow 2051521 24977 25041 := by
  decide +kernel

private theorem r_25041 : RangeOk getRow 2051521 25041 25105 := by
  decide +kernel

private theorem r_25105 : RangeOk getRow 2051521 25105 25169 := by
  decide +kernel

private theorem r_25169 : RangeOk getRow 2051521 25169 25234 := by
  decide +kernel

private theorem r_25234 : RangeOk getRow 2051521 25234 25298 := by
  decide +kernel

private theorem r_25298 : RangeOk getRow 2051521 25298 25362 := by
  decide +kernel

private theorem r_25362 : RangeOk getRow 2051521 25362 25426 := by
  decide +kernel

private theorem r_25426 : RangeOk getRow 2051521 25426 25490 := by
  decide +kernel

private theorem r_25490 : RangeOk getRow 2051521 25490 25554 := by
  decide +kernel

private theorem r_25554 : RangeOk getRow 2051521 25554 25618 := by
  decide +kernel

private theorem s_23957 : RangeOk getRow 2051521 23893 23957 := r_23893
private theorem s_24021 : RangeOk getRow 2051521 23893 24021 :=
  s_23957.append (by norm_num) r_23957
private theorem s_24085 : RangeOk getRow 2051521 23893 24085 :=
  s_24021.append (by norm_num) r_24021
private theorem s_24149 : RangeOk getRow 2051521 23893 24149 :=
  s_24085.append (by norm_num) r_24085
private theorem s_24213 : RangeOk getRow 2051521 23893 24213 :=
  s_24149.append (by norm_num) r_24149
private theorem s_24277 : RangeOk getRow 2051521 23893 24277 :=
  s_24213.append (by norm_num) r_24213
private theorem s_24337 : RangeOk getRow 2051521 23893 24337 :=
  s_24277.append (by norm_num) r_24277
private theorem s_24401 : RangeOk getRow 2051521 23893 24401 :=
  s_24337.append (by norm_num) r_24337
private theorem s_24465 : RangeOk getRow 2051521 23893 24465 :=
  s_24401.append (by norm_num) r_24401
private theorem s_24529 : RangeOk getRow 2051521 23893 24529 :=
  s_24465.append (by norm_num) r_24465
private theorem s_24593 : RangeOk getRow 2051521 23893 24593 :=
  s_24529.append (by norm_num) r_24529
private theorem s_24657 : RangeOk getRow 2051521 23893 24657 :=
  s_24593.append (by norm_num) r_24593
private theorem s_24721 : RangeOk getRow 2051521 23893 24721 :=
  s_24657.append (by norm_num) r_24657
private theorem s_24785 : RangeOk getRow 2051521 23893 24785 :=
  s_24721.append (by norm_num) r_24721
private theorem s_24849 : RangeOk getRow 2051521 23893 24849 :=
  s_24785.append (by norm_num) r_24785
private theorem s_24913 : RangeOk getRow 2051521 23893 24913 :=
  s_24849.append (by norm_num) r_24849
private theorem s_24977 : RangeOk getRow 2051521 23893 24977 :=
  s_24913.append (by norm_num) r_24913
private theorem s_25041 : RangeOk getRow 2051521 23893 25041 :=
  s_24977.append (by norm_num) r_24977
private theorem s_25105 : RangeOk getRow 2051521 23893 25105 :=
  s_25041.append (by norm_num) r_25041
private theorem s_25169 : RangeOk getRow 2051521 23893 25169 :=
  s_25105.append (by norm_num) r_25105
private theorem s_25234 : RangeOk getRow 2051521 23893 25234 :=
  s_25169.append (by norm_num) r_25169
private theorem s_25298 : RangeOk getRow 2051521 23893 25298 :=
  s_25234.append (by norm_num) r_25234
private theorem s_25362 : RangeOk getRow 2051521 23893 25362 :=
  s_25298.append (by norm_num) r_25298
private theorem s_25426 : RangeOk getRow 2051521 23893 25426 :=
  s_25362.append (by norm_num) r_25362
private theorem s_25490 : RangeOk getRow 2051521 23893 25490 :=
  s_25426.append (by norm_num) r_25426
private theorem s_25554 : RangeOk getRow 2051521 23893 25554 :=
  s_25490.append (by norm_num) r_25490
private theorem s_25618 : RangeOk getRow 2051521 23893 25618 :=
  s_25554.append (by norm_num) r_25554

/-- Rows `[23893, 25618)` are valid. -/
theorem rangeOk_23893_25618 : RangeOk getRow 2051521 23893 25618 := s_25618

end Noperthedron.Solution
