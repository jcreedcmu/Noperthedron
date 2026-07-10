import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[647128, 649256). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_647128 : RangeOk getRow 2051521 647128 647192 := by
  decide +kernel

private theorem r_647192 : RangeOk getRow 2051521 647192 647259 := by
  decide +kernel

private theorem r_647259 : RangeOk getRow 2051521 647259 647326 := by
  decide +kernel

private theorem r_647326 : RangeOk getRow 2051521 647326 647393 := by
  decide +kernel

private theorem r_647393 : RangeOk getRow 2051521 647393 647459 := by
  decide +kernel

private theorem r_647459 : RangeOk getRow 2051521 647459 647525 := by
  decide +kernel

private theorem r_647525 : RangeOk getRow 2051521 647525 647592 := by
  decide +kernel

private theorem r_647592 : RangeOk getRow 2051521 647592 647659 := by
  decide +kernel

private theorem r_647659 : RangeOk getRow 2051521 647659 647727 := by
  decide +kernel

private theorem r_647727 : RangeOk getRow 2051521 647727 647794 := by
  decide +kernel

private theorem r_647794 : RangeOk getRow 2051521 647794 647861 := by
  decide +kernel

private theorem r_647861 : RangeOk getRow 2051521 647861 647928 := by
  decide +kernel

private theorem r_647928 : RangeOk getRow 2051521 647928 647995 := by
  decide +kernel

private theorem r_647995 : RangeOk getRow 2051521 647995 648062 := by
  decide +kernel

private theorem r_648062 : RangeOk getRow 2051521 648062 648128 := by
  decide +kernel

private theorem r_648128 : RangeOk getRow 2051521 648128 648194 := by
  decide +kernel

private theorem r_648194 : RangeOk getRow 2051521 648194 648261 := by
  decide +kernel

private theorem r_648261 : RangeOk getRow 2051521 648261 648330 := by
  decide +kernel

private theorem r_648330 : RangeOk getRow 2051521 648330 648396 := by
  decide +kernel

private theorem r_648396 : RangeOk getRow 2051521 648396 648460 := by
  decide +kernel

private theorem r_648460 : RangeOk getRow 2051521 648460 648526 := by
  decide +kernel

private theorem r_648526 : RangeOk getRow 2051521 648526 648593 := by
  decide +kernel

private theorem r_648593 : RangeOk getRow 2051521 648593 648659 := by
  decide +kernel

private theorem r_648659 : RangeOk getRow 2051521 648659 648724 := by
  decide +kernel

private theorem r_648724 : RangeOk getRow 2051521 648724 648788 := by
  decide +kernel

private theorem r_648788 : RangeOk getRow 2051521 648788 648856 := by
  decide +kernel

private theorem r_648856 : RangeOk getRow 2051521 648856 648924 := by
  decide +kernel

private theorem r_648924 : RangeOk getRow 2051521 648924 648991 := by
  decide +kernel

private theorem r_648991 : RangeOk getRow 2051521 648991 649058 := by
  decide +kernel

private theorem r_649058 : RangeOk getRow 2051521 649058 649123 := by
  decide +kernel

private theorem r_649123 : RangeOk getRow 2051521 649123 649190 := by
  decide +kernel

private theorem r_649190 : RangeOk getRow 2051521 649190 649256 := by
  decide +kernel

private theorem s_647192 : RangeOk getRow 2051521 647128 647192 := r_647128
private theorem s_647259 : RangeOk getRow 2051521 647128 647259 :=
  s_647192.append (by norm_num) r_647192
private theorem s_647326 : RangeOk getRow 2051521 647128 647326 :=
  s_647259.append (by norm_num) r_647259
private theorem s_647393 : RangeOk getRow 2051521 647128 647393 :=
  s_647326.append (by norm_num) r_647326
private theorem s_647459 : RangeOk getRow 2051521 647128 647459 :=
  s_647393.append (by norm_num) r_647393
private theorem s_647525 : RangeOk getRow 2051521 647128 647525 :=
  s_647459.append (by norm_num) r_647459
private theorem s_647592 : RangeOk getRow 2051521 647128 647592 :=
  s_647525.append (by norm_num) r_647525
private theorem s_647659 : RangeOk getRow 2051521 647128 647659 :=
  s_647592.append (by norm_num) r_647592
private theorem s_647727 : RangeOk getRow 2051521 647128 647727 :=
  s_647659.append (by norm_num) r_647659
private theorem s_647794 : RangeOk getRow 2051521 647128 647794 :=
  s_647727.append (by norm_num) r_647727
private theorem s_647861 : RangeOk getRow 2051521 647128 647861 :=
  s_647794.append (by norm_num) r_647794
private theorem s_647928 : RangeOk getRow 2051521 647128 647928 :=
  s_647861.append (by norm_num) r_647861
private theorem s_647995 : RangeOk getRow 2051521 647128 647995 :=
  s_647928.append (by norm_num) r_647928
private theorem s_648062 : RangeOk getRow 2051521 647128 648062 :=
  s_647995.append (by norm_num) r_647995
private theorem s_648128 : RangeOk getRow 2051521 647128 648128 :=
  s_648062.append (by norm_num) r_648062
private theorem s_648194 : RangeOk getRow 2051521 647128 648194 :=
  s_648128.append (by norm_num) r_648128
private theorem s_648261 : RangeOk getRow 2051521 647128 648261 :=
  s_648194.append (by norm_num) r_648194
private theorem s_648330 : RangeOk getRow 2051521 647128 648330 :=
  s_648261.append (by norm_num) r_648261
private theorem s_648396 : RangeOk getRow 2051521 647128 648396 :=
  s_648330.append (by norm_num) r_648330
private theorem s_648460 : RangeOk getRow 2051521 647128 648460 :=
  s_648396.append (by norm_num) r_648396
private theorem s_648526 : RangeOk getRow 2051521 647128 648526 :=
  s_648460.append (by norm_num) r_648460
private theorem s_648593 : RangeOk getRow 2051521 647128 648593 :=
  s_648526.append (by norm_num) r_648526
private theorem s_648659 : RangeOk getRow 2051521 647128 648659 :=
  s_648593.append (by norm_num) r_648593
private theorem s_648724 : RangeOk getRow 2051521 647128 648724 :=
  s_648659.append (by norm_num) r_648659
private theorem s_648788 : RangeOk getRow 2051521 647128 648788 :=
  s_648724.append (by norm_num) r_648724
private theorem s_648856 : RangeOk getRow 2051521 647128 648856 :=
  s_648788.append (by norm_num) r_648788
private theorem s_648924 : RangeOk getRow 2051521 647128 648924 :=
  s_648856.append (by norm_num) r_648856
private theorem s_648991 : RangeOk getRow 2051521 647128 648991 :=
  s_648924.append (by norm_num) r_648924
private theorem s_649058 : RangeOk getRow 2051521 647128 649058 :=
  s_648991.append (by norm_num) r_648991
private theorem s_649123 : RangeOk getRow 2051521 647128 649123 :=
  s_649058.append (by norm_num) r_649058
private theorem s_649190 : RangeOk getRow 2051521 647128 649190 :=
  s_649123.append (by norm_num) r_649123
private theorem s_649256 : RangeOk getRow 2051521 647128 649256 :=
  s_649190.append (by norm_num) r_649190

/-- Rows `[647128, 649256)` are valid. -/
theorem rangeOk_647128_649256 : RangeOk getRow 2051521 647128 649256 := s_649256

end Noperthedron.Solution
