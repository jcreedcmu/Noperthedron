import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[310210, 312822). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_310210 : RangeOk getRow 2051521 310210 310272 := by
  decide +kernel

private theorem r_310272 : RangeOk getRow 2051521 310272 310341 := by
  decide +kernel

private theorem r_310341 : RangeOk getRow 2051521 310341 310414 := by
  decide +kernel

private theorem r_310414 : RangeOk getRow 2051521 310414 310483 := by
  decide +kernel

private theorem r_310483 : RangeOk getRow 2051521 310483 310554 := by
  decide +kernel

private theorem r_310554 : RangeOk getRow 2051521 310554 310626 := by
  decide +kernel

private theorem r_310626 : RangeOk getRow 2051521 310626 310696 := by
  decide +kernel

private theorem r_310696 : RangeOk getRow 2051521 310696 310762 := by
  decide +kernel

private theorem r_310762 : RangeOk getRow 2051521 310762 310826 := by
  decide +kernel

private theorem r_310826 : RangeOk getRow 2051521 310826 310894 := by
  decide +kernel

private theorem r_310894 : RangeOk getRow 2051521 310894 310963 := by
  decide +kernel

private theorem r_310963 : RangeOk getRow 2051521 310963 311035 := by
  decide +kernel

private theorem r_311035 : RangeOk getRow 2051521 311035 311104 := by
  decide +kernel

private theorem r_311104 : RangeOk getRow 2051521 311104 311174 := by
  decide +kernel

private theorem r_311174 : RangeOk getRow 2051521 311174 311245 := by
  decide +kernel

private theorem r_311245 : RangeOk getRow 2051521 311245 311316 := by
  decide +kernel

private theorem r_311316 : RangeOk getRow 2051521 311316 311384 := by
  decide +kernel

private theorem r_311384 : RangeOk getRow 2051521 311384 311452 := by
  decide +kernel

private theorem r_311452 : RangeOk getRow 2051521 311452 311521 := by
  decide +kernel

private theorem r_311521 : RangeOk getRow 2051521 311521 311592 := by
  decide +kernel

private theorem r_311592 : RangeOk getRow 2051521 311592 311662 := by
  decide +kernel

private theorem r_311662 : RangeOk getRow 2051521 311662 311732 := by
  decide +kernel

private theorem r_311732 : RangeOk getRow 2051521 311732 311802 := by
  decide +kernel

private theorem r_311802 : RangeOk getRow 2051521 311802 311873 := by
  decide +kernel

private theorem r_311873 : RangeOk getRow 2051521 311873 311940 := by
  decide +kernel

private theorem r_311940 : RangeOk getRow 2051521 311940 312008 := by
  decide +kernel

private theorem r_312008 : RangeOk getRow 2051521 312008 312075 := by
  decide +kernel

private theorem r_312075 : RangeOk getRow 2051521 312075 312143 := by
  decide +kernel

private theorem r_312143 : RangeOk getRow 2051521 312143 312211 := by
  decide +kernel

private theorem r_312211 : RangeOk getRow 2051521 312211 312280 := by
  decide +kernel

private theorem r_312280 : RangeOk getRow 2051521 312280 312349 := by
  decide +kernel

private theorem r_312349 : RangeOk getRow 2051521 312349 312417 := by
  decide +kernel

private theorem r_312417 : RangeOk getRow 2051521 312417 312484 := by
  decide +kernel

private theorem r_312484 : RangeOk getRow 2051521 312484 312552 := by
  decide +kernel

private theorem r_312552 : RangeOk getRow 2051521 312552 312621 := by
  decide +kernel

private theorem r_312621 : RangeOk getRow 2051521 312621 312687 := by
  decide +kernel

private theorem r_312687 : RangeOk getRow 2051521 312687 312755 := by
  decide +kernel

private theorem r_312755 : RangeOk getRow 2051521 312755 312822 := by
  decide +kernel

private theorem s_310272 : RangeOk getRow 2051521 310210 310272 := r_310210
private theorem s_310341 : RangeOk getRow 2051521 310210 310341 :=
  s_310272.append (by norm_num) r_310272
private theorem s_310414 : RangeOk getRow 2051521 310210 310414 :=
  s_310341.append (by norm_num) r_310341
private theorem s_310483 : RangeOk getRow 2051521 310210 310483 :=
  s_310414.append (by norm_num) r_310414
private theorem s_310554 : RangeOk getRow 2051521 310210 310554 :=
  s_310483.append (by norm_num) r_310483
private theorem s_310626 : RangeOk getRow 2051521 310210 310626 :=
  s_310554.append (by norm_num) r_310554
private theorem s_310696 : RangeOk getRow 2051521 310210 310696 :=
  s_310626.append (by norm_num) r_310626
private theorem s_310762 : RangeOk getRow 2051521 310210 310762 :=
  s_310696.append (by norm_num) r_310696
private theorem s_310826 : RangeOk getRow 2051521 310210 310826 :=
  s_310762.append (by norm_num) r_310762
private theorem s_310894 : RangeOk getRow 2051521 310210 310894 :=
  s_310826.append (by norm_num) r_310826
private theorem s_310963 : RangeOk getRow 2051521 310210 310963 :=
  s_310894.append (by norm_num) r_310894
private theorem s_311035 : RangeOk getRow 2051521 310210 311035 :=
  s_310963.append (by norm_num) r_310963
private theorem s_311104 : RangeOk getRow 2051521 310210 311104 :=
  s_311035.append (by norm_num) r_311035
private theorem s_311174 : RangeOk getRow 2051521 310210 311174 :=
  s_311104.append (by norm_num) r_311104
private theorem s_311245 : RangeOk getRow 2051521 310210 311245 :=
  s_311174.append (by norm_num) r_311174
private theorem s_311316 : RangeOk getRow 2051521 310210 311316 :=
  s_311245.append (by norm_num) r_311245
private theorem s_311384 : RangeOk getRow 2051521 310210 311384 :=
  s_311316.append (by norm_num) r_311316
private theorem s_311452 : RangeOk getRow 2051521 310210 311452 :=
  s_311384.append (by norm_num) r_311384
private theorem s_311521 : RangeOk getRow 2051521 310210 311521 :=
  s_311452.append (by norm_num) r_311452
private theorem s_311592 : RangeOk getRow 2051521 310210 311592 :=
  s_311521.append (by norm_num) r_311521
private theorem s_311662 : RangeOk getRow 2051521 310210 311662 :=
  s_311592.append (by norm_num) r_311592
private theorem s_311732 : RangeOk getRow 2051521 310210 311732 :=
  s_311662.append (by norm_num) r_311662
private theorem s_311802 : RangeOk getRow 2051521 310210 311802 :=
  s_311732.append (by norm_num) r_311732
private theorem s_311873 : RangeOk getRow 2051521 310210 311873 :=
  s_311802.append (by norm_num) r_311802
private theorem s_311940 : RangeOk getRow 2051521 310210 311940 :=
  s_311873.append (by norm_num) r_311873
private theorem s_312008 : RangeOk getRow 2051521 310210 312008 :=
  s_311940.append (by norm_num) r_311940
private theorem s_312075 : RangeOk getRow 2051521 310210 312075 :=
  s_312008.append (by norm_num) r_312008
private theorem s_312143 : RangeOk getRow 2051521 310210 312143 :=
  s_312075.append (by norm_num) r_312075
private theorem s_312211 : RangeOk getRow 2051521 310210 312211 :=
  s_312143.append (by norm_num) r_312143
private theorem s_312280 : RangeOk getRow 2051521 310210 312280 :=
  s_312211.append (by norm_num) r_312211
private theorem s_312349 : RangeOk getRow 2051521 310210 312349 :=
  s_312280.append (by norm_num) r_312280
private theorem s_312417 : RangeOk getRow 2051521 310210 312417 :=
  s_312349.append (by norm_num) r_312349
private theorem s_312484 : RangeOk getRow 2051521 310210 312484 :=
  s_312417.append (by norm_num) r_312417
private theorem s_312552 : RangeOk getRow 2051521 310210 312552 :=
  s_312484.append (by norm_num) r_312484
private theorem s_312621 : RangeOk getRow 2051521 310210 312621 :=
  s_312552.append (by norm_num) r_312552
private theorem s_312687 : RangeOk getRow 2051521 310210 312687 :=
  s_312621.append (by norm_num) r_312621
private theorem s_312755 : RangeOk getRow 2051521 310210 312755 :=
  s_312687.append (by norm_num) r_312687
private theorem s_312822 : RangeOk getRow 2051521 310210 312822 :=
  s_312755.append (by norm_num) r_312755

/-- Rows `[310210, 312822)` are valid. -/
theorem rangeOk_310210_312822 : RangeOk getRow 2051521 310210 312822 := s_312822

end Noperthedron.Solution
