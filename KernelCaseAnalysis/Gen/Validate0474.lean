import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1170412, 1172870). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1170412 : RangeOk getRow 2051521 1170412 1170483 := by
  decide +kernel

private theorem r_1170483 : RangeOk getRow 2051521 1170483 1170556 := by
  decide +kernel

private theorem r_1170556 : RangeOk getRow 2051521 1170556 1170628 := by
  decide +kernel

private theorem r_1170628 : RangeOk getRow 2051521 1170628 1170697 := by
  decide +kernel

private theorem r_1170697 : RangeOk getRow 2051521 1170697 1170767 := by
  decide +kernel

private theorem r_1170767 : RangeOk getRow 2051521 1170767 1170836 := by
  decide +kernel

private theorem r_1170836 : RangeOk getRow 2051521 1170836 1170908 := by
  decide +kernel

private theorem r_1170908 : RangeOk getRow 2051521 1170908 1170979 := by
  decide +kernel

private theorem r_1170979 : RangeOk getRow 2051521 1170979 1171048 := by
  decide +kernel

private theorem r_1171048 : RangeOk getRow 2051521 1171048 1171115 := by
  decide +kernel

private theorem r_1171115 : RangeOk getRow 2051521 1171115 1171184 := by
  decide +kernel

private theorem r_1171184 : RangeOk getRow 2051521 1171184 1171251 := by
  decide +kernel

private theorem r_1171251 : RangeOk getRow 2051521 1171251 1171318 := by
  decide +kernel

private theorem r_1171318 : RangeOk getRow 2051521 1171318 1171385 := by
  decide +kernel

private theorem r_1171385 : RangeOk getRow 2051521 1171385 1171453 := by
  decide +kernel

private theorem r_1171453 : RangeOk getRow 2051521 1171453 1171520 := by
  decide +kernel

private theorem r_1171520 : RangeOk getRow 2051521 1171520 1171587 := by
  decide +kernel

private theorem r_1171587 : RangeOk getRow 2051521 1171587 1171654 := by
  decide +kernel

private theorem r_1171654 : RangeOk getRow 2051521 1171654 1171721 := by
  decide +kernel

private theorem r_1171721 : RangeOk getRow 2051521 1171721 1171788 := by
  decide +kernel

private theorem r_1171788 : RangeOk getRow 2051521 1171788 1171855 := by
  decide +kernel

private theorem r_1171855 : RangeOk getRow 2051521 1171855 1171922 := by
  decide +kernel

private theorem r_1171922 : RangeOk getRow 2051521 1171922 1171990 := by
  decide +kernel

private theorem r_1171990 : RangeOk getRow 2051521 1171990 1172058 := by
  decide +kernel

private theorem r_1172058 : RangeOk getRow 2051521 1172058 1172126 := by
  decide +kernel

private theorem r_1172126 : RangeOk getRow 2051521 1172126 1172194 := by
  decide +kernel

private theorem r_1172194 : RangeOk getRow 2051521 1172194 1172262 := by
  decide +kernel

private theorem r_1172262 : RangeOk getRow 2051521 1172262 1172327 := by
  decide +kernel

private theorem r_1172327 : RangeOk getRow 2051521 1172327 1172396 := by
  decide +kernel

private theorem r_1172396 : RangeOk getRow 2051521 1172396 1172464 := by
  decide +kernel

private theorem r_1172464 : RangeOk getRow 2051521 1172464 1172529 := by
  decide +kernel

private theorem r_1172529 : RangeOk getRow 2051521 1172529 1172598 := by
  decide +kernel

private theorem r_1172598 : RangeOk getRow 2051521 1172598 1172666 := by
  decide +kernel

private theorem r_1172666 : RangeOk getRow 2051521 1172666 1172734 := by
  decide +kernel

private theorem r_1172734 : RangeOk getRow 2051521 1172734 1172804 := by
  decide +kernel

private theorem r_1172804 : RangeOk getRow 2051521 1172804 1172870 := by
  decide +kernel

private theorem s_1170483 : RangeOk getRow 2051521 1170412 1170483 := r_1170412
private theorem s_1170556 : RangeOk getRow 2051521 1170412 1170556 :=
  s_1170483.append (by norm_num) r_1170483
private theorem s_1170628 : RangeOk getRow 2051521 1170412 1170628 :=
  s_1170556.append (by norm_num) r_1170556
private theorem s_1170697 : RangeOk getRow 2051521 1170412 1170697 :=
  s_1170628.append (by norm_num) r_1170628
private theorem s_1170767 : RangeOk getRow 2051521 1170412 1170767 :=
  s_1170697.append (by norm_num) r_1170697
private theorem s_1170836 : RangeOk getRow 2051521 1170412 1170836 :=
  s_1170767.append (by norm_num) r_1170767
private theorem s_1170908 : RangeOk getRow 2051521 1170412 1170908 :=
  s_1170836.append (by norm_num) r_1170836
private theorem s_1170979 : RangeOk getRow 2051521 1170412 1170979 :=
  s_1170908.append (by norm_num) r_1170908
private theorem s_1171048 : RangeOk getRow 2051521 1170412 1171048 :=
  s_1170979.append (by norm_num) r_1170979
private theorem s_1171115 : RangeOk getRow 2051521 1170412 1171115 :=
  s_1171048.append (by norm_num) r_1171048
private theorem s_1171184 : RangeOk getRow 2051521 1170412 1171184 :=
  s_1171115.append (by norm_num) r_1171115
private theorem s_1171251 : RangeOk getRow 2051521 1170412 1171251 :=
  s_1171184.append (by norm_num) r_1171184
private theorem s_1171318 : RangeOk getRow 2051521 1170412 1171318 :=
  s_1171251.append (by norm_num) r_1171251
private theorem s_1171385 : RangeOk getRow 2051521 1170412 1171385 :=
  s_1171318.append (by norm_num) r_1171318
private theorem s_1171453 : RangeOk getRow 2051521 1170412 1171453 :=
  s_1171385.append (by norm_num) r_1171385
private theorem s_1171520 : RangeOk getRow 2051521 1170412 1171520 :=
  s_1171453.append (by norm_num) r_1171453
private theorem s_1171587 : RangeOk getRow 2051521 1170412 1171587 :=
  s_1171520.append (by norm_num) r_1171520
private theorem s_1171654 : RangeOk getRow 2051521 1170412 1171654 :=
  s_1171587.append (by norm_num) r_1171587
private theorem s_1171721 : RangeOk getRow 2051521 1170412 1171721 :=
  s_1171654.append (by norm_num) r_1171654
private theorem s_1171788 : RangeOk getRow 2051521 1170412 1171788 :=
  s_1171721.append (by norm_num) r_1171721
private theorem s_1171855 : RangeOk getRow 2051521 1170412 1171855 :=
  s_1171788.append (by norm_num) r_1171788
private theorem s_1171922 : RangeOk getRow 2051521 1170412 1171922 :=
  s_1171855.append (by norm_num) r_1171855
private theorem s_1171990 : RangeOk getRow 2051521 1170412 1171990 :=
  s_1171922.append (by norm_num) r_1171922
private theorem s_1172058 : RangeOk getRow 2051521 1170412 1172058 :=
  s_1171990.append (by norm_num) r_1171990
private theorem s_1172126 : RangeOk getRow 2051521 1170412 1172126 :=
  s_1172058.append (by norm_num) r_1172058
private theorem s_1172194 : RangeOk getRow 2051521 1170412 1172194 :=
  s_1172126.append (by norm_num) r_1172126
private theorem s_1172262 : RangeOk getRow 2051521 1170412 1172262 :=
  s_1172194.append (by norm_num) r_1172194
private theorem s_1172327 : RangeOk getRow 2051521 1170412 1172327 :=
  s_1172262.append (by norm_num) r_1172262
private theorem s_1172396 : RangeOk getRow 2051521 1170412 1172396 :=
  s_1172327.append (by norm_num) r_1172327
private theorem s_1172464 : RangeOk getRow 2051521 1170412 1172464 :=
  s_1172396.append (by norm_num) r_1172396
private theorem s_1172529 : RangeOk getRow 2051521 1170412 1172529 :=
  s_1172464.append (by norm_num) r_1172464
private theorem s_1172598 : RangeOk getRow 2051521 1170412 1172598 :=
  s_1172529.append (by norm_num) r_1172529
private theorem s_1172666 : RangeOk getRow 2051521 1170412 1172666 :=
  s_1172598.append (by norm_num) r_1172598
private theorem s_1172734 : RangeOk getRow 2051521 1170412 1172734 :=
  s_1172666.append (by norm_num) r_1172666
private theorem s_1172804 : RangeOk getRow 2051521 1170412 1172804 :=
  s_1172734.append (by norm_num) r_1172734
private theorem s_1172870 : RangeOk getRow 2051521 1170412 1172870 :=
  s_1172804.append (by norm_num) r_1172804

/-- Rows `[1170412, 1172870)` are valid. -/
theorem rangeOk_1170412_1172870 : RangeOk getRow 2051521 1170412 1172870 := s_1172870

end Noperthedron.Solution
