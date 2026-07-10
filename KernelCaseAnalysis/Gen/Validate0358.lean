import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[861701, 864155). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_861701 : RangeOk getRow 2051521 861701 861766 := by
  decide +kernel

private theorem r_861766 : RangeOk getRow 2051521 861766 861831 := by
  decide +kernel

private theorem r_861831 : RangeOk getRow 2051521 861831 861895 := by
  decide +kernel

private theorem r_861895 : RangeOk getRow 2051521 861895 861967 := by
  decide +kernel

private theorem r_861967 : RangeOk getRow 2051521 861967 862038 := by
  decide +kernel

private theorem r_862038 : RangeOk getRow 2051521 862038 862108 := by
  decide +kernel

private theorem r_862108 : RangeOk getRow 2051521 862108 862177 := by
  decide +kernel

private theorem r_862177 : RangeOk getRow 2051521 862177 862251 := by
  decide +kernel

private theorem r_862251 : RangeOk getRow 2051521 862251 862319 := by
  decide +kernel

private theorem r_862319 : RangeOk getRow 2051521 862319 862389 := by
  decide +kernel

private theorem r_862389 : RangeOk getRow 2051521 862389 862460 := by
  decide +kernel

private theorem r_862460 : RangeOk getRow 2051521 862460 862531 := by
  decide +kernel

private theorem r_862531 : RangeOk getRow 2051521 862531 862599 := by
  decide +kernel

private theorem r_862599 : RangeOk getRow 2051521 862599 862667 := by
  decide +kernel

private theorem r_862667 : RangeOk getRow 2051521 862667 862734 := by
  decide +kernel

private theorem r_862734 : RangeOk getRow 2051521 862734 862802 := by
  decide +kernel

private theorem r_862802 : RangeOk getRow 2051521 862802 862866 := by
  decide +kernel

private theorem r_862866 : RangeOk getRow 2051521 862866 862933 := by
  decide +kernel

private theorem r_862933 : RangeOk getRow 2051521 862933 862999 := by
  decide +kernel

private theorem r_862999 : RangeOk getRow 2051521 862999 863064 := by
  decide +kernel

private theorem r_863064 : RangeOk getRow 2051521 863064 863128 := by
  decide +kernel

private theorem r_863128 : RangeOk getRow 2051521 863128 863193 := by
  decide +kernel

private theorem r_863193 : RangeOk getRow 2051521 863193 863265 := by
  decide +kernel

private theorem r_863265 : RangeOk getRow 2051521 863265 863335 := by
  decide +kernel

private theorem r_863335 : RangeOk getRow 2051521 863335 863405 := by
  decide +kernel

private theorem r_863405 : RangeOk getRow 2051521 863405 863475 := by
  decide +kernel

private theorem r_863475 : RangeOk getRow 2051521 863475 863546 := by
  decide +kernel

private theorem r_863546 : RangeOk getRow 2051521 863546 863614 := by
  decide +kernel

private theorem r_863614 : RangeOk getRow 2051521 863614 863683 := by
  decide +kernel

private theorem r_863683 : RangeOk getRow 2051521 863683 863754 := by
  decide +kernel

private theorem r_863754 : RangeOk getRow 2051521 863754 863820 := by
  decide +kernel

private theorem r_863820 : RangeOk getRow 2051521 863820 863887 := by
  decide +kernel

private theorem r_863887 : RangeOk getRow 2051521 863887 863955 := by
  decide +kernel

private theorem r_863955 : RangeOk getRow 2051521 863955 864024 := by
  decide +kernel

private theorem r_864024 : RangeOk getRow 2051521 864024 864090 := by
  decide +kernel

private theorem r_864090 : RangeOk getRow 2051521 864090 864155 := by
  decide +kernel

private theorem s_861766 : RangeOk getRow 2051521 861701 861766 := r_861701
private theorem s_861831 : RangeOk getRow 2051521 861701 861831 :=
  s_861766.append (by norm_num) r_861766
private theorem s_861895 : RangeOk getRow 2051521 861701 861895 :=
  s_861831.append (by norm_num) r_861831
private theorem s_861967 : RangeOk getRow 2051521 861701 861967 :=
  s_861895.append (by norm_num) r_861895
private theorem s_862038 : RangeOk getRow 2051521 861701 862038 :=
  s_861967.append (by norm_num) r_861967
private theorem s_862108 : RangeOk getRow 2051521 861701 862108 :=
  s_862038.append (by norm_num) r_862038
private theorem s_862177 : RangeOk getRow 2051521 861701 862177 :=
  s_862108.append (by norm_num) r_862108
private theorem s_862251 : RangeOk getRow 2051521 861701 862251 :=
  s_862177.append (by norm_num) r_862177
private theorem s_862319 : RangeOk getRow 2051521 861701 862319 :=
  s_862251.append (by norm_num) r_862251
private theorem s_862389 : RangeOk getRow 2051521 861701 862389 :=
  s_862319.append (by norm_num) r_862319
private theorem s_862460 : RangeOk getRow 2051521 861701 862460 :=
  s_862389.append (by norm_num) r_862389
private theorem s_862531 : RangeOk getRow 2051521 861701 862531 :=
  s_862460.append (by norm_num) r_862460
private theorem s_862599 : RangeOk getRow 2051521 861701 862599 :=
  s_862531.append (by norm_num) r_862531
private theorem s_862667 : RangeOk getRow 2051521 861701 862667 :=
  s_862599.append (by norm_num) r_862599
private theorem s_862734 : RangeOk getRow 2051521 861701 862734 :=
  s_862667.append (by norm_num) r_862667
private theorem s_862802 : RangeOk getRow 2051521 861701 862802 :=
  s_862734.append (by norm_num) r_862734
private theorem s_862866 : RangeOk getRow 2051521 861701 862866 :=
  s_862802.append (by norm_num) r_862802
private theorem s_862933 : RangeOk getRow 2051521 861701 862933 :=
  s_862866.append (by norm_num) r_862866
private theorem s_862999 : RangeOk getRow 2051521 861701 862999 :=
  s_862933.append (by norm_num) r_862933
private theorem s_863064 : RangeOk getRow 2051521 861701 863064 :=
  s_862999.append (by norm_num) r_862999
private theorem s_863128 : RangeOk getRow 2051521 861701 863128 :=
  s_863064.append (by norm_num) r_863064
private theorem s_863193 : RangeOk getRow 2051521 861701 863193 :=
  s_863128.append (by norm_num) r_863128
private theorem s_863265 : RangeOk getRow 2051521 861701 863265 :=
  s_863193.append (by norm_num) r_863193
private theorem s_863335 : RangeOk getRow 2051521 861701 863335 :=
  s_863265.append (by norm_num) r_863265
private theorem s_863405 : RangeOk getRow 2051521 861701 863405 :=
  s_863335.append (by norm_num) r_863335
private theorem s_863475 : RangeOk getRow 2051521 861701 863475 :=
  s_863405.append (by norm_num) r_863405
private theorem s_863546 : RangeOk getRow 2051521 861701 863546 :=
  s_863475.append (by norm_num) r_863475
private theorem s_863614 : RangeOk getRow 2051521 861701 863614 :=
  s_863546.append (by norm_num) r_863546
private theorem s_863683 : RangeOk getRow 2051521 861701 863683 :=
  s_863614.append (by norm_num) r_863614
private theorem s_863754 : RangeOk getRow 2051521 861701 863754 :=
  s_863683.append (by norm_num) r_863683
private theorem s_863820 : RangeOk getRow 2051521 861701 863820 :=
  s_863754.append (by norm_num) r_863754
private theorem s_863887 : RangeOk getRow 2051521 861701 863887 :=
  s_863820.append (by norm_num) r_863820
private theorem s_863955 : RangeOk getRow 2051521 861701 863955 :=
  s_863887.append (by norm_num) r_863887
private theorem s_864024 : RangeOk getRow 2051521 861701 864024 :=
  s_863955.append (by norm_num) r_863955
private theorem s_864090 : RangeOk getRow 2051521 861701 864090 :=
  s_864024.append (by norm_num) r_864024
private theorem s_864155 : RangeOk getRow 2051521 861701 864155 :=
  s_864090.append (by norm_num) r_864090

/-- Rows `[861701, 864155)` are valid. -/
theorem rangeOk_861701_864155 : RangeOk getRow 2051521 861701 864155 := s_864155

end Noperthedron.Solution
