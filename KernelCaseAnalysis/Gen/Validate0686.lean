import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1749921, 1753188). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1749921 : RangeOk getRow 2051521 1749921 1749992 := by
  decide +kernel

private theorem r_1749992 : RangeOk getRow 2051521 1749992 1750061 := by
  decide +kernel

private theorem r_1750061 : RangeOk getRow 2051521 1750061 1750132 := by
  decide +kernel

private theorem r_1750132 : RangeOk getRow 2051521 1750132 1750204 := by
  decide +kernel

private theorem r_1750204 : RangeOk getRow 2051521 1750204 1750275 := by
  decide +kernel

private theorem r_1750275 : RangeOk getRow 2051521 1750275 1750347 := by
  decide +kernel

private theorem r_1750347 : RangeOk getRow 2051521 1750347 1750419 := by
  decide +kernel

private theorem r_1750419 : RangeOk getRow 2051521 1750419 1750491 := by
  decide +kernel

private theorem r_1750491 : RangeOk getRow 2051521 1750491 1750563 := by
  decide +kernel

private theorem r_1750563 : RangeOk getRow 2051521 1750563 1750635 := by
  decide +kernel

private theorem r_1750635 : RangeOk getRow 2051521 1750635 1750707 := by
  decide +kernel

private theorem r_1750707 : RangeOk getRow 2051521 1750707 1750779 := by
  decide +kernel

private theorem r_1750779 : RangeOk getRow 2051521 1750779 1750851 := by
  decide +kernel

private theorem r_1750851 : RangeOk getRow 2051521 1750851 1750923 := by
  decide +kernel

private theorem r_1750923 : RangeOk getRow 2051521 1750923 1750996 := by
  decide +kernel

private theorem r_1750996 : RangeOk getRow 2051521 1750996 1751068 := by
  decide +kernel

private theorem r_1751068 : RangeOk getRow 2051521 1751068 1751141 := by
  decide +kernel

private theorem r_1751141 : RangeOk getRow 2051521 1751141 1751212 := by
  decide +kernel

private theorem r_1751212 : RangeOk getRow 2051521 1751212 1751284 := by
  decide +kernel

private theorem r_1751284 : RangeOk getRow 2051521 1751284 1751357 := by
  decide +kernel

private theorem r_1751357 : RangeOk getRow 2051521 1751357 1751430 := by
  decide +kernel

private theorem r_1751430 : RangeOk getRow 2051521 1751430 1751502 := by
  decide +kernel

private theorem r_1751502 : RangeOk getRow 2051521 1751502 1751573 := by
  decide +kernel

private theorem r_1751573 : RangeOk getRow 2051521 1751573 1751644 := by
  decide +kernel

private theorem r_1751644 : RangeOk getRow 2051521 1751644 1751715 := by
  decide +kernel

private theorem r_1751715 : RangeOk getRow 2051521 1751715 1751786 := by
  decide +kernel

private theorem r_1751786 : RangeOk getRow 2051521 1751786 1751847 := by
  decide +kernel

private theorem r_1751847 : RangeOk getRow 2051521 1751847 1751884 := by
  decide +kernel

private theorem r_1751884 : RangeOk getRow 2051521 1751884 1751933 := by
  decide +kernel

private theorem r_1751933 : RangeOk getRow 2051521 1751933 1751971 := by
  decide +kernel

private theorem r_1751971 : RangeOk getRow 2051521 1751971 1752014 := by
  decide +kernel

private theorem r_1752014 : RangeOk getRow 2051521 1752014 1752057 := by
  decide +kernel

private theorem r_1752057 : RangeOk getRow 2051521 1752057 1752097 := by
  decide +kernel

private theorem r_1752097 : RangeOk getRow 2051521 1752097 1752133 := by
  decide +kernel

private theorem r_1752133 : RangeOk getRow 2051521 1752133 1752183 := by
  decide +kernel

private theorem r_1752183 : RangeOk getRow 2051521 1752183 1752241 := by
  decide +kernel

private theorem r_1752241 : RangeOk getRow 2051521 1752241 1752307 := by
  decide +kernel

private theorem r_1752307 : RangeOk getRow 2051521 1752307 1752379 := by
  decide +kernel

private theorem r_1752379 : RangeOk getRow 2051521 1752379 1752436 := by
  decide +kernel

private theorem r_1752436 : RangeOk getRow 2051521 1752436 1752480 := by
  decide +kernel

private theorem r_1752480 : RangeOk getRow 2051521 1752480 1752553 := by
  decide +kernel

private theorem r_1752553 : RangeOk getRow 2051521 1752553 1752618 := by
  decide +kernel

private theorem r_1752618 : RangeOk getRow 2051521 1752618 1752690 := by
  decide +kernel

private theorem r_1752690 : RangeOk getRow 2051521 1752690 1752755 := by
  decide +kernel

private theorem r_1752755 : RangeOk getRow 2051521 1752755 1752827 := by
  decide +kernel

private theorem r_1752827 : RangeOk getRow 2051521 1752827 1752898 := by
  decide +kernel

private theorem r_1752898 : RangeOk getRow 2051521 1752898 1752970 := by
  decide +kernel

private theorem r_1752970 : RangeOk getRow 2051521 1752970 1753044 := by
  decide +kernel

private theorem r_1753044 : RangeOk getRow 2051521 1753044 1753116 := by
  decide +kernel

private theorem r_1753116 : RangeOk getRow 2051521 1753116 1753188 := by
  decide +kernel

private theorem s_1749992 : RangeOk getRow 2051521 1749921 1749992 := r_1749921
private theorem s_1750061 : RangeOk getRow 2051521 1749921 1750061 :=
  s_1749992.append (by norm_num) r_1749992
private theorem s_1750132 : RangeOk getRow 2051521 1749921 1750132 :=
  s_1750061.append (by norm_num) r_1750061
private theorem s_1750204 : RangeOk getRow 2051521 1749921 1750204 :=
  s_1750132.append (by norm_num) r_1750132
private theorem s_1750275 : RangeOk getRow 2051521 1749921 1750275 :=
  s_1750204.append (by norm_num) r_1750204
private theorem s_1750347 : RangeOk getRow 2051521 1749921 1750347 :=
  s_1750275.append (by norm_num) r_1750275
private theorem s_1750419 : RangeOk getRow 2051521 1749921 1750419 :=
  s_1750347.append (by norm_num) r_1750347
private theorem s_1750491 : RangeOk getRow 2051521 1749921 1750491 :=
  s_1750419.append (by norm_num) r_1750419
private theorem s_1750563 : RangeOk getRow 2051521 1749921 1750563 :=
  s_1750491.append (by norm_num) r_1750491
private theorem s_1750635 : RangeOk getRow 2051521 1749921 1750635 :=
  s_1750563.append (by norm_num) r_1750563
private theorem s_1750707 : RangeOk getRow 2051521 1749921 1750707 :=
  s_1750635.append (by norm_num) r_1750635
private theorem s_1750779 : RangeOk getRow 2051521 1749921 1750779 :=
  s_1750707.append (by norm_num) r_1750707
private theorem s_1750851 : RangeOk getRow 2051521 1749921 1750851 :=
  s_1750779.append (by norm_num) r_1750779
private theorem s_1750923 : RangeOk getRow 2051521 1749921 1750923 :=
  s_1750851.append (by norm_num) r_1750851
private theorem s_1750996 : RangeOk getRow 2051521 1749921 1750996 :=
  s_1750923.append (by norm_num) r_1750923
private theorem s_1751068 : RangeOk getRow 2051521 1749921 1751068 :=
  s_1750996.append (by norm_num) r_1750996
private theorem s_1751141 : RangeOk getRow 2051521 1749921 1751141 :=
  s_1751068.append (by norm_num) r_1751068
private theorem s_1751212 : RangeOk getRow 2051521 1749921 1751212 :=
  s_1751141.append (by norm_num) r_1751141
private theorem s_1751284 : RangeOk getRow 2051521 1749921 1751284 :=
  s_1751212.append (by norm_num) r_1751212
private theorem s_1751357 : RangeOk getRow 2051521 1749921 1751357 :=
  s_1751284.append (by norm_num) r_1751284
private theorem s_1751430 : RangeOk getRow 2051521 1749921 1751430 :=
  s_1751357.append (by norm_num) r_1751357
private theorem s_1751502 : RangeOk getRow 2051521 1749921 1751502 :=
  s_1751430.append (by norm_num) r_1751430
private theorem s_1751573 : RangeOk getRow 2051521 1749921 1751573 :=
  s_1751502.append (by norm_num) r_1751502
private theorem s_1751644 : RangeOk getRow 2051521 1749921 1751644 :=
  s_1751573.append (by norm_num) r_1751573
private theorem s_1751715 : RangeOk getRow 2051521 1749921 1751715 :=
  s_1751644.append (by norm_num) r_1751644
private theorem s_1751786 : RangeOk getRow 2051521 1749921 1751786 :=
  s_1751715.append (by norm_num) r_1751715
private theorem s_1751847 : RangeOk getRow 2051521 1749921 1751847 :=
  s_1751786.append (by norm_num) r_1751786
private theorem s_1751884 : RangeOk getRow 2051521 1749921 1751884 :=
  s_1751847.append (by norm_num) r_1751847
private theorem s_1751933 : RangeOk getRow 2051521 1749921 1751933 :=
  s_1751884.append (by norm_num) r_1751884
private theorem s_1751971 : RangeOk getRow 2051521 1749921 1751971 :=
  s_1751933.append (by norm_num) r_1751933
private theorem s_1752014 : RangeOk getRow 2051521 1749921 1752014 :=
  s_1751971.append (by norm_num) r_1751971
private theorem s_1752057 : RangeOk getRow 2051521 1749921 1752057 :=
  s_1752014.append (by norm_num) r_1752014
private theorem s_1752097 : RangeOk getRow 2051521 1749921 1752097 :=
  s_1752057.append (by norm_num) r_1752057
private theorem s_1752133 : RangeOk getRow 2051521 1749921 1752133 :=
  s_1752097.append (by norm_num) r_1752097
private theorem s_1752183 : RangeOk getRow 2051521 1749921 1752183 :=
  s_1752133.append (by norm_num) r_1752133
private theorem s_1752241 : RangeOk getRow 2051521 1749921 1752241 :=
  s_1752183.append (by norm_num) r_1752183
private theorem s_1752307 : RangeOk getRow 2051521 1749921 1752307 :=
  s_1752241.append (by norm_num) r_1752241
private theorem s_1752379 : RangeOk getRow 2051521 1749921 1752379 :=
  s_1752307.append (by norm_num) r_1752307
private theorem s_1752436 : RangeOk getRow 2051521 1749921 1752436 :=
  s_1752379.append (by norm_num) r_1752379
private theorem s_1752480 : RangeOk getRow 2051521 1749921 1752480 :=
  s_1752436.append (by norm_num) r_1752436
private theorem s_1752553 : RangeOk getRow 2051521 1749921 1752553 :=
  s_1752480.append (by norm_num) r_1752480
private theorem s_1752618 : RangeOk getRow 2051521 1749921 1752618 :=
  s_1752553.append (by norm_num) r_1752553
private theorem s_1752690 : RangeOk getRow 2051521 1749921 1752690 :=
  s_1752618.append (by norm_num) r_1752618
private theorem s_1752755 : RangeOk getRow 2051521 1749921 1752755 :=
  s_1752690.append (by norm_num) r_1752690
private theorem s_1752827 : RangeOk getRow 2051521 1749921 1752827 :=
  s_1752755.append (by norm_num) r_1752755
private theorem s_1752898 : RangeOk getRow 2051521 1749921 1752898 :=
  s_1752827.append (by norm_num) r_1752827
private theorem s_1752970 : RangeOk getRow 2051521 1749921 1752970 :=
  s_1752898.append (by norm_num) r_1752898
private theorem s_1753044 : RangeOk getRow 2051521 1749921 1753044 :=
  s_1752970.append (by norm_num) r_1752970
private theorem s_1753116 : RangeOk getRow 2051521 1749921 1753116 :=
  s_1753044.append (by norm_num) r_1753044
private theorem s_1753188 : RangeOk getRow 2051521 1749921 1753188 :=
  s_1753116.append (by norm_num) r_1753116

/-- Rows `[1749921, 1753188)` are valid. -/
theorem rangeOk_1749921_1753188 : RangeOk getRow 2051521 1749921 1753188 := s_1753188

end Noperthedron.Solution
