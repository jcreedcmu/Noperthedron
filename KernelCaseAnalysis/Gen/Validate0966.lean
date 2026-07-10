import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[2007418, 2009961). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_2007418 : RangeOk getRow 2051521 2007418 2007489 := by
  decide +kernel

private theorem r_2007489 : RangeOk getRow 2051521 2007489 2007561 := by
  decide +kernel

private theorem r_2007561 : RangeOk getRow 2051521 2007561 2007633 := by
  decide +kernel

private theorem r_2007633 : RangeOk getRow 2051521 2007633 2007703 := by
  decide +kernel

private theorem r_2007703 : RangeOk getRow 2051521 2007703 2007767 := by
  decide +kernel

private theorem r_2007767 : RangeOk getRow 2051521 2007767 2007810 := by
  decide +kernel

private theorem r_2007810 : RangeOk getRow 2051521 2007810 2007847 := by
  decide +kernel

private theorem r_2007847 : RangeOk getRow 2051521 2007847 2007884 := by
  decide +kernel

private theorem r_2007884 : RangeOk getRow 2051521 2007884 2007921 := by
  decide +kernel

private theorem r_2007921 : RangeOk getRow 2051521 2007921 2007965 := by
  decide +kernel

private theorem r_2007965 : RangeOk getRow 2051521 2007965 2008008 := by
  decide +kernel

private theorem r_2008008 : RangeOk getRow 2051521 2008008 2008042 := by
  decide +kernel

private theorem r_2008042 : RangeOk getRow 2051521 2008042 2008064 := by
  decide +kernel

private theorem r_2008064 : RangeOk getRow 2051521 2008064 2008112 := by
  decide +kernel

private theorem r_2008112 : RangeOk getRow 2051521 2008112 2008147 := by
  decide +kernel

private theorem r_2008147 : RangeOk getRow 2051521 2008147 2008212 := by
  decide +kernel

private theorem r_2008212 : RangeOk getRow 2051521 2008212 2008270 := by
  decide +kernel

private theorem r_2008270 : RangeOk getRow 2051521 2008270 2008313 := by
  decide +kernel

private theorem r_2008313 : RangeOk getRow 2051521 2008313 2008379 := by
  decide +kernel

private theorem r_2008379 : RangeOk getRow 2051521 2008379 2008434 := by
  decide +kernel

private theorem r_2008434 : RangeOk getRow 2051521 2008434 2008472 := by
  decide +kernel

private theorem r_2008472 : RangeOk getRow 2051521 2008472 2008537 := by
  decide +kernel

private theorem r_2008537 : RangeOk getRow 2051521 2008537 2008600 := by
  decide +kernel

private theorem r_2008600 : RangeOk getRow 2051521 2008600 2008656 := by
  decide +kernel

private theorem r_2008656 : RangeOk getRow 2051521 2008656 2008719 := by
  decide +kernel

private theorem r_2008719 : RangeOk getRow 2051521 2008719 2008784 := by
  decide +kernel

private theorem r_2008784 : RangeOk getRow 2051521 2008784 2008841 := by
  decide +kernel

private theorem r_2008841 : RangeOk getRow 2051521 2008841 2008877 := by
  decide +kernel

private theorem r_2008877 : RangeOk getRow 2051521 2008877 2008936 := by
  decide +kernel

private theorem r_2008936 : RangeOk getRow 2051521 2008936 2008966 := by
  decide +kernel

private theorem r_2008966 : RangeOk getRow 2051521 2008966 2009023 := by
  decide +kernel

private theorem r_2009023 : RangeOk getRow 2051521 2009023 2009086 := by
  decide +kernel

private theorem r_2009086 : RangeOk getRow 2051521 2009086 2009137 := by
  decide +kernel

private theorem r_2009137 : RangeOk getRow 2051521 2009137 2009187 := by
  decide +kernel

private theorem r_2009187 : RangeOk getRow 2051521 2009187 2009244 := by
  decide +kernel

private theorem r_2009244 : RangeOk getRow 2051521 2009244 2009287 := by
  decide +kernel

private theorem r_2009287 : RangeOk getRow 2051521 2009287 2009344 := by
  decide +kernel

private theorem r_2009344 : RangeOk getRow 2051521 2009344 2009414 := by
  decide +kernel

private theorem r_2009414 : RangeOk getRow 2051521 2009414 2009478 := by
  decide +kernel

private theorem r_2009478 : RangeOk getRow 2051521 2009478 2009528 := by
  decide +kernel

private theorem r_2009528 : RangeOk getRow 2051521 2009528 2009597 := by
  decide +kernel

private theorem r_2009597 : RangeOk getRow 2051521 2009597 2009646 := by
  decide +kernel

private theorem r_2009646 : RangeOk getRow 2051521 2009646 2009700 := by
  decide +kernel

private theorem r_2009700 : RangeOk getRow 2051521 2009700 2009751 := by
  decide +kernel

private theorem r_2009751 : RangeOk getRow 2051521 2009751 2009801 := by
  decide +kernel

private theorem r_2009801 : RangeOk getRow 2051521 2009801 2009868 := by
  decide +kernel

private theorem r_2009868 : RangeOk getRow 2051521 2009868 2009911 := by
  decide +kernel

private theorem r_2009911 : RangeOk getRow 2051521 2009911 2009961 := by
  decide +kernel

private theorem s_2007489 : RangeOk getRow 2051521 2007418 2007489 := r_2007418
private theorem s_2007561 : RangeOk getRow 2051521 2007418 2007561 :=
  s_2007489.append (by norm_num) r_2007489
private theorem s_2007633 : RangeOk getRow 2051521 2007418 2007633 :=
  s_2007561.append (by norm_num) r_2007561
private theorem s_2007703 : RangeOk getRow 2051521 2007418 2007703 :=
  s_2007633.append (by norm_num) r_2007633
private theorem s_2007767 : RangeOk getRow 2051521 2007418 2007767 :=
  s_2007703.append (by norm_num) r_2007703
private theorem s_2007810 : RangeOk getRow 2051521 2007418 2007810 :=
  s_2007767.append (by norm_num) r_2007767
private theorem s_2007847 : RangeOk getRow 2051521 2007418 2007847 :=
  s_2007810.append (by norm_num) r_2007810
private theorem s_2007884 : RangeOk getRow 2051521 2007418 2007884 :=
  s_2007847.append (by norm_num) r_2007847
private theorem s_2007921 : RangeOk getRow 2051521 2007418 2007921 :=
  s_2007884.append (by norm_num) r_2007884
private theorem s_2007965 : RangeOk getRow 2051521 2007418 2007965 :=
  s_2007921.append (by norm_num) r_2007921
private theorem s_2008008 : RangeOk getRow 2051521 2007418 2008008 :=
  s_2007965.append (by norm_num) r_2007965
private theorem s_2008042 : RangeOk getRow 2051521 2007418 2008042 :=
  s_2008008.append (by norm_num) r_2008008
private theorem s_2008064 : RangeOk getRow 2051521 2007418 2008064 :=
  s_2008042.append (by norm_num) r_2008042
private theorem s_2008112 : RangeOk getRow 2051521 2007418 2008112 :=
  s_2008064.append (by norm_num) r_2008064
private theorem s_2008147 : RangeOk getRow 2051521 2007418 2008147 :=
  s_2008112.append (by norm_num) r_2008112
private theorem s_2008212 : RangeOk getRow 2051521 2007418 2008212 :=
  s_2008147.append (by norm_num) r_2008147
private theorem s_2008270 : RangeOk getRow 2051521 2007418 2008270 :=
  s_2008212.append (by norm_num) r_2008212
private theorem s_2008313 : RangeOk getRow 2051521 2007418 2008313 :=
  s_2008270.append (by norm_num) r_2008270
private theorem s_2008379 : RangeOk getRow 2051521 2007418 2008379 :=
  s_2008313.append (by norm_num) r_2008313
private theorem s_2008434 : RangeOk getRow 2051521 2007418 2008434 :=
  s_2008379.append (by norm_num) r_2008379
private theorem s_2008472 : RangeOk getRow 2051521 2007418 2008472 :=
  s_2008434.append (by norm_num) r_2008434
private theorem s_2008537 : RangeOk getRow 2051521 2007418 2008537 :=
  s_2008472.append (by norm_num) r_2008472
private theorem s_2008600 : RangeOk getRow 2051521 2007418 2008600 :=
  s_2008537.append (by norm_num) r_2008537
private theorem s_2008656 : RangeOk getRow 2051521 2007418 2008656 :=
  s_2008600.append (by norm_num) r_2008600
private theorem s_2008719 : RangeOk getRow 2051521 2007418 2008719 :=
  s_2008656.append (by norm_num) r_2008656
private theorem s_2008784 : RangeOk getRow 2051521 2007418 2008784 :=
  s_2008719.append (by norm_num) r_2008719
private theorem s_2008841 : RangeOk getRow 2051521 2007418 2008841 :=
  s_2008784.append (by norm_num) r_2008784
private theorem s_2008877 : RangeOk getRow 2051521 2007418 2008877 :=
  s_2008841.append (by norm_num) r_2008841
private theorem s_2008936 : RangeOk getRow 2051521 2007418 2008936 :=
  s_2008877.append (by norm_num) r_2008877
private theorem s_2008966 : RangeOk getRow 2051521 2007418 2008966 :=
  s_2008936.append (by norm_num) r_2008936
private theorem s_2009023 : RangeOk getRow 2051521 2007418 2009023 :=
  s_2008966.append (by norm_num) r_2008966
private theorem s_2009086 : RangeOk getRow 2051521 2007418 2009086 :=
  s_2009023.append (by norm_num) r_2009023
private theorem s_2009137 : RangeOk getRow 2051521 2007418 2009137 :=
  s_2009086.append (by norm_num) r_2009086
private theorem s_2009187 : RangeOk getRow 2051521 2007418 2009187 :=
  s_2009137.append (by norm_num) r_2009137
private theorem s_2009244 : RangeOk getRow 2051521 2007418 2009244 :=
  s_2009187.append (by norm_num) r_2009187
private theorem s_2009287 : RangeOk getRow 2051521 2007418 2009287 :=
  s_2009244.append (by norm_num) r_2009244
private theorem s_2009344 : RangeOk getRow 2051521 2007418 2009344 :=
  s_2009287.append (by norm_num) r_2009287
private theorem s_2009414 : RangeOk getRow 2051521 2007418 2009414 :=
  s_2009344.append (by norm_num) r_2009344
private theorem s_2009478 : RangeOk getRow 2051521 2007418 2009478 :=
  s_2009414.append (by norm_num) r_2009414
private theorem s_2009528 : RangeOk getRow 2051521 2007418 2009528 :=
  s_2009478.append (by norm_num) r_2009478
private theorem s_2009597 : RangeOk getRow 2051521 2007418 2009597 :=
  s_2009528.append (by norm_num) r_2009528
private theorem s_2009646 : RangeOk getRow 2051521 2007418 2009646 :=
  s_2009597.append (by norm_num) r_2009597
private theorem s_2009700 : RangeOk getRow 2051521 2007418 2009700 :=
  s_2009646.append (by norm_num) r_2009646
private theorem s_2009751 : RangeOk getRow 2051521 2007418 2009751 :=
  s_2009700.append (by norm_num) r_2009700
private theorem s_2009801 : RangeOk getRow 2051521 2007418 2009801 :=
  s_2009751.append (by norm_num) r_2009751
private theorem s_2009868 : RangeOk getRow 2051521 2007418 2009868 :=
  s_2009801.append (by norm_num) r_2009801
private theorem s_2009911 : RangeOk getRow 2051521 2007418 2009911 :=
  s_2009868.append (by norm_num) r_2009868
private theorem s_2009961 : RangeOk getRow 2051521 2007418 2009961 :=
  s_2009911.append (by norm_num) r_2009911

/-- Rows `[2007418, 2009961)` are valid. -/
theorem rangeOk_2007418_2009961 : RangeOk getRow 2051521 2007418 2009961 := s_2009961

end Noperthedron.Solution
