import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[666840, 669209). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_666840 : RangeOk getRow 2051521 666840 666909 := by
  decide +kernel

private theorem r_666909 : RangeOk getRow 2051521 666909 666977 := by
  decide +kernel

private theorem r_666977 : RangeOk getRow 2051521 666977 667043 := by
  decide +kernel

private theorem r_667043 : RangeOk getRow 2051521 667043 667112 := by
  decide +kernel

private theorem r_667112 : RangeOk getRow 2051521 667112 667179 := by
  decide +kernel

private theorem r_667179 : RangeOk getRow 2051521 667179 667243 := by
  decide +kernel

private theorem r_667243 : RangeOk getRow 2051521 667243 667309 := by
  decide +kernel

private theorem r_667309 : RangeOk getRow 2051521 667309 667378 := by
  decide +kernel

private theorem r_667378 : RangeOk getRow 2051521 667378 667447 := by
  decide +kernel

private theorem r_667447 : RangeOk getRow 2051521 667447 667517 := by
  decide +kernel

private theorem r_667517 : RangeOk getRow 2051521 667517 667588 := by
  decide +kernel

private theorem r_667588 : RangeOk getRow 2051521 667588 667658 := by
  decide +kernel

private theorem r_667658 : RangeOk getRow 2051521 667658 667726 := by
  decide +kernel

private theorem r_667726 : RangeOk getRow 2051521 667726 667793 := by
  decide +kernel

private theorem r_667793 : RangeOk getRow 2051521 667793 667860 := by
  decide +kernel

private theorem r_667860 : RangeOk getRow 2051521 667860 667929 := by
  decide +kernel

private theorem r_667929 : RangeOk getRow 2051521 667929 667994 := by
  decide +kernel

private theorem r_667994 : RangeOk getRow 2051521 667994 668059 := by
  decide +kernel

private theorem r_668059 : RangeOk getRow 2051521 668059 668127 := by
  decide +kernel

private theorem r_668127 : RangeOk getRow 2051521 668127 668196 := by
  decide +kernel

private theorem r_668196 : RangeOk getRow 2051521 668196 668265 := by
  decide +kernel

private theorem r_668265 : RangeOk getRow 2051521 668265 668333 := by
  decide +kernel

private theorem r_668333 : RangeOk getRow 2051521 668333 668404 := by
  decide +kernel

private theorem r_668404 : RangeOk getRow 2051521 668404 668472 := by
  decide +kernel

private theorem r_668472 : RangeOk getRow 2051521 668472 668539 := by
  decide +kernel

private theorem r_668539 : RangeOk getRow 2051521 668539 668605 := by
  decide +kernel

private theorem r_668605 : RangeOk getRow 2051521 668605 668670 := by
  decide +kernel

private theorem r_668670 : RangeOk getRow 2051521 668670 668735 := by
  decide +kernel

private theorem r_668735 : RangeOk getRow 2051521 668735 668805 := by
  decide +kernel

private theorem r_668805 : RangeOk getRow 2051521 668805 668875 := by
  decide +kernel

private theorem r_668875 : RangeOk getRow 2051521 668875 668943 := by
  decide +kernel

private theorem r_668943 : RangeOk getRow 2051521 668943 669011 := by
  decide +kernel

private theorem r_669011 : RangeOk getRow 2051521 669011 669077 := by
  decide +kernel

private theorem r_669077 : RangeOk getRow 2051521 669077 669144 := by
  decide +kernel

private theorem r_669144 : RangeOk getRow 2051521 669144 669209 := by
  decide +kernel

private theorem s_666909 : RangeOk getRow 2051521 666840 666909 := r_666840
private theorem s_666977 : RangeOk getRow 2051521 666840 666977 :=
  s_666909.append (by norm_num) r_666909
private theorem s_667043 : RangeOk getRow 2051521 666840 667043 :=
  s_666977.append (by norm_num) r_666977
private theorem s_667112 : RangeOk getRow 2051521 666840 667112 :=
  s_667043.append (by norm_num) r_667043
private theorem s_667179 : RangeOk getRow 2051521 666840 667179 :=
  s_667112.append (by norm_num) r_667112
private theorem s_667243 : RangeOk getRow 2051521 666840 667243 :=
  s_667179.append (by norm_num) r_667179
private theorem s_667309 : RangeOk getRow 2051521 666840 667309 :=
  s_667243.append (by norm_num) r_667243
private theorem s_667378 : RangeOk getRow 2051521 666840 667378 :=
  s_667309.append (by norm_num) r_667309
private theorem s_667447 : RangeOk getRow 2051521 666840 667447 :=
  s_667378.append (by norm_num) r_667378
private theorem s_667517 : RangeOk getRow 2051521 666840 667517 :=
  s_667447.append (by norm_num) r_667447
private theorem s_667588 : RangeOk getRow 2051521 666840 667588 :=
  s_667517.append (by norm_num) r_667517
private theorem s_667658 : RangeOk getRow 2051521 666840 667658 :=
  s_667588.append (by norm_num) r_667588
private theorem s_667726 : RangeOk getRow 2051521 666840 667726 :=
  s_667658.append (by norm_num) r_667658
private theorem s_667793 : RangeOk getRow 2051521 666840 667793 :=
  s_667726.append (by norm_num) r_667726
private theorem s_667860 : RangeOk getRow 2051521 666840 667860 :=
  s_667793.append (by norm_num) r_667793
private theorem s_667929 : RangeOk getRow 2051521 666840 667929 :=
  s_667860.append (by norm_num) r_667860
private theorem s_667994 : RangeOk getRow 2051521 666840 667994 :=
  s_667929.append (by norm_num) r_667929
private theorem s_668059 : RangeOk getRow 2051521 666840 668059 :=
  s_667994.append (by norm_num) r_667994
private theorem s_668127 : RangeOk getRow 2051521 666840 668127 :=
  s_668059.append (by norm_num) r_668059
private theorem s_668196 : RangeOk getRow 2051521 666840 668196 :=
  s_668127.append (by norm_num) r_668127
private theorem s_668265 : RangeOk getRow 2051521 666840 668265 :=
  s_668196.append (by norm_num) r_668196
private theorem s_668333 : RangeOk getRow 2051521 666840 668333 :=
  s_668265.append (by norm_num) r_668265
private theorem s_668404 : RangeOk getRow 2051521 666840 668404 :=
  s_668333.append (by norm_num) r_668333
private theorem s_668472 : RangeOk getRow 2051521 666840 668472 :=
  s_668404.append (by norm_num) r_668404
private theorem s_668539 : RangeOk getRow 2051521 666840 668539 :=
  s_668472.append (by norm_num) r_668472
private theorem s_668605 : RangeOk getRow 2051521 666840 668605 :=
  s_668539.append (by norm_num) r_668539
private theorem s_668670 : RangeOk getRow 2051521 666840 668670 :=
  s_668605.append (by norm_num) r_668605
private theorem s_668735 : RangeOk getRow 2051521 666840 668735 :=
  s_668670.append (by norm_num) r_668670
private theorem s_668805 : RangeOk getRow 2051521 666840 668805 :=
  s_668735.append (by norm_num) r_668735
private theorem s_668875 : RangeOk getRow 2051521 666840 668875 :=
  s_668805.append (by norm_num) r_668805
private theorem s_668943 : RangeOk getRow 2051521 666840 668943 :=
  s_668875.append (by norm_num) r_668875
private theorem s_669011 : RangeOk getRow 2051521 666840 669011 :=
  s_668943.append (by norm_num) r_668943
private theorem s_669077 : RangeOk getRow 2051521 666840 669077 :=
  s_669011.append (by norm_num) r_669011
private theorem s_669144 : RangeOk getRow 2051521 666840 669144 :=
  s_669077.append (by norm_num) r_669077
private theorem s_669209 : RangeOk getRow 2051521 666840 669209 :=
  s_669144.append (by norm_num) r_669144

/-- Rows `[666840, 669209)` are valid. -/
theorem rangeOk_666840_669209 : RangeOk getRow 2051521 666840 669209 := s_669209

end Noperthedron.Solution
