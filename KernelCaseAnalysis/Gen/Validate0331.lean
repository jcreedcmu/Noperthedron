import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[796865, 799080). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_796865 : RangeOk getRow 2051521 796865 796932 := by
  decide +kernel

private theorem r_796932 : RangeOk getRow 2051521 796932 796998 := by
  decide +kernel

private theorem r_796998 : RangeOk getRow 2051521 796998 797063 := by
  decide +kernel

private theorem r_797063 : RangeOk getRow 2051521 797063 797130 := by
  decide +kernel

private theorem r_797130 : RangeOk getRow 2051521 797130 797198 := by
  decide +kernel

private theorem r_797198 : RangeOk getRow 2051521 797198 797266 := by
  decide +kernel

private theorem r_797266 : RangeOk getRow 2051521 797266 797334 := by
  decide +kernel

private theorem r_797334 : RangeOk getRow 2051521 797334 797400 := by
  decide +kernel

private theorem r_797400 : RangeOk getRow 2051521 797400 797468 := by
  decide +kernel

private theorem r_797468 : RangeOk getRow 2051521 797468 797535 := by
  decide +kernel

private theorem r_797535 : RangeOk getRow 2051521 797535 797599 := by
  decide +kernel

private theorem r_797599 : RangeOk getRow 2051521 797599 797666 := by
  decide +kernel

private theorem r_797666 : RangeOk getRow 2051521 797666 797733 := by
  decide +kernel

private theorem r_797733 : RangeOk getRow 2051521 797733 797801 := by
  decide +kernel

private theorem r_797801 : RangeOk getRow 2051521 797801 797869 := by
  decide +kernel

private theorem r_797869 : RangeOk getRow 2051521 797869 797935 := by
  decide +kernel

private theorem r_797935 : RangeOk getRow 2051521 797935 798002 := by
  decide +kernel

private theorem r_798002 : RangeOk getRow 2051521 798002 798066 := by
  decide +kernel

private theorem r_798066 : RangeOk getRow 2051521 798066 798132 := by
  decide +kernel

private theorem r_798132 : RangeOk getRow 2051521 798132 798201 := by
  decide +kernel

private theorem r_798201 : RangeOk getRow 2051521 798201 798267 := by
  decide +kernel

private theorem r_798267 : RangeOk getRow 2051521 798267 798332 := by
  decide +kernel

private theorem r_798332 : RangeOk getRow 2051521 798332 798401 := by
  decide +kernel

private theorem r_798401 : RangeOk getRow 2051521 798401 798470 := by
  decide +kernel

private theorem r_798470 : RangeOk getRow 2051521 798470 798538 := by
  decide +kernel

private theorem r_798538 : RangeOk getRow 2051521 798538 798607 := by
  decide +kernel

private theorem r_798607 : RangeOk getRow 2051521 798607 798675 := by
  decide +kernel

private theorem r_798675 : RangeOk getRow 2051521 798675 798740 := by
  decide +kernel

private theorem r_798740 : RangeOk getRow 2051521 798740 798807 := by
  decide +kernel

private theorem r_798807 : RangeOk getRow 2051521 798807 798874 := by
  decide +kernel

private theorem r_798874 : RangeOk getRow 2051521 798874 798942 := by
  decide +kernel

private theorem r_798942 : RangeOk getRow 2051521 798942 799012 := by
  decide +kernel

private theorem r_799012 : RangeOk getRow 2051521 799012 799080 := by
  decide +kernel

private theorem s_796932 : RangeOk getRow 2051521 796865 796932 := r_796865
private theorem s_796998 : RangeOk getRow 2051521 796865 796998 :=
  s_796932.append (by norm_num) r_796932
private theorem s_797063 : RangeOk getRow 2051521 796865 797063 :=
  s_796998.append (by norm_num) r_796998
private theorem s_797130 : RangeOk getRow 2051521 796865 797130 :=
  s_797063.append (by norm_num) r_797063
private theorem s_797198 : RangeOk getRow 2051521 796865 797198 :=
  s_797130.append (by norm_num) r_797130
private theorem s_797266 : RangeOk getRow 2051521 796865 797266 :=
  s_797198.append (by norm_num) r_797198
private theorem s_797334 : RangeOk getRow 2051521 796865 797334 :=
  s_797266.append (by norm_num) r_797266
private theorem s_797400 : RangeOk getRow 2051521 796865 797400 :=
  s_797334.append (by norm_num) r_797334
private theorem s_797468 : RangeOk getRow 2051521 796865 797468 :=
  s_797400.append (by norm_num) r_797400
private theorem s_797535 : RangeOk getRow 2051521 796865 797535 :=
  s_797468.append (by norm_num) r_797468
private theorem s_797599 : RangeOk getRow 2051521 796865 797599 :=
  s_797535.append (by norm_num) r_797535
private theorem s_797666 : RangeOk getRow 2051521 796865 797666 :=
  s_797599.append (by norm_num) r_797599
private theorem s_797733 : RangeOk getRow 2051521 796865 797733 :=
  s_797666.append (by norm_num) r_797666
private theorem s_797801 : RangeOk getRow 2051521 796865 797801 :=
  s_797733.append (by norm_num) r_797733
private theorem s_797869 : RangeOk getRow 2051521 796865 797869 :=
  s_797801.append (by norm_num) r_797801
private theorem s_797935 : RangeOk getRow 2051521 796865 797935 :=
  s_797869.append (by norm_num) r_797869
private theorem s_798002 : RangeOk getRow 2051521 796865 798002 :=
  s_797935.append (by norm_num) r_797935
private theorem s_798066 : RangeOk getRow 2051521 796865 798066 :=
  s_798002.append (by norm_num) r_798002
private theorem s_798132 : RangeOk getRow 2051521 796865 798132 :=
  s_798066.append (by norm_num) r_798066
private theorem s_798201 : RangeOk getRow 2051521 796865 798201 :=
  s_798132.append (by norm_num) r_798132
private theorem s_798267 : RangeOk getRow 2051521 796865 798267 :=
  s_798201.append (by norm_num) r_798201
private theorem s_798332 : RangeOk getRow 2051521 796865 798332 :=
  s_798267.append (by norm_num) r_798267
private theorem s_798401 : RangeOk getRow 2051521 796865 798401 :=
  s_798332.append (by norm_num) r_798332
private theorem s_798470 : RangeOk getRow 2051521 796865 798470 :=
  s_798401.append (by norm_num) r_798401
private theorem s_798538 : RangeOk getRow 2051521 796865 798538 :=
  s_798470.append (by norm_num) r_798470
private theorem s_798607 : RangeOk getRow 2051521 796865 798607 :=
  s_798538.append (by norm_num) r_798538
private theorem s_798675 : RangeOk getRow 2051521 796865 798675 :=
  s_798607.append (by norm_num) r_798607
private theorem s_798740 : RangeOk getRow 2051521 796865 798740 :=
  s_798675.append (by norm_num) r_798675
private theorem s_798807 : RangeOk getRow 2051521 796865 798807 :=
  s_798740.append (by norm_num) r_798740
private theorem s_798874 : RangeOk getRow 2051521 796865 798874 :=
  s_798807.append (by norm_num) r_798807
private theorem s_798942 : RangeOk getRow 2051521 796865 798942 :=
  s_798874.append (by norm_num) r_798874
private theorem s_799012 : RangeOk getRow 2051521 796865 799012 :=
  s_798942.append (by norm_num) r_798942
private theorem s_799080 : RangeOk getRow 2051521 796865 799080 :=
  s_799012.append (by norm_num) r_799012

/-- Rows `[796865, 799080)` are valid. -/
theorem rangeOk_796865_799080 : RangeOk getRow 2051521 796865 799080 := s_799080

end Noperthedron.Solution
