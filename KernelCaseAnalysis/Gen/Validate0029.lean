import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[60848, 64211). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_60848 : RangeOk getRow 2051521 60848 60913 := by
  decide +kernel

private theorem r_60913 : RangeOk getRow 2051521 60913 60989 := by
  decide +kernel

private theorem r_60989 : RangeOk getRow 2051521 60989 61060 := by
  decide +kernel

private theorem r_61060 : RangeOk getRow 2051521 61060 61120 := by
  decide +kernel

private theorem r_61120 : RangeOk getRow 2051521 61120 61194 := by
  decide +kernel

private theorem r_61194 : RangeOk getRow 2051521 61194 61266 := by
  decide +kernel

private theorem r_61266 : RangeOk getRow 2051521 61266 61330 := by
  decide +kernel

private theorem r_61330 : RangeOk getRow 2051521 61330 61401 := by
  decide +kernel

private theorem r_61401 : RangeOk getRow 2051521 61401 61470 := by
  decide +kernel

private theorem r_61470 : RangeOk getRow 2051521 61470 61540 := by
  decide +kernel

private theorem r_61540 : RangeOk getRow 2051521 61540 61614 := by
  decide +kernel

private theorem r_61614 : RangeOk getRow 2051521 61614 61688 := by
  decide +kernel

private theorem r_61688 : RangeOk getRow 2051521 61688 61753 := by
  decide +kernel

private theorem r_61753 : RangeOk getRow 2051521 61753 61819 := by
  decide +kernel

private theorem r_61819 : RangeOk getRow 2051521 61819 61895 := by
  decide +kernel

private theorem r_61895 : RangeOk getRow 2051521 61895 61950 := by
  decide +kernel

private theorem r_61950 : RangeOk getRow 2051521 61950 62015 := by
  decide +kernel

private theorem r_62015 : RangeOk getRow 2051521 62015 62088 := by
  decide +kernel

private theorem r_62088 : RangeOk getRow 2051521 62088 62158 := by
  decide +kernel

private theorem r_62158 : RangeOk getRow 2051521 62158 62222 := by
  decide +kernel

private theorem r_62222 : RangeOk getRow 2051521 62222 62291 := by
  decide +kernel

private theorem r_62291 : RangeOk getRow 2051521 62291 62367 := by
  decide +kernel

private theorem r_62367 : RangeOk getRow 2051521 62367 62438 := by
  decide +kernel

private theorem r_62438 : RangeOk getRow 2051521 62438 62513 := by
  decide +kernel

private theorem r_62513 : RangeOk getRow 2051521 62513 62585 := by
  decide +kernel

private theorem r_62585 : RangeOk getRow 2051521 62585 62652 := by
  decide +kernel

private theorem r_62652 : RangeOk getRow 2051521 62652 62718 := by
  decide +kernel

private theorem r_62718 : RangeOk getRow 2051521 62718 62794 := by
  decide +kernel

private theorem r_62794 : RangeOk getRow 2051521 62794 62870 := by
  decide +kernel

private theorem r_62870 : RangeOk getRow 2051521 62870 62935 := by
  decide +kernel

private theorem r_62935 : RangeOk getRow 2051521 62935 63007 := by
  decide +kernel

private theorem r_63007 : RangeOk getRow 2051521 63007 63077 := by
  decide +kernel

private theorem r_63077 : RangeOk getRow 2051521 63077 63141 := by
  decide +kernel

private theorem r_63141 : RangeOk getRow 2051521 63141 63214 := by
  decide +kernel

private theorem r_63214 : RangeOk getRow 2051521 63214 63290 := by
  decide +kernel

private theorem r_63290 : RangeOk getRow 2051521 63290 63365 := by
  decide +kernel

private theorem r_63365 : RangeOk getRow 2051521 63365 63439 := by
  decide +kernel

private theorem r_63439 : RangeOk getRow 2051521 63439 63509 := by
  decide +kernel

private theorem r_63509 : RangeOk getRow 2051521 63509 63573 := by
  decide +kernel

private theorem r_63573 : RangeOk getRow 2051521 63573 63643 := by
  decide +kernel

private theorem r_63643 : RangeOk getRow 2051521 63643 63719 := by
  decide +kernel

private theorem r_63719 : RangeOk getRow 2051521 63719 63793 := by
  decide +kernel

private theorem r_63793 : RangeOk getRow 2051521 63793 63862 := by
  decide +kernel

private theorem r_63862 : RangeOk getRow 2051521 63862 63930 := by
  decide +kernel

private theorem r_63930 : RangeOk getRow 2051521 63930 63995 := by
  decide +kernel

private theorem r_63995 : RangeOk getRow 2051521 63995 64059 := by
  decide +kernel

private theorem r_64059 : RangeOk getRow 2051521 64059 64135 := by
  decide +kernel

private theorem r_64135 : RangeOk getRow 2051521 64135 64211 := by
  decide +kernel

private theorem s_60913 : RangeOk getRow 2051521 60848 60913 := r_60848
private theorem s_60989 : RangeOk getRow 2051521 60848 60989 :=
  s_60913.append (by norm_num) r_60913
private theorem s_61060 : RangeOk getRow 2051521 60848 61060 :=
  s_60989.append (by norm_num) r_60989
private theorem s_61120 : RangeOk getRow 2051521 60848 61120 :=
  s_61060.append (by norm_num) r_61060
private theorem s_61194 : RangeOk getRow 2051521 60848 61194 :=
  s_61120.append (by norm_num) r_61120
private theorem s_61266 : RangeOk getRow 2051521 60848 61266 :=
  s_61194.append (by norm_num) r_61194
private theorem s_61330 : RangeOk getRow 2051521 60848 61330 :=
  s_61266.append (by norm_num) r_61266
private theorem s_61401 : RangeOk getRow 2051521 60848 61401 :=
  s_61330.append (by norm_num) r_61330
private theorem s_61470 : RangeOk getRow 2051521 60848 61470 :=
  s_61401.append (by norm_num) r_61401
private theorem s_61540 : RangeOk getRow 2051521 60848 61540 :=
  s_61470.append (by norm_num) r_61470
private theorem s_61614 : RangeOk getRow 2051521 60848 61614 :=
  s_61540.append (by norm_num) r_61540
private theorem s_61688 : RangeOk getRow 2051521 60848 61688 :=
  s_61614.append (by norm_num) r_61614
private theorem s_61753 : RangeOk getRow 2051521 60848 61753 :=
  s_61688.append (by norm_num) r_61688
private theorem s_61819 : RangeOk getRow 2051521 60848 61819 :=
  s_61753.append (by norm_num) r_61753
private theorem s_61895 : RangeOk getRow 2051521 60848 61895 :=
  s_61819.append (by norm_num) r_61819
private theorem s_61950 : RangeOk getRow 2051521 60848 61950 :=
  s_61895.append (by norm_num) r_61895
private theorem s_62015 : RangeOk getRow 2051521 60848 62015 :=
  s_61950.append (by norm_num) r_61950
private theorem s_62088 : RangeOk getRow 2051521 60848 62088 :=
  s_62015.append (by norm_num) r_62015
private theorem s_62158 : RangeOk getRow 2051521 60848 62158 :=
  s_62088.append (by norm_num) r_62088
private theorem s_62222 : RangeOk getRow 2051521 60848 62222 :=
  s_62158.append (by norm_num) r_62158
private theorem s_62291 : RangeOk getRow 2051521 60848 62291 :=
  s_62222.append (by norm_num) r_62222
private theorem s_62367 : RangeOk getRow 2051521 60848 62367 :=
  s_62291.append (by norm_num) r_62291
private theorem s_62438 : RangeOk getRow 2051521 60848 62438 :=
  s_62367.append (by norm_num) r_62367
private theorem s_62513 : RangeOk getRow 2051521 60848 62513 :=
  s_62438.append (by norm_num) r_62438
private theorem s_62585 : RangeOk getRow 2051521 60848 62585 :=
  s_62513.append (by norm_num) r_62513
private theorem s_62652 : RangeOk getRow 2051521 60848 62652 :=
  s_62585.append (by norm_num) r_62585
private theorem s_62718 : RangeOk getRow 2051521 60848 62718 :=
  s_62652.append (by norm_num) r_62652
private theorem s_62794 : RangeOk getRow 2051521 60848 62794 :=
  s_62718.append (by norm_num) r_62718
private theorem s_62870 : RangeOk getRow 2051521 60848 62870 :=
  s_62794.append (by norm_num) r_62794
private theorem s_62935 : RangeOk getRow 2051521 60848 62935 :=
  s_62870.append (by norm_num) r_62870
private theorem s_63007 : RangeOk getRow 2051521 60848 63007 :=
  s_62935.append (by norm_num) r_62935
private theorem s_63077 : RangeOk getRow 2051521 60848 63077 :=
  s_63007.append (by norm_num) r_63007
private theorem s_63141 : RangeOk getRow 2051521 60848 63141 :=
  s_63077.append (by norm_num) r_63077
private theorem s_63214 : RangeOk getRow 2051521 60848 63214 :=
  s_63141.append (by norm_num) r_63141
private theorem s_63290 : RangeOk getRow 2051521 60848 63290 :=
  s_63214.append (by norm_num) r_63214
private theorem s_63365 : RangeOk getRow 2051521 60848 63365 :=
  s_63290.append (by norm_num) r_63290
private theorem s_63439 : RangeOk getRow 2051521 60848 63439 :=
  s_63365.append (by norm_num) r_63365
private theorem s_63509 : RangeOk getRow 2051521 60848 63509 :=
  s_63439.append (by norm_num) r_63439
private theorem s_63573 : RangeOk getRow 2051521 60848 63573 :=
  s_63509.append (by norm_num) r_63509
private theorem s_63643 : RangeOk getRow 2051521 60848 63643 :=
  s_63573.append (by norm_num) r_63573
private theorem s_63719 : RangeOk getRow 2051521 60848 63719 :=
  s_63643.append (by norm_num) r_63643
private theorem s_63793 : RangeOk getRow 2051521 60848 63793 :=
  s_63719.append (by norm_num) r_63719
private theorem s_63862 : RangeOk getRow 2051521 60848 63862 :=
  s_63793.append (by norm_num) r_63793
private theorem s_63930 : RangeOk getRow 2051521 60848 63930 :=
  s_63862.append (by norm_num) r_63862
private theorem s_63995 : RangeOk getRow 2051521 60848 63995 :=
  s_63930.append (by norm_num) r_63930
private theorem s_64059 : RangeOk getRow 2051521 60848 64059 :=
  s_63995.append (by norm_num) r_63995
private theorem s_64135 : RangeOk getRow 2051521 60848 64135 :=
  s_64059.append (by norm_num) r_64059
private theorem s_64211 : RangeOk getRow 2051521 60848 64211 :=
  s_64135.append (by norm_num) r_64135

/-- Rows `[60848, 64211)` are valid. -/
theorem rangeOk_60848_64211 : RangeOk getRow 2051521 60848 64211 := s_64211

end Noperthedron.Solution
