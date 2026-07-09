import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[127473, 130306). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_127473 : RangeOk getRow 2051521 127473 127542 := by
  decide +kernel

private theorem r_127542 : RangeOk getRow 2051521 127542 127615 := by
  decide +kernel

private theorem r_127615 : RangeOk getRow 2051521 127615 127690 := by
  decide +kernel

private theorem r_127690 : RangeOk getRow 2051521 127690 127760 := by
  decide +kernel

private theorem r_127760 : RangeOk getRow 2051521 127760 127831 := by
  decide +kernel

private theorem r_127831 : RangeOk getRow 2051521 127831 127898 := by
  decide +kernel

private theorem r_127898 : RangeOk getRow 2051521 127898 127962 := by
  decide +kernel

private theorem r_127962 : RangeOk getRow 2051521 127962 128035 := by
  decide +kernel

private theorem r_128035 : RangeOk getRow 2051521 128035 128107 := by
  decide +kernel

private theorem r_128107 : RangeOk getRow 2051521 128107 128177 := by
  decide +kernel

private theorem r_128177 : RangeOk getRow 2051521 128177 128248 := by
  decide +kernel

private theorem r_128248 : RangeOk getRow 2051521 128248 128316 := by
  decide +kernel

private theorem r_128316 : RangeOk getRow 2051521 128316 128380 := by
  decide +kernel

private theorem r_128380 : RangeOk getRow 2051521 128380 128450 := by
  decide +kernel

private theorem r_128450 : RangeOk getRow 2051521 128450 128518 := by
  decide +kernel

private theorem r_128518 : RangeOk getRow 2051521 128518 128582 := by
  decide +kernel

private theorem r_128582 : RangeOk getRow 2051521 128582 128654 := by
  decide +kernel

private theorem r_128654 : RangeOk getRow 2051521 128654 128723 := by
  decide +kernel

private theorem r_128723 : RangeOk getRow 2051521 128723 128791 := by
  decide +kernel

private theorem r_128791 : RangeOk getRow 2051521 128791 128855 := by
  decide +kernel

private theorem r_128855 : RangeOk getRow 2051521 128855 128929 := by
  decide +kernel

private theorem r_128929 : RangeOk getRow 2051521 128929 128999 := by
  decide +kernel

private theorem r_128999 : RangeOk getRow 2051521 128999 129072 := by
  decide +kernel

private theorem r_129072 : RangeOk getRow 2051521 129072 129142 := by
  decide +kernel

private theorem r_129142 : RangeOk getRow 2051521 129142 129211 := by
  decide +kernel

private theorem r_129211 : RangeOk getRow 2051521 129211 129275 := by
  decide +kernel

private theorem r_129275 : RangeOk getRow 2051521 129275 129344 := by
  decide +kernel

private theorem r_129344 : RangeOk getRow 2051521 129344 129413 := by
  decide +kernel

private theorem r_129413 : RangeOk getRow 2051521 129413 129487 := by
  decide +kernel

private theorem r_129487 : RangeOk getRow 2051521 129487 129557 := by
  decide +kernel

private theorem r_129557 : RangeOk getRow 2051521 129557 129626 := by
  decide +kernel

private theorem r_129626 : RangeOk getRow 2051521 129626 129693 := by
  decide +kernel

private theorem r_129693 : RangeOk getRow 2051521 129693 129757 := by
  decide +kernel

private theorem r_129757 : RangeOk getRow 2051521 129757 129831 := by
  decide +kernel

private theorem r_129831 : RangeOk getRow 2051521 129831 129904 := by
  decide +kernel

private theorem r_129904 : RangeOk getRow 2051521 129904 129975 := by
  decide +kernel

private theorem r_129975 : RangeOk getRow 2051521 129975 130045 := by
  decide +kernel

private theorem r_130045 : RangeOk getRow 2051521 130045 130114 := by
  decide +kernel

private theorem r_130114 : RangeOk getRow 2051521 130114 130178 := by
  decide +kernel

private theorem r_130178 : RangeOk getRow 2051521 130178 130242 := by
  decide +kernel

private theorem r_130242 : RangeOk getRow 2051521 130242 130306 := by
  decide +kernel

private theorem s_127542 : RangeOk getRow 2051521 127473 127542 := r_127473
private theorem s_127615 : RangeOk getRow 2051521 127473 127615 :=
  s_127542.append (by norm_num) r_127542
private theorem s_127690 : RangeOk getRow 2051521 127473 127690 :=
  s_127615.append (by norm_num) r_127615
private theorem s_127760 : RangeOk getRow 2051521 127473 127760 :=
  s_127690.append (by norm_num) r_127690
private theorem s_127831 : RangeOk getRow 2051521 127473 127831 :=
  s_127760.append (by norm_num) r_127760
private theorem s_127898 : RangeOk getRow 2051521 127473 127898 :=
  s_127831.append (by norm_num) r_127831
private theorem s_127962 : RangeOk getRow 2051521 127473 127962 :=
  s_127898.append (by norm_num) r_127898
private theorem s_128035 : RangeOk getRow 2051521 127473 128035 :=
  s_127962.append (by norm_num) r_127962
private theorem s_128107 : RangeOk getRow 2051521 127473 128107 :=
  s_128035.append (by norm_num) r_128035
private theorem s_128177 : RangeOk getRow 2051521 127473 128177 :=
  s_128107.append (by norm_num) r_128107
private theorem s_128248 : RangeOk getRow 2051521 127473 128248 :=
  s_128177.append (by norm_num) r_128177
private theorem s_128316 : RangeOk getRow 2051521 127473 128316 :=
  s_128248.append (by norm_num) r_128248
private theorem s_128380 : RangeOk getRow 2051521 127473 128380 :=
  s_128316.append (by norm_num) r_128316
private theorem s_128450 : RangeOk getRow 2051521 127473 128450 :=
  s_128380.append (by norm_num) r_128380
private theorem s_128518 : RangeOk getRow 2051521 127473 128518 :=
  s_128450.append (by norm_num) r_128450
private theorem s_128582 : RangeOk getRow 2051521 127473 128582 :=
  s_128518.append (by norm_num) r_128518
private theorem s_128654 : RangeOk getRow 2051521 127473 128654 :=
  s_128582.append (by norm_num) r_128582
private theorem s_128723 : RangeOk getRow 2051521 127473 128723 :=
  s_128654.append (by norm_num) r_128654
private theorem s_128791 : RangeOk getRow 2051521 127473 128791 :=
  s_128723.append (by norm_num) r_128723
private theorem s_128855 : RangeOk getRow 2051521 127473 128855 :=
  s_128791.append (by norm_num) r_128791
private theorem s_128929 : RangeOk getRow 2051521 127473 128929 :=
  s_128855.append (by norm_num) r_128855
private theorem s_128999 : RangeOk getRow 2051521 127473 128999 :=
  s_128929.append (by norm_num) r_128929
private theorem s_129072 : RangeOk getRow 2051521 127473 129072 :=
  s_128999.append (by norm_num) r_128999
private theorem s_129142 : RangeOk getRow 2051521 127473 129142 :=
  s_129072.append (by norm_num) r_129072
private theorem s_129211 : RangeOk getRow 2051521 127473 129211 :=
  s_129142.append (by norm_num) r_129142
private theorem s_129275 : RangeOk getRow 2051521 127473 129275 :=
  s_129211.append (by norm_num) r_129211
private theorem s_129344 : RangeOk getRow 2051521 127473 129344 :=
  s_129275.append (by norm_num) r_129275
private theorem s_129413 : RangeOk getRow 2051521 127473 129413 :=
  s_129344.append (by norm_num) r_129344
private theorem s_129487 : RangeOk getRow 2051521 127473 129487 :=
  s_129413.append (by norm_num) r_129413
private theorem s_129557 : RangeOk getRow 2051521 127473 129557 :=
  s_129487.append (by norm_num) r_129487
private theorem s_129626 : RangeOk getRow 2051521 127473 129626 :=
  s_129557.append (by norm_num) r_129557
private theorem s_129693 : RangeOk getRow 2051521 127473 129693 :=
  s_129626.append (by norm_num) r_129626
private theorem s_129757 : RangeOk getRow 2051521 127473 129757 :=
  s_129693.append (by norm_num) r_129693
private theorem s_129831 : RangeOk getRow 2051521 127473 129831 :=
  s_129757.append (by norm_num) r_129757
private theorem s_129904 : RangeOk getRow 2051521 127473 129904 :=
  s_129831.append (by norm_num) r_129831
private theorem s_129975 : RangeOk getRow 2051521 127473 129975 :=
  s_129904.append (by norm_num) r_129904
private theorem s_130045 : RangeOk getRow 2051521 127473 130045 :=
  s_129975.append (by norm_num) r_129975
private theorem s_130114 : RangeOk getRow 2051521 127473 130114 :=
  s_130045.append (by norm_num) r_130045
private theorem s_130178 : RangeOk getRow 2051521 127473 130178 :=
  s_130114.append (by norm_num) r_130114
private theorem s_130242 : RangeOk getRow 2051521 127473 130242 :=
  s_130178.append (by norm_num) r_130178
private theorem s_130306 : RangeOk getRow 2051521 127473 130306 :=
  s_130242.append (by norm_num) r_130242

/-- Rows `[127473, 130306)` are valid. -/
theorem rangeOk_127473_130306 : RangeOk getRow 2051521 127473 130306 := s_130306

end Noperthedron.Solution
