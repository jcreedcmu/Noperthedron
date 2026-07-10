import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[385173, 387388). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_385173 : RangeOk getRow 2051521 385173 385240 := by
  decide +kernel

private theorem r_385240 : RangeOk getRow 2051521 385240 385308 := by
  decide +kernel

private theorem r_385308 : RangeOk getRow 2051521 385308 385375 := by
  decide +kernel

private theorem r_385375 : RangeOk getRow 2051521 385375 385441 := by
  decide +kernel

private theorem r_385441 : RangeOk getRow 2051521 385441 385506 := by
  decide +kernel

private theorem r_385506 : RangeOk getRow 2051521 385506 385572 := by
  decide +kernel

private theorem r_385572 : RangeOk getRow 2051521 385572 385640 := by
  decide +kernel

private theorem r_385640 : RangeOk getRow 2051521 385640 385706 := by
  decide +kernel

private theorem r_385706 : RangeOk getRow 2051521 385706 385772 := by
  decide +kernel

private theorem r_385772 : RangeOk getRow 2051521 385772 385840 := by
  decide +kernel

private theorem r_385840 : RangeOk getRow 2051521 385840 385907 := by
  decide +kernel

private theorem r_385907 : RangeOk getRow 2051521 385907 385973 := by
  decide +kernel

private theorem r_385973 : RangeOk getRow 2051521 385973 386039 := by
  decide +kernel

private theorem r_386039 : RangeOk getRow 2051521 386039 386105 := by
  decide +kernel

private theorem r_386105 : RangeOk getRow 2051521 386105 386172 := by
  decide +kernel

private theorem r_386172 : RangeOk getRow 2051521 386172 386239 := by
  decide +kernel

private theorem r_386239 : RangeOk getRow 2051521 386239 386306 := by
  decide +kernel

private theorem r_386306 : RangeOk getRow 2051521 386306 386372 := by
  decide +kernel

private theorem r_386372 : RangeOk getRow 2051521 386372 386437 := by
  decide +kernel

private theorem r_386437 : RangeOk getRow 2051521 386437 386501 := by
  decide +kernel

private theorem r_386501 : RangeOk getRow 2051521 386501 386566 := by
  decide +kernel

private theorem r_386566 : RangeOk getRow 2051521 386566 386632 := by
  decide +kernel

private theorem r_386632 : RangeOk getRow 2051521 386632 386700 := by
  decide +kernel

private theorem r_386700 : RangeOk getRow 2051521 386700 386768 := by
  decide +kernel

private theorem r_386768 : RangeOk getRow 2051521 386768 386838 := by
  decide +kernel

private theorem r_386838 : RangeOk getRow 2051521 386838 386908 := by
  decide +kernel

private theorem r_386908 : RangeOk getRow 2051521 386908 386978 := by
  decide +kernel

private theorem r_386978 : RangeOk getRow 2051521 386978 387047 := by
  decide +kernel

private theorem r_387047 : RangeOk getRow 2051521 387047 387116 := by
  decide +kernel

private theorem r_387116 : RangeOk getRow 2051521 387116 387184 := by
  decide +kernel

private theorem r_387184 : RangeOk getRow 2051521 387184 387254 := by
  decide +kernel

private theorem r_387254 : RangeOk getRow 2051521 387254 387321 := by
  decide +kernel

private theorem r_387321 : RangeOk getRow 2051521 387321 387388 := by
  decide +kernel

private theorem s_385240 : RangeOk getRow 2051521 385173 385240 := r_385173
private theorem s_385308 : RangeOk getRow 2051521 385173 385308 :=
  s_385240.append (by norm_num) r_385240
private theorem s_385375 : RangeOk getRow 2051521 385173 385375 :=
  s_385308.append (by norm_num) r_385308
private theorem s_385441 : RangeOk getRow 2051521 385173 385441 :=
  s_385375.append (by norm_num) r_385375
private theorem s_385506 : RangeOk getRow 2051521 385173 385506 :=
  s_385441.append (by norm_num) r_385441
private theorem s_385572 : RangeOk getRow 2051521 385173 385572 :=
  s_385506.append (by norm_num) r_385506
private theorem s_385640 : RangeOk getRow 2051521 385173 385640 :=
  s_385572.append (by norm_num) r_385572
private theorem s_385706 : RangeOk getRow 2051521 385173 385706 :=
  s_385640.append (by norm_num) r_385640
private theorem s_385772 : RangeOk getRow 2051521 385173 385772 :=
  s_385706.append (by norm_num) r_385706
private theorem s_385840 : RangeOk getRow 2051521 385173 385840 :=
  s_385772.append (by norm_num) r_385772
private theorem s_385907 : RangeOk getRow 2051521 385173 385907 :=
  s_385840.append (by norm_num) r_385840
private theorem s_385973 : RangeOk getRow 2051521 385173 385973 :=
  s_385907.append (by norm_num) r_385907
private theorem s_386039 : RangeOk getRow 2051521 385173 386039 :=
  s_385973.append (by norm_num) r_385973
private theorem s_386105 : RangeOk getRow 2051521 385173 386105 :=
  s_386039.append (by norm_num) r_386039
private theorem s_386172 : RangeOk getRow 2051521 385173 386172 :=
  s_386105.append (by norm_num) r_386105
private theorem s_386239 : RangeOk getRow 2051521 385173 386239 :=
  s_386172.append (by norm_num) r_386172
private theorem s_386306 : RangeOk getRow 2051521 385173 386306 :=
  s_386239.append (by norm_num) r_386239
private theorem s_386372 : RangeOk getRow 2051521 385173 386372 :=
  s_386306.append (by norm_num) r_386306
private theorem s_386437 : RangeOk getRow 2051521 385173 386437 :=
  s_386372.append (by norm_num) r_386372
private theorem s_386501 : RangeOk getRow 2051521 385173 386501 :=
  s_386437.append (by norm_num) r_386437
private theorem s_386566 : RangeOk getRow 2051521 385173 386566 :=
  s_386501.append (by norm_num) r_386501
private theorem s_386632 : RangeOk getRow 2051521 385173 386632 :=
  s_386566.append (by norm_num) r_386566
private theorem s_386700 : RangeOk getRow 2051521 385173 386700 :=
  s_386632.append (by norm_num) r_386632
private theorem s_386768 : RangeOk getRow 2051521 385173 386768 :=
  s_386700.append (by norm_num) r_386700
private theorem s_386838 : RangeOk getRow 2051521 385173 386838 :=
  s_386768.append (by norm_num) r_386768
private theorem s_386908 : RangeOk getRow 2051521 385173 386908 :=
  s_386838.append (by norm_num) r_386838
private theorem s_386978 : RangeOk getRow 2051521 385173 386978 :=
  s_386908.append (by norm_num) r_386908
private theorem s_387047 : RangeOk getRow 2051521 385173 387047 :=
  s_386978.append (by norm_num) r_386978
private theorem s_387116 : RangeOk getRow 2051521 385173 387116 :=
  s_387047.append (by norm_num) r_387047
private theorem s_387184 : RangeOk getRow 2051521 385173 387184 :=
  s_387116.append (by norm_num) r_387116
private theorem s_387254 : RangeOk getRow 2051521 385173 387254 :=
  s_387184.append (by norm_num) r_387184
private theorem s_387321 : RangeOk getRow 2051521 385173 387321 :=
  s_387254.append (by norm_num) r_387254
private theorem s_387388 : RangeOk getRow 2051521 385173 387388 :=
  s_387321.append (by norm_num) r_387321

/-- Rows `[385173, 387388)` are valid. -/
theorem rangeOk_385173_387388 : RangeOk getRow 2051521 385173 387388 := s_387388

end Noperthedron.Solution
