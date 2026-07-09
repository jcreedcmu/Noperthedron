import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[200378, 202106). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_200378 : RangeOk getRow 2051521 200378 200442 := by
  decide +kernel

private theorem r_200442 : RangeOk getRow 2051521 200442 200506 := by
  decide +kernel

private theorem r_200506 : RangeOk getRow 2051521 200506 200570 := by
  decide +kernel

private theorem r_200570 : RangeOk getRow 2051521 200570 200634 := by
  decide +kernel

private theorem r_200634 : RangeOk getRow 2051521 200634 200698 := by
  decide +kernel

private theorem r_200698 : RangeOk getRow 2051521 200698 200762 := by
  decide +kernel

private theorem r_200762 : RangeOk getRow 2051521 200762 200826 := by
  decide +kernel

private theorem r_200826 : RangeOk getRow 2051521 200826 200890 := by
  decide +kernel

private theorem r_200890 : RangeOk getRow 2051521 200890 200954 := by
  decide +kernel

private theorem r_200954 : RangeOk getRow 2051521 200954 201018 := by
  decide +kernel

private theorem r_201018 : RangeOk getRow 2051521 201018 201082 := by
  decide +kernel

private theorem r_201082 : RangeOk getRow 2051521 201082 201146 := by
  decide +kernel

private theorem r_201146 : RangeOk getRow 2051521 201146 201210 := by
  decide +kernel

private theorem r_201210 : RangeOk getRow 2051521 201210 201274 := by
  decide +kernel

private theorem r_201274 : RangeOk getRow 2051521 201274 201338 := by
  decide +kernel

private theorem r_201338 : RangeOk getRow 2051521 201338 201402 := by
  decide +kernel

private theorem r_201402 : RangeOk getRow 2051521 201402 201466 := by
  decide +kernel

private theorem r_201466 : RangeOk getRow 2051521 201466 201530 := by
  decide +kernel

private theorem r_201530 : RangeOk getRow 2051521 201530 201594 := by
  decide +kernel

private theorem r_201594 : RangeOk getRow 2051521 201594 201658 := by
  decide +kernel

private theorem r_201658 : RangeOk getRow 2051521 201658 201722 := by
  decide +kernel

private theorem r_201722 : RangeOk getRow 2051521 201722 201786 := by
  decide +kernel

private theorem r_201786 : RangeOk getRow 2051521 201786 201850 := by
  decide +kernel

private theorem r_201850 : RangeOk getRow 2051521 201850 201914 := by
  decide +kernel

private theorem r_201914 : RangeOk getRow 2051521 201914 201978 := by
  decide +kernel

private theorem r_201978 : RangeOk getRow 2051521 201978 202042 := by
  decide +kernel

private theorem r_202042 : RangeOk getRow 2051521 202042 202106 := by
  decide +kernel

private theorem s_200442 : RangeOk getRow 2051521 200378 200442 := r_200378
private theorem s_200506 : RangeOk getRow 2051521 200378 200506 :=
  s_200442.append (by norm_num) r_200442
private theorem s_200570 : RangeOk getRow 2051521 200378 200570 :=
  s_200506.append (by norm_num) r_200506
private theorem s_200634 : RangeOk getRow 2051521 200378 200634 :=
  s_200570.append (by norm_num) r_200570
private theorem s_200698 : RangeOk getRow 2051521 200378 200698 :=
  s_200634.append (by norm_num) r_200634
private theorem s_200762 : RangeOk getRow 2051521 200378 200762 :=
  s_200698.append (by norm_num) r_200698
private theorem s_200826 : RangeOk getRow 2051521 200378 200826 :=
  s_200762.append (by norm_num) r_200762
private theorem s_200890 : RangeOk getRow 2051521 200378 200890 :=
  s_200826.append (by norm_num) r_200826
private theorem s_200954 : RangeOk getRow 2051521 200378 200954 :=
  s_200890.append (by norm_num) r_200890
private theorem s_201018 : RangeOk getRow 2051521 200378 201018 :=
  s_200954.append (by norm_num) r_200954
private theorem s_201082 : RangeOk getRow 2051521 200378 201082 :=
  s_201018.append (by norm_num) r_201018
private theorem s_201146 : RangeOk getRow 2051521 200378 201146 :=
  s_201082.append (by norm_num) r_201082
private theorem s_201210 : RangeOk getRow 2051521 200378 201210 :=
  s_201146.append (by norm_num) r_201146
private theorem s_201274 : RangeOk getRow 2051521 200378 201274 :=
  s_201210.append (by norm_num) r_201210
private theorem s_201338 : RangeOk getRow 2051521 200378 201338 :=
  s_201274.append (by norm_num) r_201274
private theorem s_201402 : RangeOk getRow 2051521 200378 201402 :=
  s_201338.append (by norm_num) r_201338
private theorem s_201466 : RangeOk getRow 2051521 200378 201466 :=
  s_201402.append (by norm_num) r_201402
private theorem s_201530 : RangeOk getRow 2051521 200378 201530 :=
  s_201466.append (by norm_num) r_201466
private theorem s_201594 : RangeOk getRow 2051521 200378 201594 :=
  s_201530.append (by norm_num) r_201530
private theorem s_201658 : RangeOk getRow 2051521 200378 201658 :=
  s_201594.append (by norm_num) r_201594
private theorem s_201722 : RangeOk getRow 2051521 200378 201722 :=
  s_201658.append (by norm_num) r_201658
private theorem s_201786 : RangeOk getRow 2051521 200378 201786 :=
  s_201722.append (by norm_num) r_201722
private theorem s_201850 : RangeOk getRow 2051521 200378 201850 :=
  s_201786.append (by norm_num) r_201786
private theorem s_201914 : RangeOk getRow 2051521 200378 201914 :=
  s_201850.append (by norm_num) r_201850
private theorem s_201978 : RangeOk getRow 2051521 200378 201978 :=
  s_201914.append (by norm_num) r_201914
private theorem s_202042 : RangeOk getRow 2051521 200378 202042 :=
  s_201978.append (by norm_num) r_201978
private theorem s_202106 : RangeOk getRow 2051521 200378 202106 :=
  s_202042.append (by norm_num) r_202042

/-- Rows `[200378, 202106)` are valid. -/
theorem rangeOk_200378_202106 : RangeOk getRow 2051521 200378 202106 := s_202106

end Noperthedron.Solution
