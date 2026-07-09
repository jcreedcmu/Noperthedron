import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[895886, 898505). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_895886 : RangeOk getRow 2051521 895886 895953 := by
  decide +kernel

private theorem r_895953 : RangeOk getRow 2051521 895953 896021 := by
  decide +kernel

private theorem r_896021 : RangeOk getRow 2051521 896021 896088 := by
  decide +kernel

private theorem r_896088 : RangeOk getRow 2051521 896088 896154 := by
  decide +kernel

private theorem r_896154 : RangeOk getRow 2051521 896154 896222 := by
  decide +kernel

private theorem r_896222 : RangeOk getRow 2051521 896222 896290 := by
  decide +kernel

private theorem r_896290 : RangeOk getRow 2051521 896290 896358 := by
  decide +kernel

private theorem r_896358 : RangeOk getRow 2051521 896358 896424 := by
  decide +kernel

private theorem r_896424 : RangeOk getRow 2051521 896424 896491 := by
  decide +kernel

private theorem r_896491 : RangeOk getRow 2051521 896491 896560 := by
  decide +kernel

private theorem r_896560 : RangeOk getRow 2051521 896560 896629 := by
  decide +kernel

private theorem r_896629 : RangeOk getRow 2051521 896629 896696 := by
  decide +kernel

private theorem r_896696 : RangeOk getRow 2051521 896696 896761 := by
  decide +kernel

private theorem r_896761 : RangeOk getRow 2051521 896761 896830 := by
  decide +kernel

private theorem r_896830 : RangeOk getRow 2051521 896830 896902 := by
  decide +kernel

private theorem r_896902 : RangeOk getRow 2051521 896902 896970 := by
  decide +kernel

private theorem r_896970 : RangeOk getRow 2051521 896970 897039 := by
  decide +kernel

private theorem r_897039 : RangeOk getRow 2051521 897039 897111 := by
  decide +kernel

private theorem r_897111 : RangeOk getRow 2051521 897111 897179 := by
  decide +kernel

private theorem r_897179 : RangeOk getRow 2051521 897179 897251 := by
  decide +kernel

private theorem r_897251 : RangeOk getRow 2051521 897251 897321 := by
  decide +kernel

private theorem r_897321 : RangeOk getRow 2051521 897321 897393 := by
  decide +kernel

private theorem r_897393 : RangeOk getRow 2051521 897393 897464 := by
  decide +kernel

private theorem r_897464 : RangeOk getRow 2051521 897464 897535 := by
  decide +kernel

private theorem r_897535 : RangeOk getRow 2051521 897535 897606 := by
  decide +kernel

private theorem r_897606 : RangeOk getRow 2051521 897606 897676 := by
  decide +kernel

private theorem r_897676 : RangeOk getRow 2051521 897676 897746 := by
  decide +kernel

private theorem r_897746 : RangeOk getRow 2051521 897746 897818 := by
  decide +kernel

private theorem r_897818 : RangeOk getRow 2051521 897818 897887 := by
  decide +kernel

private theorem r_897887 : RangeOk getRow 2051521 897887 897956 := by
  decide +kernel

private theorem r_897956 : RangeOk getRow 2051521 897956 898026 := by
  decide +kernel

private theorem r_898026 : RangeOk getRow 2051521 898026 898096 := by
  decide +kernel

private theorem r_898096 : RangeOk getRow 2051521 898096 898167 := by
  decide +kernel

private theorem r_898167 : RangeOk getRow 2051521 898167 898236 := by
  decide +kernel

private theorem r_898236 : RangeOk getRow 2051521 898236 898305 := by
  decide +kernel

private theorem r_898305 : RangeOk getRow 2051521 898305 898371 := by
  decide +kernel

private theorem r_898371 : RangeOk getRow 2051521 898371 898438 := by
  decide +kernel

private theorem r_898438 : RangeOk getRow 2051521 898438 898505 := by
  decide +kernel

private theorem s_895953 : RangeOk getRow 2051521 895886 895953 := r_895886
private theorem s_896021 : RangeOk getRow 2051521 895886 896021 :=
  s_895953.append (by norm_num) r_895953
private theorem s_896088 : RangeOk getRow 2051521 895886 896088 :=
  s_896021.append (by norm_num) r_896021
private theorem s_896154 : RangeOk getRow 2051521 895886 896154 :=
  s_896088.append (by norm_num) r_896088
private theorem s_896222 : RangeOk getRow 2051521 895886 896222 :=
  s_896154.append (by norm_num) r_896154
private theorem s_896290 : RangeOk getRow 2051521 895886 896290 :=
  s_896222.append (by norm_num) r_896222
private theorem s_896358 : RangeOk getRow 2051521 895886 896358 :=
  s_896290.append (by norm_num) r_896290
private theorem s_896424 : RangeOk getRow 2051521 895886 896424 :=
  s_896358.append (by norm_num) r_896358
private theorem s_896491 : RangeOk getRow 2051521 895886 896491 :=
  s_896424.append (by norm_num) r_896424
private theorem s_896560 : RangeOk getRow 2051521 895886 896560 :=
  s_896491.append (by norm_num) r_896491
private theorem s_896629 : RangeOk getRow 2051521 895886 896629 :=
  s_896560.append (by norm_num) r_896560
private theorem s_896696 : RangeOk getRow 2051521 895886 896696 :=
  s_896629.append (by norm_num) r_896629
private theorem s_896761 : RangeOk getRow 2051521 895886 896761 :=
  s_896696.append (by norm_num) r_896696
private theorem s_896830 : RangeOk getRow 2051521 895886 896830 :=
  s_896761.append (by norm_num) r_896761
private theorem s_896902 : RangeOk getRow 2051521 895886 896902 :=
  s_896830.append (by norm_num) r_896830
private theorem s_896970 : RangeOk getRow 2051521 895886 896970 :=
  s_896902.append (by norm_num) r_896902
private theorem s_897039 : RangeOk getRow 2051521 895886 897039 :=
  s_896970.append (by norm_num) r_896970
private theorem s_897111 : RangeOk getRow 2051521 895886 897111 :=
  s_897039.append (by norm_num) r_897039
private theorem s_897179 : RangeOk getRow 2051521 895886 897179 :=
  s_897111.append (by norm_num) r_897111
private theorem s_897251 : RangeOk getRow 2051521 895886 897251 :=
  s_897179.append (by norm_num) r_897179
private theorem s_897321 : RangeOk getRow 2051521 895886 897321 :=
  s_897251.append (by norm_num) r_897251
private theorem s_897393 : RangeOk getRow 2051521 895886 897393 :=
  s_897321.append (by norm_num) r_897321
private theorem s_897464 : RangeOk getRow 2051521 895886 897464 :=
  s_897393.append (by norm_num) r_897393
private theorem s_897535 : RangeOk getRow 2051521 895886 897535 :=
  s_897464.append (by norm_num) r_897464
private theorem s_897606 : RangeOk getRow 2051521 895886 897606 :=
  s_897535.append (by norm_num) r_897535
private theorem s_897676 : RangeOk getRow 2051521 895886 897676 :=
  s_897606.append (by norm_num) r_897606
private theorem s_897746 : RangeOk getRow 2051521 895886 897746 :=
  s_897676.append (by norm_num) r_897676
private theorem s_897818 : RangeOk getRow 2051521 895886 897818 :=
  s_897746.append (by norm_num) r_897746
private theorem s_897887 : RangeOk getRow 2051521 895886 897887 :=
  s_897818.append (by norm_num) r_897818
private theorem s_897956 : RangeOk getRow 2051521 895886 897956 :=
  s_897887.append (by norm_num) r_897887
private theorem s_898026 : RangeOk getRow 2051521 895886 898026 :=
  s_897956.append (by norm_num) r_897956
private theorem s_898096 : RangeOk getRow 2051521 895886 898096 :=
  s_898026.append (by norm_num) r_898026
private theorem s_898167 : RangeOk getRow 2051521 895886 898167 :=
  s_898096.append (by norm_num) r_898096
private theorem s_898236 : RangeOk getRow 2051521 895886 898236 :=
  s_898167.append (by norm_num) r_898167
private theorem s_898305 : RangeOk getRow 2051521 895886 898305 :=
  s_898236.append (by norm_num) r_898236
private theorem s_898371 : RangeOk getRow 2051521 895886 898371 :=
  s_898305.append (by norm_num) r_898305
private theorem s_898438 : RangeOk getRow 2051521 895886 898438 :=
  s_898371.append (by norm_num) r_898371
private theorem s_898505 : RangeOk getRow 2051521 895886 898505 :=
  s_898438.append (by norm_num) r_898438

/-- Rows `[895886, 898505)` are valid. -/
theorem rangeOk_895886_898505 : RangeOk getRow 2051521 895886 898505 := s_898505

end Noperthedron.Solution
