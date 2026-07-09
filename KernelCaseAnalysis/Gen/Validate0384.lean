import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[925491, 928024). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_925491 : RangeOk getRow 2051521 925491 925560 := by
  decide +kernel

private theorem r_925560 : RangeOk getRow 2051521 925560 925629 := by
  decide +kernel

private theorem r_925629 : RangeOk getRow 2051521 925629 925698 := by
  decide +kernel

private theorem r_925698 : RangeOk getRow 2051521 925698 925765 := by
  decide +kernel

private theorem r_925765 : RangeOk getRow 2051521 925765 925831 := by
  decide +kernel

private theorem r_925831 : RangeOk getRow 2051521 925831 925898 := by
  decide +kernel

private theorem r_925898 : RangeOk getRow 2051521 925898 925964 := by
  decide +kernel

private theorem r_925964 : RangeOk getRow 2051521 925964 926029 := by
  decide +kernel

private theorem r_926029 : RangeOk getRow 2051521 926029 926093 := by
  decide +kernel

private theorem r_926093 : RangeOk getRow 2051521 926093 926164 := by
  decide +kernel

private theorem r_926164 : RangeOk getRow 2051521 926164 926234 := by
  decide +kernel

private theorem r_926234 : RangeOk getRow 2051521 926234 926304 := by
  decide +kernel

private theorem r_926304 : RangeOk getRow 2051521 926304 926374 := by
  decide +kernel

private theorem r_926374 : RangeOk getRow 2051521 926374 926446 := by
  decide +kernel

private theorem r_926446 : RangeOk getRow 2051521 926446 926517 := by
  decide +kernel

private theorem r_926517 : RangeOk getRow 2051521 926517 926587 := by
  decide +kernel

private theorem r_926587 : RangeOk getRow 2051521 926587 926657 := by
  decide +kernel

private theorem r_926657 : RangeOk getRow 2051521 926657 926726 := by
  decide +kernel

private theorem r_926726 : RangeOk getRow 2051521 926726 926794 := by
  decide +kernel

private theorem r_926794 : RangeOk getRow 2051521 926794 926862 := by
  decide +kernel

private theorem r_926862 : RangeOk getRow 2051521 926862 926930 := by
  decide +kernel

private theorem r_926930 : RangeOk getRow 2051521 926930 926997 := by
  decide +kernel

private theorem r_926997 : RangeOk getRow 2051521 926997 927063 := by
  decide +kernel

private theorem r_927063 : RangeOk getRow 2051521 927063 927129 := by
  decide +kernel

private theorem r_927129 : RangeOk getRow 2051521 927129 927193 := by
  decide +kernel

private theorem r_927193 : RangeOk getRow 2051521 927193 927260 := by
  decide +kernel

private theorem r_927260 : RangeOk getRow 2051521 927260 927330 := by
  decide +kernel

private theorem r_927330 : RangeOk getRow 2051521 927330 927400 := by
  decide +kernel

private theorem r_927400 : RangeOk getRow 2051521 927400 927470 := by
  decide +kernel

private theorem r_927470 : RangeOk getRow 2051521 927470 927540 := by
  decide +kernel

private theorem r_927540 : RangeOk getRow 2051521 927540 927610 := by
  decide +kernel

private theorem r_927610 : RangeOk getRow 2051521 927610 927682 := by
  decide +kernel

private theorem r_927682 : RangeOk getRow 2051521 927682 927752 := by
  decide +kernel

private theorem r_927752 : RangeOk getRow 2051521 927752 927820 := by
  decide +kernel

private theorem r_927820 : RangeOk getRow 2051521 927820 927888 := by
  decide +kernel

private theorem r_927888 : RangeOk getRow 2051521 927888 927956 := by
  decide +kernel

private theorem r_927956 : RangeOk getRow 2051521 927956 928024 := by
  decide +kernel

private theorem s_925560 : RangeOk getRow 2051521 925491 925560 := r_925491
private theorem s_925629 : RangeOk getRow 2051521 925491 925629 :=
  s_925560.append (by norm_num) r_925560
private theorem s_925698 : RangeOk getRow 2051521 925491 925698 :=
  s_925629.append (by norm_num) r_925629
private theorem s_925765 : RangeOk getRow 2051521 925491 925765 :=
  s_925698.append (by norm_num) r_925698
private theorem s_925831 : RangeOk getRow 2051521 925491 925831 :=
  s_925765.append (by norm_num) r_925765
private theorem s_925898 : RangeOk getRow 2051521 925491 925898 :=
  s_925831.append (by norm_num) r_925831
private theorem s_925964 : RangeOk getRow 2051521 925491 925964 :=
  s_925898.append (by norm_num) r_925898
private theorem s_926029 : RangeOk getRow 2051521 925491 926029 :=
  s_925964.append (by norm_num) r_925964
private theorem s_926093 : RangeOk getRow 2051521 925491 926093 :=
  s_926029.append (by norm_num) r_926029
private theorem s_926164 : RangeOk getRow 2051521 925491 926164 :=
  s_926093.append (by norm_num) r_926093
private theorem s_926234 : RangeOk getRow 2051521 925491 926234 :=
  s_926164.append (by norm_num) r_926164
private theorem s_926304 : RangeOk getRow 2051521 925491 926304 :=
  s_926234.append (by norm_num) r_926234
private theorem s_926374 : RangeOk getRow 2051521 925491 926374 :=
  s_926304.append (by norm_num) r_926304
private theorem s_926446 : RangeOk getRow 2051521 925491 926446 :=
  s_926374.append (by norm_num) r_926374
private theorem s_926517 : RangeOk getRow 2051521 925491 926517 :=
  s_926446.append (by norm_num) r_926446
private theorem s_926587 : RangeOk getRow 2051521 925491 926587 :=
  s_926517.append (by norm_num) r_926517
private theorem s_926657 : RangeOk getRow 2051521 925491 926657 :=
  s_926587.append (by norm_num) r_926587
private theorem s_926726 : RangeOk getRow 2051521 925491 926726 :=
  s_926657.append (by norm_num) r_926657
private theorem s_926794 : RangeOk getRow 2051521 925491 926794 :=
  s_926726.append (by norm_num) r_926726
private theorem s_926862 : RangeOk getRow 2051521 925491 926862 :=
  s_926794.append (by norm_num) r_926794
private theorem s_926930 : RangeOk getRow 2051521 925491 926930 :=
  s_926862.append (by norm_num) r_926862
private theorem s_926997 : RangeOk getRow 2051521 925491 926997 :=
  s_926930.append (by norm_num) r_926930
private theorem s_927063 : RangeOk getRow 2051521 925491 927063 :=
  s_926997.append (by norm_num) r_926997
private theorem s_927129 : RangeOk getRow 2051521 925491 927129 :=
  s_927063.append (by norm_num) r_927063
private theorem s_927193 : RangeOk getRow 2051521 925491 927193 :=
  s_927129.append (by norm_num) r_927129
private theorem s_927260 : RangeOk getRow 2051521 925491 927260 :=
  s_927193.append (by norm_num) r_927193
private theorem s_927330 : RangeOk getRow 2051521 925491 927330 :=
  s_927260.append (by norm_num) r_927260
private theorem s_927400 : RangeOk getRow 2051521 925491 927400 :=
  s_927330.append (by norm_num) r_927330
private theorem s_927470 : RangeOk getRow 2051521 925491 927470 :=
  s_927400.append (by norm_num) r_927400
private theorem s_927540 : RangeOk getRow 2051521 925491 927540 :=
  s_927470.append (by norm_num) r_927470
private theorem s_927610 : RangeOk getRow 2051521 925491 927610 :=
  s_927540.append (by norm_num) r_927540
private theorem s_927682 : RangeOk getRow 2051521 925491 927682 :=
  s_927610.append (by norm_num) r_927610
private theorem s_927752 : RangeOk getRow 2051521 925491 927752 :=
  s_927682.append (by norm_num) r_927682
private theorem s_927820 : RangeOk getRow 2051521 925491 927820 :=
  s_927752.append (by norm_num) r_927752
private theorem s_927888 : RangeOk getRow 2051521 925491 927888 :=
  s_927820.append (by norm_num) r_927820
private theorem s_927956 : RangeOk getRow 2051521 925491 927956 :=
  s_927888.append (by norm_num) r_927888
private theorem s_928024 : RangeOk getRow 2051521 925491 928024 :=
  s_927956.append (by norm_num) r_927956

/-- Rows `[925491, 928024)` are valid. -/
theorem rangeOk_925491_928024 : RangeOk getRow 2051521 925491 928024 := s_928024

end Noperthedron.Solution
