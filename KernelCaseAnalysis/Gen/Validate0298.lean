import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[718472, 720686). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_718472 : RangeOk getRow 2051521 718472 718541 := by
  decide +kernel

private theorem r_718541 : RangeOk getRow 2051521 718541 718609 := by
  decide +kernel

private theorem r_718609 : RangeOk getRow 2051521 718609 718677 := by
  decide +kernel

private theorem r_718677 : RangeOk getRow 2051521 718677 718743 := by
  decide +kernel

private theorem r_718743 : RangeOk getRow 2051521 718743 718811 := by
  decide +kernel

private theorem r_718811 : RangeOk getRow 2051521 718811 718876 := by
  decide +kernel

private theorem r_718876 : RangeOk getRow 2051521 718876 718942 := by
  decide +kernel

private theorem r_718942 : RangeOk getRow 2051521 718942 719010 := by
  decide +kernel

private theorem r_719010 : RangeOk getRow 2051521 719010 719079 := by
  decide +kernel

private theorem r_719079 : RangeOk getRow 2051521 719079 719147 := by
  decide +kernel

private theorem r_719147 : RangeOk getRow 2051521 719147 719215 := by
  decide +kernel

private theorem r_719215 : RangeOk getRow 2051521 719215 719280 := by
  decide +kernel

private theorem r_719280 : RangeOk getRow 2051521 719280 719345 := by
  decide +kernel

private theorem r_719345 : RangeOk getRow 2051521 719345 719412 := by
  decide +kernel

private theorem r_719412 : RangeOk getRow 2051521 719412 719479 := by
  decide +kernel

private theorem r_719479 : RangeOk getRow 2051521 719479 719548 := by
  decide +kernel

private theorem r_719548 : RangeOk getRow 2051521 719548 719615 := by
  decide +kernel

private theorem r_719615 : RangeOk getRow 2051521 719615 719684 := by
  decide +kernel

private theorem r_719684 : RangeOk getRow 2051521 719684 719751 := by
  decide +kernel

private theorem r_719751 : RangeOk getRow 2051521 719751 719819 := by
  decide +kernel

private theorem r_719819 : RangeOk getRow 2051521 719819 719886 := by
  decide +kernel

private theorem r_719886 : RangeOk getRow 2051521 719886 719952 := by
  decide +kernel

private theorem r_719952 : RangeOk getRow 2051521 719952 720018 := by
  decide +kernel

private theorem r_720018 : RangeOk getRow 2051521 720018 720084 := by
  decide +kernel

private theorem r_720084 : RangeOk getRow 2051521 720084 720152 := by
  decide +kernel

private theorem r_720152 : RangeOk getRow 2051521 720152 720220 := by
  decide +kernel

private theorem r_720220 : RangeOk getRow 2051521 720220 720288 := by
  decide +kernel

private theorem r_720288 : RangeOk getRow 2051521 720288 720356 := by
  decide +kernel

private theorem r_720356 : RangeOk getRow 2051521 720356 720423 := by
  decide +kernel

private theorem r_720423 : RangeOk getRow 2051521 720423 720488 := by
  decide +kernel

private theorem r_720488 : RangeOk getRow 2051521 720488 720556 := by
  decide +kernel

private theorem r_720556 : RangeOk getRow 2051521 720556 720620 := by
  decide +kernel

private theorem r_720620 : RangeOk getRow 2051521 720620 720686 := by
  decide +kernel

private theorem s_718541 : RangeOk getRow 2051521 718472 718541 := r_718472
private theorem s_718609 : RangeOk getRow 2051521 718472 718609 :=
  s_718541.append (by norm_num) r_718541
private theorem s_718677 : RangeOk getRow 2051521 718472 718677 :=
  s_718609.append (by norm_num) r_718609
private theorem s_718743 : RangeOk getRow 2051521 718472 718743 :=
  s_718677.append (by norm_num) r_718677
private theorem s_718811 : RangeOk getRow 2051521 718472 718811 :=
  s_718743.append (by norm_num) r_718743
private theorem s_718876 : RangeOk getRow 2051521 718472 718876 :=
  s_718811.append (by norm_num) r_718811
private theorem s_718942 : RangeOk getRow 2051521 718472 718942 :=
  s_718876.append (by norm_num) r_718876
private theorem s_719010 : RangeOk getRow 2051521 718472 719010 :=
  s_718942.append (by norm_num) r_718942
private theorem s_719079 : RangeOk getRow 2051521 718472 719079 :=
  s_719010.append (by norm_num) r_719010
private theorem s_719147 : RangeOk getRow 2051521 718472 719147 :=
  s_719079.append (by norm_num) r_719079
private theorem s_719215 : RangeOk getRow 2051521 718472 719215 :=
  s_719147.append (by norm_num) r_719147
private theorem s_719280 : RangeOk getRow 2051521 718472 719280 :=
  s_719215.append (by norm_num) r_719215
private theorem s_719345 : RangeOk getRow 2051521 718472 719345 :=
  s_719280.append (by norm_num) r_719280
private theorem s_719412 : RangeOk getRow 2051521 718472 719412 :=
  s_719345.append (by norm_num) r_719345
private theorem s_719479 : RangeOk getRow 2051521 718472 719479 :=
  s_719412.append (by norm_num) r_719412
private theorem s_719548 : RangeOk getRow 2051521 718472 719548 :=
  s_719479.append (by norm_num) r_719479
private theorem s_719615 : RangeOk getRow 2051521 718472 719615 :=
  s_719548.append (by norm_num) r_719548
private theorem s_719684 : RangeOk getRow 2051521 718472 719684 :=
  s_719615.append (by norm_num) r_719615
private theorem s_719751 : RangeOk getRow 2051521 718472 719751 :=
  s_719684.append (by norm_num) r_719684
private theorem s_719819 : RangeOk getRow 2051521 718472 719819 :=
  s_719751.append (by norm_num) r_719751
private theorem s_719886 : RangeOk getRow 2051521 718472 719886 :=
  s_719819.append (by norm_num) r_719819
private theorem s_719952 : RangeOk getRow 2051521 718472 719952 :=
  s_719886.append (by norm_num) r_719886
private theorem s_720018 : RangeOk getRow 2051521 718472 720018 :=
  s_719952.append (by norm_num) r_719952
private theorem s_720084 : RangeOk getRow 2051521 718472 720084 :=
  s_720018.append (by norm_num) r_720018
private theorem s_720152 : RangeOk getRow 2051521 718472 720152 :=
  s_720084.append (by norm_num) r_720084
private theorem s_720220 : RangeOk getRow 2051521 718472 720220 :=
  s_720152.append (by norm_num) r_720152
private theorem s_720288 : RangeOk getRow 2051521 718472 720288 :=
  s_720220.append (by norm_num) r_720220
private theorem s_720356 : RangeOk getRow 2051521 718472 720356 :=
  s_720288.append (by norm_num) r_720288
private theorem s_720423 : RangeOk getRow 2051521 718472 720423 :=
  s_720356.append (by norm_num) r_720356
private theorem s_720488 : RangeOk getRow 2051521 718472 720488 :=
  s_720423.append (by norm_num) r_720423
private theorem s_720556 : RangeOk getRow 2051521 718472 720556 :=
  s_720488.append (by norm_num) r_720488
private theorem s_720620 : RangeOk getRow 2051521 718472 720620 :=
  s_720556.append (by norm_num) r_720556
private theorem s_720686 : RangeOk getRow 2051521 718472 720686 :=
  s_720620.append (by norm_num) r_720620

/-- Rows `[718472, 720686)` are valid. -/
theorem rangeOk_718472_720686 : RangeOk getRow 2051521 718472 720686 := s_720686

end Noperthedron.Solution
