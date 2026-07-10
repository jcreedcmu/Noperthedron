import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[406945, 409316). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_406945 : RangeOk getRow 2051521 406945 407014 := by
  decide +kernel

private theorem r_407014 : RangeOk getRow 2051521 407014 407083 := by
  decide +kernel

private theorem r_407083 : RangeOk getRow 2051521 407083 407151 := by
  decide +kernel

private theorem r_407151 : RangeOk getRow 2051521 407151 407219 := by
  decide +kernel

private theorem r_407219 : RangeOk getRow 2051521 407219 407286 := by
  decide +kernel

private theorem r_407286 : RangeOk getRow 2051521 407286 407352 := by
  decide +kernel

private theorem r_407352 : RangeOk getRow 2051521 407352 407422 := by
  decide +kernel

private theorem r_407422 : RangeOk getRow 2051521 407422 407491 := by
  decide +kernel

private theorem r_407491 : RangeOk getRow 2051521 407491 407562 := by
  decide +kernel

private theorem r_407562 : RangeOk getRow 2051521 407562 407631 := by
  decide +kernel

private theorem r_407631 : RangeOk getRow 2051521 407631 407696 := by
  decide +kernel

private theorem r_407696 : RangeOk getRow 2051521 407696 407760 := by
  decide +kernel

private theorem r_407760 : RangeOk getRow 2051521 407760 407826 := by
  decide +kernel

private theorem r_407826 : RangeOk getRow 2051521 407826 407893 := by
  decide +kernel

private theorem r_407893 : RangeOk getRow 2051521 407893 407961 := by
  decide +kernel

private theorem r_407961 : RangeOk getRow 2051521 407961 408028 := by
  decide +kernel

private theorem r_408028 : RangeOk getRow 2051521 408028 408095 := by
  decide +kernel

private theorem r_408095 : RangeOk getRow 2051521 408095 408164 := by
  decide +kernel

private theorem r_408164 : RangeOk getRow 2051521 408164 408234 := by
  decide +kernel

private theorem r_408234 : RangeOk getRow 2051521 408234 408303 := by
  decide +kernel

private theorem r_408303 : RangeOk getRow 2051521 408303 408371 := by
  decide +kernel

private theorem r_408371 : RangeOk getRow 2051521 408371 408439 := by
  decide +kernel

private theorem r_408439 : RangeOk getRow 2051521 408439 408507 := by
  decide +kernel

private theorem r_408507 : RangeOk getRow 2051521 408507 408575 := by
  decide +kernel

private theorem r_408575 : RangeOk getRow 2051521 408575 408642 := by
  decide +kernel

private theorem r_408642 : RangeOk getRow 2051521 408642 408711 := by
  decide +kernel

private theorem r_408711 : RangeOk getRow 2051521 408711 408781 := by
  decide +kernel

private theorem r_408781 : RangeOk getRow 2051521 408781 408849 := by
  decide +kernel

private theorem r_408849 : RangeOk getRow 2051521 408849 408916 := by
  decide +kernel

private theorem r_408916 : RangeOk getRow 2051521 408916 408982 := by
  decide +kernel

private theorem r_408982 : RangeOk getRow 2051521 408982 409047 := by
  decide +kernel

private theorem r_409047 : RangeOk getRow 2051521 409047 409112 := by
  decide +kernel

private theorem r_409112 : RangeOk getRow 2051521 409112 409179 := by
  decide +kernel

private theorem r_409179 : RangeOk getRow 2051521 409179 409247 := by
  decide +kernel

private theorem r_409247 : RangeOk getRow 2051521 409247 409316 := by
  decide +kernel

private theorem s_407014 : RangeOk getRow 2051521 406945 407014 := r_406945
private theorem s_407083 : RangeOk getRow 2051521 406945 407083 :=
  s_407014.append (by norm_num) r_407014
private theorem s_407151 : RangeOk getRow 2051521 406945 407151 :=
  s_407083.append (by norm_num) r_407083
private theorem s_407219 : RangeOk getRow 2051521 406945 407219 :=
  s_407151.append (by norm_num) r_407151
private theorem s_407286 : RangeOk getRow 2051521 406945 407286 :=
  s_407219.append (by norm_num) r_407219
private theorem s_407352 : RangeOk getRow 2051521 406945 407352 :=
  s_407286.append (by norm_num) r_407286
private theorem s_407422 : RangeOk getRow 2051521 406945 407422 :=
  s_407352.append (by norm_num) r_407352
private theorem s_407491 : RangeOk getRow 2051521 406945 407491 :=
  s_407422.append (by norm_num) r_407422
private theorem s_407562 : RangeOk getRow 2051521 406945 407562 :=
  s_407491.append (by norm_num) r_407491
private theorem s_407631 : RangeOk getRow 2051521 406945 407631 :=
  s_407562.append (by norm_num) r_407562
private theorem s_407696 : RangeOk getRow 2051521 406945 407696 :=
  s_407631.append (by norm_num) r_407631
private theorem s_407760 : RangeOk getRow 2051521 406945 407760 :=
  s_407696.append (by norm_num) r_407696
private theorem s_407826 : RangeOk getRow 2051521 406945 407826 :=
  s_407760.append (by norm_num) r_407760
private theorem s_407893 : RangeOk getRow 2051521 406945 407893 :=
  s_407826.append (by norm_num) r_407826
private theorem s_407961 : RangeOk getRow 2051521 406945 407961 :=
  s_407893.append (by norm_num) r_407893
private theorem s_408028 : RangeOk getRow 2051521 406945 408028 :=
  s_407961.append (by norm_num) r_407961
private theorem s_408095 : RangeOk getRow 2051521 406945 408095 :=
  s_408028.append (by norm_num) r_408028
private theorem s_408164 : RangeOk getRow 2051521 406945 408164 :=
  s_408095.append (by norm_num) r_408095
private theorem s_408234 : RangeOk getRow 2051521 406945 408234 :=
  s_408164.append (by norm_num) r_408164
private theorem s_408303 : RangeOk getRow 2051521 406945 408303 :=
  s_408234.append (by norm_num) r_408234
private theorem s_408371 : RangeOk getRow 2051521 406945 408371 :=
  s_408303.append (by norm_num) r_408303
private theorem s_408439 : RangeOk getRow 2051521 406945 408439 :=
  s_408371.append (by norm_num) r_408371
private theorem s_408507 : RangeOk getRow 2051521 406945 408507 :=
  s_408439.append (by norm_num) r_408439
private theorem s_408575 : RangeOk getRow 2051521 406945 408575 :=
  s_408507.append (by norm_num) r_408507
private theorem s_408642 : RangeOk getRow 2051521 406945 408642 :=
  s_408575.append (by norm_num) r_408575
private theorem s_408711 : RangeOk getRow 2051521 406945 408711 :=
  s_408642.append (by norm_num) r_408642
private theorem s_408781 : RangeOk getRow 2051521 406945 408781 :=
  s_408711.append (by norm_num) r_408711
private theorem s_408849 : RangeOk getRow 2051521 406945 408849 :=
  s_408781.append (by norm_num) r_408781
private theorem s_408916 : RangeOk getRow 2051521 406945 408916 :=
  s_408849.append (by norm_num) r_408849
private theorem s_408982 : RangeOk getRow 2051521 406945 408982 :=
  s_408916.append (by norm_num) r_408916
private theorem s_409047 : RangeOk getRow 2051521 406945 409047 :=
  s_408982.append (by norm_num) r_408982
private theorem s_409112 : RangeOk getRow 2051521 406945 409112 :=
  s_409047.append (by norm_num) r_409047
private theorem s_409179 : RangeOk getRow 2051521 406945 409179 :=
  s_409112.append (by norm_num) r_409112
private theorem s_409247 : RangeOk getRow 2051521 406945 409247 :=
  s_409179.append (by norm_num) r_409179
private theorem s_409316 : RangeOk getRow 2051521 406945 409316 :=
  s_409247.append (by norm_num) r_409247

/-- Rows `[406945, 409316)` are valid. -/
theorem rangeOk_406945_409316 : RangeOk getRow 2051521 406945 409316 := s_409316

end Noperthedron.Solution
