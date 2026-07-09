import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[491682, 493978). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_491682 : RangeOk getRow 2051521 491682 491749 := by
  decide +kernel

private theorem r_491749 : RangeOk getRow 2051521 491749 491820 := by
  decide +kernel

private theorem r_491820 : RangeOk getRow 2051521 491820 491888 := by
  decide +kernel

private theorem r_491888 : RangeOk getRow 2051521 491888 491955 := by
  decide +kernel

private theorem r_491955 : RangeOk getRow 2051521 491955 492022 := by
  decide +kernel

private theorem r_492022 : RangeOk getRow 2051521 492022 492090 := by
  decide +kernel

private theorem r_492090 : RangeOk getRow 2051521 492090 492159 := by
  decide +kernel

private theorem r_492159 : RangeOk getRow 2051521 492159 492229 := by
  decide +kernel

private theorem r_492229 : RangeOk getRow 2051521 492229 492298 := by
  decide +kernel

private theorem r_492298 : RangeOk getRow 2051521 492298 492366 := by
  decide +kernel

private theorem r_492366 : RangeOk getRow 2051521 492366 492434 := by
  decide +kernel

private theorem r_492434 : RangeOk getRow 2051521 492434 492500 := by
  decide +kernel

private theorem r_492500 : RangeOk getRow 2051521 492500 492566 := by
  decide +kernel

private theorem r_492566 : RangeOk getRow 2051521 492566 492632 := by
  decide +kernel

private theorem r_492632 : RangeOk getRow 2051521 492632 492700 := by
  decide +kernel

private theorem r_492700 : RangeOk getRow 2051521 492700 492768 := by
  decide +kernel

private theorem r_492768 : RangeOk getRow 2051521 492768 492837 := by
  decide +kernel

private theorem r_492837 : RangeOk getRow 2051521 492837 492904 := by
  decide +kernel

private theorem r_492904 : RangeOk getRow 2051521 492904 492972 := by
  decide +kernel

private theorem r_492972 : RangeOk getRow 2051521 492972 493036 := by
  decide +kernel

private theorem r_493036 : RangeOk getRow 2051521 493036 493103 := by
  decide +kernel

private theorem r_493103 : RangeOk getRow 2051521 493103 493172 := by
  decide +kernel

private theorem r_493172 : RangeOk getRow 2051521 493172 493241 := by
  decide +kernel

private theorem r_493241 : RangeOk getRow 2051521 493241 493308 := by
  decide +kernel

private theorem r_493308 : RangeOk getRow 2051521 493308 493372 := by
  decide +kernel

private theorem r_493372 : RangeOk getRow 2051521 493372 493436 := by
  decide +kernel

private theorem r_493436 : RangeOk getRow 2051521 493436 493506 := by
  decide +kernel

private theorem r_493506 : RangeOk getRow 2051521 493506 493573 := by
  decide +kernel

private theorem r_493573 : RangeOk getRow 2051521 493573 493638 := by
  decide +kernel

private theorem r_493638 : RangeOk getRow 2051521 493638 493705 := by
  decide +kernel

private theorem r_493705 : RangeOk getRow 2051521 493705 493773 := by
  decide +kernel

private theorem r_493773 : RangeOk getRow 2051521 493773 493842 := by
  decide +kernel

private theorem r_493842 : RangeOk getRow 2051521 493842 493910 := by
  decide +kernel

private theorem r_493910 : RangeOk getRow 2051521 493910 493978 := by
  decide +kernel

private theorem s_491749 : RangeOk getRow 2051521 491682 491749 := r_491682
private theorem s_491820 : RangeOk getRow 2051521 491682 491820 :=
  s_491749.append (by norm_num) r_491749
private theorem s_491888 : RangeOk getRow 2051521 491682 491888 :=
  s_491820.append (by norm_num) r_491820
private theorem s_491955 : RangeOk getRow 2051521 491682 491955 :=
  s_491888.append (by norm_num) r_491888
private theorem s_492022 : RangeOk getRow 2051521 491682 492022 :=
  s_491955.append (by norm_num) r_491955
private theorem s_492090 : RangeOk getRow 2051521 491682 492090 :=
  s_492022.append (by norm_num) r_492022
private theorem s_492159 : RangeOk getRow 2051521 491682 492159 :=
  s_492090.append (by norm_num) r_492090
private theorem s_492229 : RangeOk getRow 2051521 491682 492229 :=
  s_492159.append (by norm_num) r_492159
private theorem s_492298 : RangeOk getRow 2051521 491682 492298 :=
  s_492229.append (by norm_num) r_492229
private theorem s_492366 : RangeOk getRow 2051521 491682 492366 :=
  s_492298.append (by norm_num) r_492298
private theorem s_492434 : RangeOk getRow 2051521 491682 492434 :=
  s_492366.append (by norm_num) r_492366
private theorem s_492500 : RangeOk getRow 2051521 491682 492500 :=
  s_492434.append (by norm_num) r_492434
private theorem s_492566 : RangeOk getRow 2051521 491682 492566 :=
  s_492500.append (by norm_num) r_492500
private theorem s_492632 : RangeOk getRow 2051521 491682 492632 :=
  s_492566.append (by norm_num) r_492566
private theorem s_492700 : RangeOk getRow 2051521 491682 492700 :=
  s_492632.append (by norm_num) r_492632
private theorem s_492768 : RangeOk getRow 2051521 491682 492768 :=
  s_492700.append (by norm_num) r_492700
private theorem s_492837 : RangeOk getRow 2051521 491682 492837 :=
  s_492768.append (by norm_num) r_492768
private theorem s_492904 : RangeOk getRow 2051521 491682 492904 :=
  s_492837.append (by norm_num) r_492837
private theorem s_492972 : RangeOk getRow 2051521 491682 492972 :=
  s_492904.append (by norm_num) r_492904
private theorem s_493036 : RangeOk getRow 2051521 491682 493036 :=
  s_492972.append (by norm_num) r_492972
private theorem s_493103 : RangeOk getRow 2051521 491682 493103 :=
  s_493036.append (by norm_num) r_493036
private theorem s_493172 : RangeOk getRow 2051521 491682 493172 :=
  s_493103.append (by norm_num) r_493103
private theorem s_493241 : RangeOk getRow 2051521 491682 493241 :=
  s_493172.append (by norm_num) r_493172
private theorem s_493308 : RangeOk getRow 2051521 491682 493308 :=
  s_493241.append (by norm_num) r_493241
private theorem s_493372 : RangeOk getRow 2051521 491682 493372 :=
  s_493308.append (by norm_num) r_493308
private theorem s_493436 : RangeOk getRow 2051521 491682 493436 :=
  s_493372.append (by norm_num) r_493372
private theorem s_493506 : RangeOk getRow 2051521 491682 493506 :=
  s_493436.append (by norm_num) r_493436
private theorem s_493573 : RangeOk getRow 2051521 491682 493573 :=
  s_493506.append (by norm_num) r_493506
private theorem s_493638 : RangeOk getRow 2051521 491682 493638 :=
  s_493573.append (by norm_num) r_493573
private theorem s_493705 : RangeOk getRow 2051521 491682 493705 :=
  s_493638.append (by norm_num) r_493638
private theorem s_493773 : RangeOk getRow 2051521 491682 493773 :=
  s_493705.append (by norm_num) r_493705
private theorem s_493842 : RangeOk getRow 2051521 491682 493842 :=
  s_493773.append (by norm_num) r_493773
private theorem s_493910 : RangeOk getRow 2051521 491682 493910 :=
  s_493842.append (by norm_num) r_493842
private theorem s_493978 : RangeOk getRow 2051521 491682 493978 :=
  s_493910.append (by norm_num) r_493910

/-- Rows `[491682, 493978)` are valid. -/
theorem rangeOk_491682_493978 : RangeOk getRow 2051521 491682 493978 := s_493978

end Noperthedron.Solution
