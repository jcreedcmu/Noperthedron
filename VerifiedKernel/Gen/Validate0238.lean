import VerifiedKernel.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[575832, 578126). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_575832 : RangeOk getRow 2051521 575832 575901 := by
  decide +kernel

private theorem r_575901 : RangeOk getRow 2051521 575901 575968 := by
  decide +kernel

private theorem r_575968 : RangeOk getRow 2051521 575968 576037 := by
  decide +kernel

private theorem r_576037 : RangeOk getRow 2051521 576037 576105 := by
  decide +kernel

private theorem r_576105 : RangeOk getRow 2051521 576105 576171 := by
  decide +kernel

private theorem r_576171 : RangeOk getRow 2051521 576171 576238 := by
  decide +kernel

private theorem r_576238 : RangeOk getRow 2051521 576238 576305 := by
  decide +kernel

private theorem r_576305 : RangeOk getRow 2051521 576305 576370 := by
  decide +kernel

private theorem r_576370 : RangeOk getRow 2051521 576370 576436 := by
  decide +kernel

private theorem r_576436 : RangeOk getRow 2051521 576436 576505 := by
  decide +kernel

private theorem r_576505 : RangeOk getRow 2051521 576505 576573 := by
  decide +kernel

private theorem r_576573 : RangeOk getRow 2051521 576573 576643 := by
  decide +kernel

private theorem r_576643 : RangeOk getRow 2051521 576643 576712 := by
  decide +kernel

private theorem r_576712 : RangeOk getRow 2051521 576712 576781 := by
  decide +kernel

private theorem r_576781 : RangeOk getRow 2051521 576781 576847 := by
  decide +kernel

private theorem r_576847 : RangeOk getRow 2051521 576847 576914 := by
  decide +kernel

private theorem r_576914 : RangeOk getRow 2051521 576914 576983 := by
  decide +kernel

private theorem r_576983 : RangeOk getRow 2051521 576983 577049 := by
  decide +kernel

private theorem r_577049 : RangeOk getRow 2051521 577049 577114 := by
  decide +kernel

private theorem r_577114 : RangeOk getRow 2051521 577114 577179 := by
  decide +kernel

private theorem r_577179 : RangeOk getRow 2051521 577179 577248 := by
  decide +kernel

private theorem r_577248 : RangeOk getRow 2051521 577248 577316 := by
  decide +kernel

private theorem r_577316 : RangeOk getRow 2051521 577316 577384 := by
  decide +kernel

private theorem r_577384 : RangeOk getRow 2051521 577384 577452 := by
  decide +kernel

private theorem r_577452 : RangeOk getRow 2051521 577452 577521 := by
  decide +kernel

private theorem r_577521 : RangeOk getRow 2051521 577521 577587 := by
  decide +kernel

private theorem r_577587 : RangeOk getRow 2051521 577587 577654 := by
  decide +kernel

private theorem r_577654 : RangeOk getRow 2051521 577654 577719 := by
  decide +kernel

private theorem r_577719 : RangeOk getRow 2051521 577719 577785 := by
  decide +kernel

private theorem r_577785 : RangeOk getRow 2051521 577785 577853 := by
  decide +kernel

private theorem r_577853 : RangeOk getRow 2051521 577853 577923 := by
  decide +kernel

private theorem r_577923 : RangeOk getRow 2051521 577923 577993 := by
  decide +kernel

private theorem r_577993 : RangeOk getRow 2051521 577993 578060 := by
  decide +kernel

private theorem r_578060 : RangeOk getRow 2051521 578060 578126 := by
  decide +kernel

private theorem s_575901 : RangeOk getRow 2051521 575832 575901 := r_575832
private theorem s_575968 : RangeOk getRow 2051521 575832 575968 :=
  s_575901.append (by norm_num) r_575901
private theorem s_576037 : RangeOk getRow 2051521 575832 576037 :=
  s_575968.append (by norm_num) r_575968
private theorem s_576105 : RangeOk getRow 2051521 575832 576105 :=
  s_576037.append (by norm_num) r_576037
private theorem s_576171 : RangeOk getRow 2051521 575832 576171 :=
  s_576105.append (by norm_num) r_576105
private theorem s_576238 : RangeOk getRow 2051521 575832 576238 :=
  s_576171.append (by norm_num) r_576171
private theorem s_576305 : RangeOk getRow 2051521 575832 576305 :=
  s_576238.append (by norm_num) r_576238
private theorem s_576370 : RangeOk getRow 2051521 575832 576370 :=
  s_576305.append (by norm_num) r_576305
private theorem s_576436 : RangeOk getRow 2051521 575832 576436 :=
  s_576370.append (by norm_num) r_576370
private theorem s_576505 : RangeOk getRow 2051521 575832 576505 :=
  s_576436.append (by norm_num) r_576436
private theorem s_576573 : RangeOk getRow 2051521 575832 576573 :=
  s_576505.append (by norm_num) r_576505
private theorem s_576643 : RangeOk getRow 2051521 575832 576643 :=
  s_576573.append (by norm_num) r_576573
private theorem s_576712 : RangeOk getRow 2051521 575832 576712 :=
  s_576643.append (by norm_num) r_576643
private theorem s_576781 : RangeOk getRow 2051521 575832 576781 :=
  s_576712.append (by norm_num) r_576712
private theorem s_576847 : RangeOk getRow 2051521 575832 576847 :=
  s_576781.append (by norm_num) r_576781
private theorem s_576914 : RangeOk getRow 2051521 575832 576914 :=
  s_576847.append (by norm_num) r_576847
private theorem s_576983 : RangeOk getRow 2051521 575832 576983 :=
  s_576914.append (by norm_num) r_576914
private theorem s_577049 : RangeOk getRow 2051521 575832 577049 :=
  s_576983.append (by norm_num) r_576983
private theorem s_577114 : RangeOk getRow 2051521 575832 577114 :=
  s_577049.append (by norm_num) r_577049
private theorem s_577179 : RangeOk getRow 2051521 575832 577179 :=
  s_577114.append (by norm_num) r_577114
private theorem s_577248 : RangeOk getRow 2051521 575832 577248 :=
  s_577179.append (by norm_num) r_577179
private theorem s_577316 : RangeOk getRow 2051521 575832 577316 :=
  s_577248.append (by norm_num) r_577248
private theorem s_577384 : RangeOk getRow 2051521 575832 577384 :=
  s_577316.append (by norm_num) r_577316
private theorem s_577452 : RangeOk getRow 2051521 575832 577452 :=
  s_577384.append (by norm_num) r_577384
private theorem s_577521 : RangeOk getRow 2051521 575832 577521 :=
  s_577452.append (by norm_num) r_577452
private theorem s_577587 : RangeOk getRow 2051521 575832 577587 :=
  s_577521.append (by norm_num) r_577521
private theorem s_577654 : RangeOk getRow 2051521 575832 577654 :=
  s_577587.append (by norm_num) r_577587
private theorem s_577719 : RangeOk getRow 2051521 575832 577719 :=
  s_577654.append (by norm_num) r_577654
private theorem s_577785 : RangeOk getRow 2051521 575832 577785 :=
  s_577719.append (by norm_num) r_577719
private theorem s_577853 : RangeOk getRow 2051521 575832 577853 :=
  s_577785.append (by norm_num) r_577785
private theorem s_577923 : RangeOk getRow 2051521 575832 577923 :=
  s_577853.append (by norm_num) r_577853
private theorem s_577993 : RangeOk getRow 2051521 575832 577993 :=
  s_577923.append (by norm_num) r_577923
private theorem s_578060 : RangeOk getRow 2051521 575832 578060 :=
  s_577993.append (by norm_num) r_577993
private theorem s_578126 : RangeOk getRow 2051521 575832 578126 :=
  s_578060.append (by norm_num) r_578060

/-- Rows `[575832, 578126)` are valid. -/
theorem rangeOk_575832_578126 : RangeOk getRow 2051521 575832 578126 := s_578126

end Noperthedron.Solution
