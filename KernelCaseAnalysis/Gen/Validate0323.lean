import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[777540, 779751). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_777540 : RangeOk getRow 2051521 777540 777608 := by
  decide +kernel

private theorem r_777608 : RangeOk getRow 2051521 777608 777677 := by
  decide +kernel

private theorem r_777677 : RangeOk getRow 2051521 777677 777745 := by
  decide +kernel

private theorem r_777745 : RangeOk getRow 2051521 777745 777813 := by
  decide +kernel

private theorem r_777813 : RangeOk getRow 2051521 777813 777881 := by
  decide +kernel

private theorem r_777881 : RangeOk getRow 2051521 777881 777948 := by
  decide +kernel

private theorem r_777948 : RangeOk getRow 2051521 777948 778014 := by
  decide +kernel

private theorem r_778014 : RangeOk getRow 2051521 778014 778082 := by
  decide +kernel

private theorem r_778082 : RangeOk getRow 2051521 778082 778147 := by
  decide +kernel

private theorem r_778147 : RangeOk getRow 2051521 778147 778215 := by
  decide +kernel

private theorem r_778215 : RangeOk getRow 2051521 778215 778284 := by
  decide +kernel

private theorem r_778284 : RangeOk getRow 2051521 778284 778352 := by
  decide +kernel

private theorem r_778352 : RangeOk getRow 2051521 778352 778419 := by
  decide +kernel

private theorem r_778419 : RangeOk getRow 2051521 778419 778487 := by
  decide +kernel

private theorem r_778487 : RangeOk getRow 2051521 778487 778553 := by
  decide +kernel

private theorem r_778553 : RangeOk getRow 2051521 778553 778618 := by
  decide +kernel

private theorem r_778618 : RangeOk getRow 2051521 778618 778685 := by
  decide +kernel

private theorem r_778685 : RangeOk getRow 2051521 778685 778751 := by
  decide +kernel

private theorem r_778751 : RangeOk getRow 2051521 778751 778818 := by
  decide +kernel

private theorem r_778818 : RangeOk getRow 2051521 778818 778882 := by
  decide +kernel

private theorem r_778882 : RangeOk getRow 2051521 778882 778947 := by
  decide +kernel

private theorem r_778947 : RangeOk getRow 2051521 778947 779013 := by
  decide +kernel

private theorem r_779013 : RangeOk getRow 2051521 779013 779081 := by
  decide +kernel

private theorem r_779081 : RangeOk getRow 2051521 779081 779147 := by
  decide +kernel

private theorem r_779147 : RangeOk getRow 2051521 779147 779213 := by
  decide +kernel

private theorem r_779213 : RangeOk getRow 2051521 779213 779279 := by
  decide +kernel

private theorem r_779279 : RangeOk getRow 2051521 779279 779346 := by
  decide +kernel

private theorem r_779346 : RangeOk getRow 2051521 779346 779414 := by
  decide +kernel

private theorem r_779414 : RangeOk getRow 2051521 779414 779483 := by
  decide +kernel

private theorem r_779483 : RangeOk getRow 2051521 779483 779551 := by
  decide +kernel

private theorem r_779551 : RangeOk getRow 2051521 779551 779619 := by
  decide +kernel

private theorem r_779619 : RangeOk getRow 2051521 779619 779686 := by
  decide +kernel

private theorem r_779686 : RangeOk getRow 2051521 779686 779751 := by
  decide +kernel

private theorem s_777608 : RangeOk getRow 2051521 777540 777608 := r_777540
private theorem s_777677 : RangeOk getRow 2051521 777540 777677 :=
  s_777608.append (by norm_num) r_777608
private theorem s_777745 : RangeOk getRow 2051521 777540 777745 :=
  s_777677.append (by norm_num) r_777677
private theorem s_777813 : RangeOk getRow 2051521 777540 777813 :=
  s_777745.append (by norm_num) r_777745
private theorem s_777881 : RangeOk getRow 2051521 777540 777881 :=
  s_777813.append (by norm_num) r_777813
private theorem s_777948 : RangeOk getRow 2051521 777540 777948 :=
  s_777881.append (by norm_num) r_777881
private theorem s_778014 : RangeOk getRow 2051521 777540 778014 :=
  s_777948.append (by norm_num) r_777948
private theorem s_778082 : RangeOk getRow 2051521 777540 778082 :=
  s_778014.append (by norm_num) r_778014
private theorem s_778147 : RangeOk getRow 2051521 777540 778147 :=
  s_778082.append (by norm_num) r_778082
private theorem s_778215 : RangeOk getRow 2051521 777540 778215 :=
  s_778147.append (by norm_num) r_778147
private theorem s_778284 : RangeOk getRow 2051521 777540 778284 :=
  s_778215.append (by norm_num) r_778215
private theorem s_778352 : RangeOk getRow 2051521 777540 778352 :=
  s_778284.append (by norm_num) r_778284
private theorem s_778419 : RangeOk getRow 2051521 777540 778419 :=
  s_778352.append (by norm_num) r_778352
private theorem s_778487 : RangeOk getRow 2051521 777540 778487 :=
  s_778419.append (by norm_num) r_778419
private theorem s_778553 : RangeOk getRow 2051521 777540 778553 :=
  s_778487.append (by norm_num) r_778487
private theorem s_778618 : RangeOk getRow 2051521 777540 778618 :=
  s_778553.append (by norm_num) r_778553
private theorem s_778685 : RangeOk getRow 2051521 777540 778685 :=
  s_778618.append (by norm_num) r_778618
private theorem s_778751 : RangeOk getRow 2051521 777540 778751 :=
  s_778685.append (by norm_num) r_778685
private theorem s_778818 : RangeOk getRow 2051521 777540 778818 :=
  s_778751.append (by norm_num) r_778751
private theorem s_778882 : RangeOk getRow 2051521 777540 778882 :=
  s_778818.append (by norm_num) r_778818
private theorem s_778947 : RangeOk getRow 2051521 777540 778947 :=
  s_778882.append (by norm_num) r_778882
private theorem s_779013 : RangeOk getRow 2051521 777540 779013 :=
  s_778947.append (by norm_num) r_778947
private theorem s_779081 : RangeOk getRow 2051521 777540 779081 :=
  s_779013.append (by norm_num) r_779013
private theorem s_779147 : RangeOk getRow 2051521 777540 779147 :=
  s_779081.append (by norm_num) r_779081
private theorem s_779213 : RangeOk getRow 2051521 777540 779213 :=
  s_779147.append (by norm_num) r_779147
private theorem s_779279 : RangeOk getRow 2051521 777540 779279 :=
  s_779213.append (by norm_num) r_779213
private theorem s_779346 : RangeOk getRow 2051521 777540 779346 :=
  s_779279.append (by norm_num) r_779279
private theorem s_779414 : RangeOk getRow 2051521 777540 779414 :=
  s_779346.append (by norm_num) r_779346
private theorem s_779483 : RangeOk getRow 2051521 777540 779483 :=
  s_779414.append (by norm_num) r_779414
private theorem s_779551 : RangeOk getRow 2051521 777540 779551 :=
  s_779483.append (by norm_num) r_779483
private theorem s_779619 : RangeOk getRow 2051521 777540 779619 :=
  s_779551.append (by norm_num) r_779551
private theorem s_779686 : RangeOk getRow 2051521 777540 779686 :=
  s_779619.append (by norm_num) r_779619
private theorem s_779751 : RangeOk getRow 2051521 777540 779751 :=
  s_779686.append (by norm_num) r_779686

/-- Rows `[777540, 779751)` are valid. -/
theorem rangeOk_777540_779751 : RangeOk getRow 2051521 777540 779751 := s_779751

end Noperthedron.Solution
