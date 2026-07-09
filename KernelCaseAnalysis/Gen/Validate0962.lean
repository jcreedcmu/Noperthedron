import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1996957, 1999314). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1996957 : RangeOk getRow 2051521 1996957 1996999 := by
  decide +kernel

private theorem r_1996999 : RangeOk getRow 2051521 1996999 1997056 := by
  decide +kernel

private theorem r_1997056 : RangeOk getRow 2051521 1997056 1997120 := by
  decide +kernel

private theorem r_1997120 : RangeOk getRow 2051521 1997120 1997149 := by
  decide +kernel

private theorem r_1997149 : RangeOk getRow 2051521 1997149 1997191 := by
  decide +kernel

private theorem r_1997191 : RangeOk getRow 2051521 1997191 1997262 := by
  decide +kernel

private theorem r_1997262 : RangeOk getRow 2051521 1997262 1997333 := by
  decide +kernel

private theorem r_1997333 : RangeOk getRow 2051521 1997333 1997399 := by
  decide +kernel

private theorem r_1997399 : RangeOk getRow 2051521 1997399 1997429 := by
  decide +kernel

private theorem r_1997429 : RangeOk getRow 2051521 1997429 1997485 := by
  decide +kernel

private theorem r_1997485 : RangeOk getRow 2051521 1997485 1997549 := by
  decide +kernel

private theorem r_1997549 : RangeOk getRow 2051521 1997549 1997569 := by
  decide +kernel

private theorem r_1997569 : RangeOk getRow 2051521 1997569 1997625 := by
  decide +kernel

private theorem r_1997625 : RangeOk getRow 2051521 1997625 1997695 := by
  decide +kernel

private theorem r_1997695 : RangeOk getRow 2051521 1997695 1997767 := by
  decide +kernel

private theorem r_1997767 : RangeOk getRow 2051521 1997767 1997816 := by
  decide +kernel

private theorem r_1997816 : RangeOk getRow 2051521 1997816 1997878 := by
  decide +kernel

private theorem r_1997878 : RangeOk getRow 2051521 1997878 1997941 := by
  decide +kernel

private theorem r_1997941 : RangeOk getRow 2051521 1997941 1997998 := by
  decide +kernel

private theorem r_1997998 : RangeOk getRow 2051521 1997998 1998040 := by
  decide +kernel

private theorem r_1998040 : RangeOk getRow 2051521 1998040 1998069 := by
  decide +kernel

private theorem r_1998069 : RangeOk getRow 2051521 1998069 1998119 := by
  decide +kernel

private theorem r_1998119 : RangeOk getRow 2051521 1998119 1998169 := by
  decide +kernel

private theorem r_1998169 : RangeOk getRow 2051521 1998169 1998211 := by
  decide +kernel

private theorem r_1998211 : RangeOk getRow 2051521 1998211 1998240 := by
  decide +kernel

private theorem r_1998240 : RangeOk getRow 2051521 1998240 1998287 := by
  decide +kernel

private theorem r_1998287 : RangeOk getRow 2051521 1998287 1998340 := by
  decide +kernel

private theorem r_1998340 : RangeOk getRow 2051521 1998340 1998371 := by
  decide +kernel

private theorem r_1998371 : RangeOk getRow 2051521 1998371 1998435 := by
  decide +kernel

private theorem r_1998435 : RangeOk getRow 2051521 1998435 1998492 := by
  decide +kernel

private theorem r_1998492 : RangeOk getRow 2051521 1998492 1998542 := by
  decide +kernel

private theorem r_1998542 : RangeOk getRow 2051521 1998542 1998599 := by
  decide +kernel

private theorem r_1998599 : RangeOk getRow 2051521 1998599 1998649 := by
  decide +kernel

private theorem r_1998649 : RangeOk getRow 2051521 1998649 1998706 := by
  decide +kernel

private theorem r_1998706 : RangeOk getRow 2051521 1998706 1998762 := by
  decide +kernel

private theorem r_1998762 : RangeOk getRow 2051521 1998762 1998812 := by
  decide +kernel

private theorem r_1998812 : RangeOk getRow 2051521 1998812 1998877 := by
  decide +kernel

private theorem r_1998877 : RangeOk getRow 2051521 1998877 1998933 := by
  decide +kernel

private theorem r_1998933 : RangeOk getRow 2051521 1998933 1998996 := by
  decide +kernel

private theorem r_1998996 : RangeOk getRow 2051521 1998996 1999054 := by
  decide +kernel

private theorem r_1999054 : RangeOk getRow 2051521 1999054 1999111 := by
  decide +kernel

private theorem r_1999111 : RangeOk getRow 2051521 1999111 1999167 := by
  decide +kernel

private theorem r_1999167 : RangeOk getRow 2051521 1999167 1999217 := by
  decide +kernel

private theorem r_1999217 : RangeOk getRow 2051521 1999217 1999253 := by
  decide +kernel

private theorem r_1999253 : RangeOk getRow 2051521 1999253 1999290 := by
  decide +kernel

private theorem r_1999290 : RangeOk getRow 2051521 1999290 1999314 := by
  decide +kernel

private theorem s_1996999 : RangeOk getRow 2051521 1996957 1996999 := r_1996957
private theorem s_1997056 : RangeOk getRow 2051521 1996957 1997056 :=
  s_1996999.append (by norm_num) r_1996999
private theorem s_1997120 : RangeOk getRow 2051521 1996957 1997120 :=
  s_1997056.append (by norm_num) r_1997056
private theorem s_1997149 : RangeOk getRow 2051521 1996957 1997149 :=
  s_1997120.append (by norm_num) r_1997120
private theorem s_1997191 : RangeOk getRow 2051521 1996957 1997191 :=
  s_1997149.append (by norm_num) r_1997149
private theorem s_1997262 : RangeOk getRow 2051521 1996957 1997262 :=
  s_1997191.append (by norm_num) r_1997191
private theorem s_1997333 : RangeOk getRow 2051521 1996957 1997333 :=
  s_1997262.append (by norm_num) r_1997262
private theorem s_1997399 : RangeOk getRow 2051521 1996957 1997399 :=
  s_1997333.append (by norm_num) r_1997333
private theorem s_1997429 : RangeOk getRow 2051521 1996957 1997429 :=
  s_1997399.append (by norm_num) r_1997399
private theorem s_1997485 : RangeOk getRow 2051521 1996957 1997485 :=
  s_1997429.append (by norm_num) r_1997429
private theorem s_1997549 : RangeOk getRow 2051521 1996957 1997549 :=
  s_1997485.append (by norm_num) r_1997485
private theorem s_1997569 : RangeOk getRow 2051521 1996957 1997569 :=
  s_1997549.append (by norm_num) r_1997549
private theorem s_1997625 : RangeOk getRow 2051521 1996957 1997625 :=
  s_1997569.append (by norm_num) r_1997569
private theorem s_1997695 : RangeOk getRow 2051521 1996957 1997695 :=
  s_1997625.append (by norm_num) r_1997625
private theorem s_1997767 : RangeOk getRow 2051521 1996957 1997767 :=
  s_1997695.append (by norm_num) r_1997695
private theorem s_1997816 : RangeOk getRow 2051521 1996957 1997816 :=
  s_1997767.append (by norm_num) r_1997767
private theorem s_1997878 : RangeOk getRow 2051521 1996957 1997878 :=
  s_1997816.append (by norm_num) r_1997816
private theorem s_1997941 : RangeOk getRow 2051521 1996957 1997941 :=
  s_1997878.append (by norm_num) r_1997878
private theorem s_1997998 : RangeOk getRow 2051521 1996957 1997998 :=
  s_1997941.append (by norm_num) r_1997941
private theorem s_1998040 : RangeOk getRow 2051521 1996957 1998040 :=
  s_1997998.append (by norm_num) r_1997998
private theorem s_1998069 : RangeOk getRow 2051521 1996957 1998069 :=
  s_1998040.append (by norm_num) r_1998040
private theorem s_1998119 : RangeOk getRow 2051521 1996957 1998119 :=
  s_1998069.append (by norm_num) r_1998069
private theorem s_1998169 : RangeOk getRow 2051521 1996957 1998169 :=
  s_1998119.append (by norm_num) r_1998119
private theorem s_1998211 : RangeOk getRow 2051521 1996957 1998211 :=
  s_1998169.append (by norm_num) r_1998169
private theorem s_1998240 : RangeOk getRow 2051521 1996957 1998240 :=
  s_1998211.append (by norm_num) r_1998211
private theorem s_1998287 : RangeOk getRow 2051521 1996957 1998287 :=
  s_1998240.append (by norm_num) r_1998240
private theorem s_1998340 : RangeOk getRow 2051521 1996957 1998340 :=
  s_1998287.append (by norm_num) r_1998287
private theorem s_1998371 : RangeOk getRow 2051521 1996957 1998371 :=
  s_1998340.append (by norm_num) r_1998340
private theorem s_1998435 : RangeOk getRow 2051521 1996957 1998435 :=
  s_1998371.append (by norm_num) r_1998371
private theorem s_1998492 : RangeOk getRow 2051521 1996957 1998492 :=
  s_1998435.append (by norm_num) r_1998435
private theorem s_1998542 : RangeOk getRow 2051521 1996957 1998542 :=
  s_1998492.append (by norm_num) r_1998492
private theorem s_1998599 : RangeOk getRow 2051521 1996957 1998599 :=
  s_1998542.append (by norm_num) r_1998542
private theorem s_1998649 : RangeOk getRow 2051521 1996957 1998649 :=
  s_1998599.append (by norm_num) r_1998599
private theorem s_1998706 : RangeOk getRow 2051521 1996957 1998706 :=
  s_1998649.append (by norm_num) r_1998649
private theorem s_1998762 : RangeOk getRow 2051521 1996957 1998762 :=
  s_1998706.append (by norm_num) r_1998706
private theorem s_1998812 : RangeOk getRow 2051521 1996957 1998812 :=
  s_1998762.append (by norm_num) r_1998762
private theorem s_1998877 : RangeOk getRow 2051521 1996957 1998877 :=
  s_1998812.append (by norm_num) r_1998812
private theorem s_1998933 : RangeOk getRow 2051521 1996957 1998933 :=
  s_1998877.append (by norm_num) r_1998877
private theorem s_1998996 : RangeOk getRow 2051521 1996957 1998996 :=
  s_1998933.append (by norm_num) r_1998933
private theorem s_1999054 : RangeOk getRow 2051521 1996957 1999054 :=
  s_1998996.append (by norm_num) r_1998996
private theorem s_1999111 : RangeOk getRow 2051521 1996957 1999111 :=
  s_1999054.append (by norm_num) r_1999054
private theorem s_1999167 : RangeOk getRow 2051521 1996957 1999167 :=
  s_1999111.append (by norm_num) r_1999111
private theorem s_1999217 : RangeOk getRow 2051521 1996957 1999217 :=
  s_1999167.append (by norm_num) r_1999167
private theorem s_1999253 : RangeOk getRow 2051521 1996957 1999253 :=
  s_1999217.append (by norm_num) r_1999217
private theorem s_1999290 : RangeOk getRow 2051521 1996957 1999290 :=
  s_1999253.append (by norm_num) r_1999253
private theorem s_1999314 : RangeOk getRow 2051521 1996957 1999314 :=
  s_1999290.append (by norm_num) r_1999290

/-- Rows `[1996957, 1999314)` are valid. -/
theorem rangeOk_1996957_1999314 : RangeOk getRow 2051521 1996957 1999314 := s_1999314

end Noperthedron.Solution
