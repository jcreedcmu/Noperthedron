import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[913305, 915752). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_913305 : RangeOk getRow 2051521 913305 913373 := by
  decide +kernel

private theorem r_913373 : RangeOk getRow 2051521 913373 913444 := by
  decide +kernel

private theorem r_913444 : RangeOk getRow 2051521 913444 913512 := by
  decide +kernel

private theorem r_913512 : RangeOk getRow 2051521 913512 913582 := by
  decide +kernel

private theorem r_913582 : RangeOk getRow 2051521 913582 913653 := by
  decide +kernel

private theorem r_913653 : RangeOk getRow 2051521 913653 913721 := by
  decide +kernel

private theorem r_913721 : RangeOk getRow 2051521 913721 913786 := by
  decide +kernel

private theorem r_913786 : RangeOk getRow 2051521 913786 913856 := by
  decide +kernel

private theorem r_913856 : RangeOk getRow 2051521 913856 913924 := by
  decide +kernel

private theorem r_913924 : RangeOk getRow 2051521 913924 913991 := by
  decide +kernel

private theorem r_913991 : RangeOk getRow 2051521 913991 914057 := by
  decide +kernel

private theorem r_914057 : RangeOk getRow 2051521 914057 914124 := by
  decide +kernel

private theorem r_914124 : RangeOk getRow 2051521 914124 914191 := by
  decide +kernel

private theorem r_914191 : RangeOk getRow 2051521 914191 914259 := by
  decide +kernel

private theorem r_914259 : RangeOk getRow 2051521 914259 914327 := by
  decide +kernel

private theorem r_914327 : RangeOk getRow 2051521 914327 914394 := by
  decide +kernel

private theorem r_914394 : RangeOk getRow 2051521 914394 914462 := by
  decide +kernel

private theorem r_914462 : RangeOk getRow 2051521 914462 914530 := by
  decide +kernel

private theorem r_914530 : RangeOk getRow 2051521 914530 914602 := by
  decide +kernel

private theorem r_914602 : RangeOk getRow 2051521 914602 914670 := by
  decide +kernel

private theorem r_914670 : RangeOk getRow 2051521 914670 914735 := by
  decide +kernel

private theorem r_914735 : RangeOk getRow 2051521 914735 914805 := by
  decide +kernel

private theorem r_914805 : RangeOk getRow 2051521 914805 914872 := by
  decide +kernel

private theorem r_914872 : RangeOk getRow 2051521 914872 914939 := by
  decide +kernel

private theorem r_914939 : RangeOk getRow 2051521 914939 915005 := by
  decide +kernel

private theorem r_915005 : RangeOk getRow 2051521 915005 915071 := by
  decide +kernel

private theorem r_915071 : RangeOk getRow 2051521 915071 915137 := by
  decide +kernel

private theorem r_915137 : RangeOk getRow 2051521 915137 915205 := by
  decide +kernel

private theorem r_915205 : RangeOk getRow 2051521 915205 915275 := by
  decide +kernel

private theorem r_915275 : RangeOk getRow 2051521 915275 915346 := by
  decide +kernel

private theorem r_915346 : RangeOk getRow 2051521 915346 915414 := by
  decide +kernel

private theorem r_915414 : RangeOk getRow 2051521 915414 915481 := by
  decide +kernel

private theorem r_915481 : RangeOk getRow 2051521 915481 915548 := by
  decide +kernel

private theorem r_915548 : RangeOk getRow 2051521 915548 915615 := by
  decide +kernel

private theorem r_915615 : RangeOk getRow 2051521 915615 915685 := by
  decide +kernel

private theorem r_915685 : RangeOk getRow 2051521 915685 915752 := by
  decide +kernel

private theorem s_913373 : RangeOk getRow 2051521 913305 913373 := r_913305
private theorem s_913444 : RangeOk getRow 2051521 913305 913444 :=
  s_913373.append (by norm_num) r_913373
private theorem s_913512 : RangeOk getRow 2051521 913305 913512 :=
  s_913444.append (by norm_num) r_913444
private theorem s_913582 : RangeOk getRow 2051521 913305 913582 :=
  s_913512.append (by norm_num) r_913512
private theorem s_913653 : RangeOk getRow 2051521 913305 913653 :=
  s_913582.append (by norm_num) r_913582
private theorem s_913721 : RangeOk getRow 2051521 913305 913721 :=
  s_913653.append (by norm_num) r_913653
private theorem s_913786 : RangeOk getRow 2051521 913305 913786 :=
  s_913721.append (by norm_num) r_913721
private theorem s_913856 : RangeOk getRow 2051521 913305 913856 :=
  s_913786.append (by norm_num) r_913786
private theorem s_913924 : RangeOk getRow 2051521 913305 913924 :=
  s_913856.append (by norm_num) r_913856
private theorem s_913991 : RangeOk getRow 2051521 913305 913991 :=
  s_913924.append (by norm_num) r_913924
private theorem s_914057 : RangeOk getRow 2051521 913305 914057 :=
  s_913991.append (by norm_num) r_913991
private theorem s_914124 : RangeOk getRow 2051521 913305 914124 :=
  s_914057.append (by norm_num) r_914057
private theorem s_914191 : RangeOk getRow 2051521 913305 914191 :=
  s_914124.append (by norm_num) r_914124
private theorem s_914259 : RangeOk getRow 2051521 913305 914259 :=
  s_914191.append (by norm_num) r_914191
private theorem s_914327 : RangeOk getRow 2051521 913305 914327 :=
  s_914259.append (by norm_num) r_914259
private theorem s_914394 : RangeOk getRow 2051521 913305 914394 :=
  s_914327.append (by norm_num) r_914327
private theorem s_914462 : RangeOk getRow 2051521 913305 914462 :=
  s_914394.append (by norm_num) r_914394
private theorem s_914530 : RangeOk getRow 2051521 913305 914530 :=
  s_914462.append (by norm_num) r_914462
private theorem s_914602 : RangeOk getRow 2051521 913305 914602 :=
  s_914530.append (by norm_num) r_914530
private theorem s_914670 : RangeOk getRow 2051521 913305 914670 :=
  s_914602.append (by norm_num) r_914602
private theorem s_914735 : RangeOk getRow 2051521 913305 914735 :=
  s_914670.append (by norm_num) r_914670
private theorem s_914805 : RangeOk getRow 2051521 913305 914805 :=
  s_914735.append (by norm_num) r_914735
private theorem s_914872 : RangeOk getRow 2051521 913305 914872 :=
  s_914805.append (by norm_num) r_914805
private theorem s_914939 : RangeOk getRow 2051521 913305 914939 :=
  s_914872.append (by norm_num) r_914872
private theorem s_915005 : RangeOk getRow 2051521 913305 915005 :=
  s_914939.append (by norm_num) r_914939
private theorem s_915071 : RangeOk getRow 2051521 913305 915071 :=
  s_915005.append (by norm_num) r_915005
private theorem s_915137 : RangeOk getRow 2051521 913305 915137 :=
  s_915071.append (by norm_num) r_915071
private theorem s_915205 : RangeOk getRow 2051521 913305 915205 :=
  s_915137.append (by norm_num) r_915137
private theorem s_915275 : RangeOk getRow 2051521 913305 915275 :=
  s_915205.append (by norm_num) r_915205
private theorem s_915346 : RangeOk getRow 2051521 913305 915346 :=
  s_915275.append (by norm_num) r_915275
private theorem s_915414 : RangeOk getRow 2051521 913305 915414 :=
  s_915346.append (by norm_num) r_915346
private theorem s_915481 : RangeOk getRow 2051521 913305 915481 :=
  s_915414.append (by norm_num) r_915414
private theorem s_915548 : RangeOk getRow 2051521 913305 915548 :=
  s_915481.append (by norm_num) r_915481
private theorem s_915615 : RangeOk getRow 2051521 913305 915615 :=
  s_915548.append (by norm_num) r_915548
private theorem s_915685 : RangeOk getRow 2051521 913305 915685 :=
  s_915615.append (by norm_num) r_915615
private theorem s_915752 : RangeOk getRow 2051521 913305 915752 :=
  s_915685.append (by norm_num) r_915685

/-- Rows `[913305, 915752)` are valid. -/
theorem rangeOk_913305_915752 : RangeOk getRow 2051521 913305 915752 := s_915752

end Noperthedron.Solution
