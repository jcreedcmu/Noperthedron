import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[649256, 651549). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_649256 : RangeOk getRow 2051521 649256 649321 := by
  decide +kernel

private theorem r_649321 : RangeOk getRow 2051521 649321 649386 := by
  decide +kernel

private theorem r_649386 : RangeOk getRow 2051521 649386 649452 := by
  decide +kernel

private theorem r_649452 : RangeOk getRow 2051521 649452 649517 := by
  decide +kernel

private theorem r_649517 : RangeOk getRow 2051521 649517 649584 := by
  decide +kernel

private theorem r_649584 : RangeOk getRow 2051521 649584 649652 := by
  decide +kernel

private theorem r_649652 : RangeOk getRow 2051521 649652 649720 := by
  decide +kernel

private theorem r_649720 : RangeOk getRow 2051521 649720 649789 := by
  decide +kernel

private theorem r_649789 : RangeOk getRow 2051521 649789 649857 := by
  decide +kernel

private theorem r_649857 : RangeOk getRow 2051521 649857 649925 := by
  decide +kernel

private theorem r_649925 : RangeOk getRow 2051521 649925 649992 := by
  decide +kernel

private theorem r_649992 : RangeOk getRow 2051521 649992 650058 := by
  decide +kernel

private theorem r_650058 : RangeOk getRow 2051521 650058 650123 := by
  decide +kernel

private theorem r_650123 : RangeOk getRow 2051521 650123 650191 := by
  decide +kernel

private theorem r_650191 : RangeOk getRow 2051521 650191 650259 := by
  decide +kernel

private theorem r_650259 : RangeOk getRow 2051521 650259 650329 := by
  decide +kernel

private theorem r_650329 : RangeOk getRow 2051521 650329 650399 := by
  decide +kernel

private theorem r_650399 : RangeOk getRow 2051521 650399 650470 := by
  decide +kernel

private theorem r_650470 : RangeOk getRow 2051521 650470 650539 := by
  decide +kernel

private theorem r_650539 : RangeOk getRow 2051521 650539 650607 := by
  decide +kernel

private theorem r_650607 : RangeOk getRow 2051521 650607 650675 := by
  decide +kernel

private theorem r_650675 : RangeOk getRow 2051521 650675 650743 := by
  decide +kernel

private theorem r_650743 : RangeOk getRow 2051521 650743 650809 := by
  decide +kernel

private theorem r_650809 : RangeOk getRow 2051521 650809 650875 := by
  decide +kernel

private theorem r_650875 : RangeOk getRow 2051521 650875 650944 := by
  decide +kernel

private theorem r_650944 : RangeOk getRow 2051521 650944 651012 := by
  decide +kernel

private theorem r_651012 : RangeOk getRow 2051521 651012 651081 := by
  decide +kernel

private theorem r_651081 : RangeOk getRow 2051521 651081 651150 := by
  decide +kernel

private theorem r_651150 : RangeOk getRow 2051521 651150 651219 := by
  decide +kernel

private theorem r_651219 : RangeOk getRow 2051521 651219 651284 := by
  decide +kernel

private theorem r_651284 : RangeOk getRow 2051521 651284 651351 := by
  decide +kernel

private theorem r_651351 : RangeOk getRow 2051521 651351 651417 := by
  decide +kernel

private theorem r_651417 : RangeOk getRow 2051521 651417 651483 := by
  decide +kernel

private theorem r_651483 : RangeOk getRow 2051521 651483 651549 := by
  decide +kernel

private theorem s_649321 : RangeOk getRow 2051521 649256 649321 := r_649256
private theorem s_649386 : RangeOk getRow 2051521 649256 649386 :=
  s_649321.append (by norm_num) r_649321
private theorem s_649452 : RangeOk getRow 2051521 649256 649452 :=
  s_649386.append (by norm_num) r_649386
private theorem s_649517 : RangeOk getRow 2051521 649256 649517 :=
  s_649452.append (by norm_num) r_649452
private theorem s_649584 : RangeOk getRow 2051521 649256 649584 :=
  s_649517.append (by norm_num) r_649517
private theorem s_649652 : RangeOk getRow 2051521 649256 649652 :=
  s_649584.append (by norm_num) r_649584
private theorem s_649720 : RangeOk getRow 2051521 649256 649720 :=
  s_649652.append (by norm_num) r_649652
private theorem s_649789 : RangeOk getRow 2051521 649256 649789 :=
  s_649720.append (by norm_num) r_649720
private theorem s_649857 : RangeOk getRow 2051521 649256 649857 :=
  s_649789.append (by norm_num) r_649789
private theorem s_649925 : RangeOk getRow 2051521 649256 649925 :=
  s_649857.append (by norm_num) r_649857
private theorem s_649992 : RangeOk getRow 2051521 649256 649992 :=
  s_649925.append (by norm_num) r_649925
private theorem s_650058 : RangeOk getRow 2051521 649256 650058 :=
  s_649992.append (by norm_num) r_649992
private theorem s_650123 : RangeOk getRow 2051521 649256 650123 :=
  s_650058.append (by norm_num) r_650058
private theorem s_650191 : RangeOk getRow 2051521 649256 650191 :=
  s_650123.append (by norm_num) r_650123
private theorem s_650259 : RangeOk getRow 2051521 649256 650259 :=
  s_650191.append (by norm_num) r_650191
private theorem s_650329 : RangeOk getRow 2051521 649256 650329 :=
  s_650259.append (by norm_num) r_650259
private theorem s_650399 : RangeOk getRow 2051521 649256 650399 :=
  s_650329.append (by norm_num) r_650329
private theorem s_650470 : RangeOk getRow 2051521 649256 650470 :=
  s_650399.append (by norm_num) r_650399
private theorem s_650539 : RangeOk getRow 2051521 649256 650539 :=
  s_650470.append (by norm_num) r_650470
private theorem s_650607 : RangeOk getRow 2051521 649256 650607 :=
  s_650539.append (by norm_num) r_650539
private theorem s_650675 : RangeOk getRow 2051521 649256 650675 :=
  s_650607.append (by norm_num) r_650607
private theorem s_650743 : RangeOk getRow 2051521 649256 650743 :=
  s_650675.append (by norm_num) r_650675
private theorem s_650809 : RangeOk getRow 2051521 649256 650809 :=
  s_650743.append (by norm_num) r_650743
private theorem s_650875 : RangeOk getRow 2051521 649256 650875 :=
  s_650809.append (by norm_num) r_650809
private theorem s_650944 : RangeOk getRow 2051521 649256 650944 :=
  s_650875.append (by norm_num) r_650875
private theorem s_651012 : RangeOk getRow 2051521 649256 651012 :=
  s_650944.append (by norm_num) r_650944
private theorem s_651081 : RangeOk getRow 2051521 649256 651081 :=
  s_651012.append (by norm_num) r_651012
private theorem s_651150 : RangeOk getRow 2051521 649256 651150 :=
  s_651081.append (by norm_num) r_651081
private theorem s_651219 : RangeOk getRow 2051521 649256 651219 :=
  s_651150.append (by norm_num) r_651150
private theorem s_651284 : RangeOk getRow 2051521 649256 651284 :=
  s_651219.append (by norm_num) r_651219
private theorem s_651351 : RangeOk getRow 2051521 649256 651351 :=
  s_651284.append (by norm_num) r_651284
private theorem s_651417 : RangeOk getRow 2051521 649256 651417 :=
  s_651351.append (by norm_num) r_651351
private theorem s_651483 : RangeOk getRow 2051521 649256 651483 :=
  s_651417.append (by norm_num) r_651417
private theorem s_651549 : RangeOk getRow 2051521 649256 651549 :=
  s_651483.append (by norm_num) r_651483

/-- Rows `[649256, 651549)` are valid. -/
theorem rangeOk_649256_651549 : RangeOk getRow 2051521 649256 651549 := s_651549

end Noperthedron.Solution
