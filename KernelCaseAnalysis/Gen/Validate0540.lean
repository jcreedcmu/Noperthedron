import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1315061, 1318035). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1315061 : RangeOk getRow 2051521 1315061 1315132 := by
  decide +kernel

private theorem r_1315132 : RangeOk getRow 2051521 1315132 1315203 := by
  decide +kernel

private theorem r_1315203 : RangeOk getRow 2051521 1315203 1315276 := by
  decide +kernel

private theorem r_1315276 : RangeOk getRow 2051521 1315276 1315349 := by
  decide +kernel

private theorem r_1315349 : RangeOk getRow 2051521 1315349 1315422 := by
  decide +kernel

private theorem r_1315422 : RangeOk getRow 2051521 1315422 1315496 := by
  decide +kernel

private theorem r_1315496 : RangeOk getRow 2051521 1315496 1315568 := by
  decide +kernel

private theorem r_1315568 : RangeOk getRow 2051521 1315568 1315641 := by
  decide +kernel

private theorem r_1315641 : RangeOk getRow 2051521 1315641 1315713 := by
  decide +kernel

private theorem r_1315713 : RangeOk getRow 2051521 1315713 1315785 := by
  decide +kernel

private theorem r_1315785 : RangeOk getRow 2051521 1315785 1315857 := by
  decide +kernel

private theorem r_1315857 : RangeOk getRow 2051521 1315857 1315928 := by
  decide +kernel

private theorem r_1315928 : RangeOk getRow 2051521 1315928 1315998 := by
  decide +kernel

private theorem r_1315998 : RangeOk getRow 2051521 1315998 1316068 := by
  decide +kernel

private theorem r_1316068 : RangeOk getRow 2051521 1316068 1316141 := by
  decide +kernel

private theorem r_1316141 : RangeOk getRow 2051521 1316141 1316211 := by
  decide +kernel

private theorem r_1316211 : RangeOk getRow 2051521 1316211 1316281 := by
  decide +kernel

private theorem r_1316281 : RangeOk getRow 2051521 1316281 1316352 := by
  decide +kernel

private theorem r_1316352 : RangeOk getRow 2051521 1316352 1316423 := by
  decide +kernel

private theorem r_1316423 : RangeOk getRow 2051521 1316423 1316496 := by
  decide +kernel

private theorem r_1316496 : RangeOk getRow 2051521 1316496 1316570 := by
  decide +kernel

private theorem r_1316570 : RangeOk getRow 2051521 1316570 1316607 := by
  decide +kernel

private theorem r_1316607 : RangeOk getRow 2051521 1316607 1316644 := by
  decide +kernel

private theorem r_1316644 : RangeOk getRow 2051521 1316644 1316681 := by
  decide +kernel

private theorem r_1316681 : RangeOk getRow 2051521 1316681 1316712 := by
  decide +kernel

private theorem r_1316712 : RangeOk getRow 2051521 1316712 1316743 := by
  decide +kernel

private theorem r_1316743 : RangeOk getRow 2051521 1316743 1316801 := by
  decide +kernel

private theorem r_1316801 : RangeOk getRow 2051521 1316801 1316873 := by
  decide +kernel

private theorem r_1316873 : RangeOk getRow 2051521 1316873 1316947 := by
  decide +kernel

private theorem r_1316947 : RangeOk getRow 2051521 1316947 1317016 := by
  decide +kernel

private theorem r_1317016 : RangeOk getRow 2051521 1317016 1317087 := by
  decide +kernel

private theorem r_1317087 : RangeOk getRow 2051521 1317087 1317144 := by
  decide +kernel

private theorem r_1317144 : RangeOk getRow 2051521 1317144 1317196 := by
  decide +kernel

private theorem r_1317196 : RangeOk getRow 2051521 1317196 1317260 := by
  decide +kernel

private theorem r_1317260 : RangeOk getRow 2051521 1317260 1317331 := by
  decide +kernel

private theorem r_1317331 : RangeOk getRow 2051521 1317331 1317392 := by
  decide +kernel

private theorem r_1317392 : RangeOk getRow 2051521 1317392 1317449 := by
  decide +kernel

private theorem r_1317449 : RangeOk getRow 2051521 1317449 1317511 := by
  decide +kernel

private theorem r_1317511 : RangeOk getRow 2051521 1317511 1317579 := by
  decide +kernel

private theorem r_1317579 : RangeOk getRow 2051521 1317579 1317619 := by
  decide +kernel

private theorem r_1317619 : RangeOk getRow 2051521 1317619 1317645 := by
  decide +kernel

private theorem r_1317645 : RangeOk getRow 2051521 1317645 1317706 := by
  decide +kernel

private theorem r_1317706 : RangeOk getRow 2051521 1317706 1317761 := by
  decide +kernel

private theorem r_1317761 : RangeOk getRow 2051521 1317761 1317813 := by
  decide +kernel

private theorem r_1317813 : RangeOk getRow 2051521 1317813 1317862 := by
  decide +kernel

private theorem r_1317862 : RangeOk getRow 2051521 1317862 1317923 := by
  decide +kernel

private theorem r_1317923 : RangeOk getRow 2051521 1317923 1317985 := by
  decide +kernel

private theorem r_1317985 : RangeOk getRow 2051521 1317985 1318035 := by
  decide +kernel

private theorem s_1315132 : RangeOk getRow 2051521 1315061 1315132 := r_1315061
private theorem s_1315203 : RangeOk getRow 2051521 1315061 1315203 :=
  s_1315132.append (by norm_num) r_1315132
private theorem s_1315276 : RangeOk getRow 2051521 1315061 1315276 :=
  s_1315203.append (by norm_num) r_1315203
private theorem s_1315349 : RangeOk getRow 2051521 1315061 1315349 :=
  s_1315276.append (by norm_num) r_1315276
private theorem s_1315422 : RangeOk getRow 2051521 1315061 1315422 :=
  s_1315349.append (by norm_num) r_1315349
private theorem s_1315496 : RangeOk getRow 2051521 1315061 1315496 :=
  s_1315422.append (by norm_num) r_1315422
private theorem s_1315568 : RangeOk getRow 2051521 1315061 1315568 :=
  s_1315496.append (by norm_num) r_1315496
private theorem s_1315641 : RangeOk getRow 2051521 1315061 1315641 :=
  s_1315568.append (by norm_num) r_1315568
private theorem s_1315713 : RangeOk getRow 2051521 1315061 1315713 :=
  s_1315641.append (by norm_num) r_1315641
private theorem s_1315785 : RangeOk getRow 2051521 1315061 1315785 :=
  s_1315713.append (by norm_num) r_1315713
private theorem s_1315857 : RangeOk getRow 2051521 1315061 1315857 :=
  s_1315785.append (by norm_num) r_1315785
private theorem s_1315928 : RangeOk getRow 2051521 1315061 1315928 :=
  s_1315857.append (by norm_num) r_1315857
private theorem s_1315998 : RangeOk getRow 2051521 1315061 1315998 :=
  s_1315928.append (by norm_num) r_1315928
private theorem s_1316068 : RangeOk getRow 2051521 1315061 1316068 :=
  s_1315998.append (by norm_num) r_1315998
private theorem s_1316141 : RangeOk getRow 2051521 1315061 1316141 :=
  s_1316068.append (by norm_num) r_1316068
private theorem s_1316211 : RangeOk getRow 2051521 1315061 1316211 :=
  s_1316141.append (by norm_num) r_1316141
private theorem s_1316281 : RangeOk getRow 2051521 1315061 1316281 :=
  s_1316211.append (by norm_num) r_1316211
private theorem s_1316352 : RangeOk getRow 2051521 1315061 1316352 :=
  s_1316281.append (by norm_num) r_1316281
private theorem s_1316423 : RangeOk getRow 2051521 1315061 1316423 :=
  s_1316352.append (by norm_num) r_1316352
private theorem s_1316496 : RangeOk getRow 2051521 1315061 1316496 :=
  s_1316423.append (by norm_num) r_1316423
private theorem s_1316570 : RangeOk getRow 2051521 1315061 1316570 :=
  s_1316496.append (by norm_num) r_1316496
private theorem s_1316607 : RangeOk getRow 2051521 1315061 1316607 :=
  s_1316570.append (by norm_num) r_1316570
private theorem s_1316644 : RangeOk getRow 2051521 1315061 1316644 :=
  s_1316607.append (by norm_num) r_1316607
private theorem s_1316681 : RangeOk getRow 2051521 1315061 1316681 :=
  s_1316644.append (by norm_num) r_1316644
private theorem s_1316712 : RangeOk getRow 2051521 1315061 1316712 :=
  s_1316681.append (by norm_num) r_1316681
private theorem s_1316743 : RangeOk getRow 2051521 1315061 1316743 :=
  s_1316712.append (by norm_num) r_1316712
private theorem s_1316801 : RangeOk getRow 2051521 1315061 1316801 :=
  s_1316743.append (by norm_num) r_1316743
private theorem s_1316873 : RangeOk getRow 2051521 1315061 1316873 :=
  s_1316801.append (by norm_num) r_1316801
private theorem s_1316947 : RangeOk getRow 2051521 1315061 1316947 :=
  s_1316873.append (by norm_num) r_1316873
private theorem s_1317016 : RangeOk getRow 2051521 1315061 1317016 :=
  s_1316947.append (by norm_num) r_1316947
private theorem s_1317087 : RangeOk getRow 2051521 1315061 1317087 :=
  s_1317016.append (by norm_num) r_1317016
private theorem s_1317144 : RangeOk getRow 2051521 1315061 1317144 :=
  s_1317087.append (by norm_num) r_1317087
private theorem s_1317196 : RangeOk getRow 2051521 1315061 1317196 :=
  s_1317144.append (by norm_num) r_1317144
private theorem s_1317260 : RangeOk getRow 2051521 1315061 1317260 :=
  s_1317196.append (by norm_num) r_1317196
private theorem s_1317331 : RangeOk getRow 2051521 1315061 1317331 :=
  s_1317260.append (by norm_num) r_1317260
private theorem s_1317392 : RangeOk getRow 2051521 1315061 1317392 :=
  s_1317331.append (by norm_num) r_1317331
private theorem s_1317449 : RangeOk getRow 2051521 1315061 1317449 :=
  s_1317392.append (by norm_num) r_1317392
private theorem s_1317511 : RangeOk getRow 2051521 1315061 1317511 :=
  s_1317449.append (by norm_num) r_1317449
private theorem s_1317579 : RangeOk getRow 2051521 1315061 1317579 :=
  s_1317511.append (by norm_num) r_1317511
private theorem s_1317619 : RangeOk getRow 2051521 1315061 1317619 :=
  s_1317579.append (by norm_num) r_1317579
private theorem s_1317645 : RangeOk getRow 2051521 1315061 1317645 :=
  s_1317619.append (by norm_num) r_1317619
private theorem s_1317706 : RangeOk getRow 2051521 1315061 1317706 :=
  s_1317645.append (by norm_num) r_1317645
private theorem s_1317761 : RangeOk getRow 2051521 1315061 1317761 :=
  s_1317706.append (by norm_num) r_1317706
private theorem s_1317813 : RangeOk getRow 2051521 1315061 1317813 :=
  s_1317761.append (by norm_num) r_1317761
private theorem s_1317862 : RangeOk getRow 2051521 1315061 1317862 :=
  s_1317813.append (by norm_num) r_1317813
private theorem s_1317923 : RangeOk getRow 2051521 1315061 1317923 :=
  s_1317862.append (by norm_num) r_1317862
private theorem s_1317985 : RangeOk getRow 2051521 1315061 1317985 :=
  s_1317923.append (by norm_num) r_1317923
private theorem s_1318035 : RangeOk getRow 2051521 1315061 1318035 :=
  s_1317985.append (by norm_num) r_1317985

/-- Rows `[1315061, 1318035)` are valid. -/
theorem rangeOk_1315061_1318035 : RangeOk getRow 2051521 1315061 1318035 := s_1318035

end Noperthedron.Solution
