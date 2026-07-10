import KernelCaseAnalysis.Gen.Dispatch

/-! GENERATED (scripts/gen_kernel_chunks.py): kernel validation of rows
[1201241, 1204148). -/

namespace Noperthedron.Solution

set_option Elab.async false

private theorem r_1201241 : RangeOk getRow 2051521 1201241 1201312 := by
  decide +kernel

private theorem r_1201312 : RangeOk getRow 2051521 1201312 1201383 := by
  decide +kernel

private theorem r_1201383 : RangeOk getRow 2051521 1201383 1201450 := by
  decide +kernel

private theorem r_1201450 : RangeOk getRow 2051521 1201450 1201519 := by
  decide +kernel

private theorem r_1201519 : RangeOk getRow 2051521 1201519 1201588 := by
  decide +kernel

private theorem r_1201588 : RangeOk getRow 2051521 1201588 1201658 := by
  decide +kernel

private theorem r_1201658 : RangeOk getRow 2051521 1201658 1201729 := by
  decide +kernel

private theorem r_1201729 : RangeOk getRow 2051521 1201729 1201800 := by
  decide +kernel

private theorem r_1201800 : RangeOk getRow 2051521 1201800 1201868 := by
  decide +kernel

private theorem r_1201868 : RangeOk getRow 2051521 1201868 1201940 := by
  decide +kernel

private theorem r_1201940 : RangeOk getRow 2051521 1201940 1202012 := by
  decide +kernel

private theorem r_1202012 : RangeOk getRow 2051521 1202012 1202084 := by
  decide +kernel

private theorem r_1202084 : RangeOk getRow 2051521 1202084 1202156 := by
  decide +kernel

private theorem r_1202156 : RangeOk getRow 2051521 1202156 1202228 := by
  decide +kernel

private theorem r_1202228 : RangeOk getRow 2051521 1202228 1202300 := by
  decide +kernel

private theorem r_1202300 : RangeOk getRow 2051521 1202300 1202372 := by
  decide +kernel

private theorem r_1202372 : RangeOk getRow 2051521 1202372 1202444 := by
  decide +kernel

private theorem r_1202444 : RangeOk getRow 2051521 1202444 1202516 := by
  decide +kernel

private theorem r_1202516 : RangeOk getRow 2051521 1202516 1202588 := by
  decide +kernel

private theorem r_1202588 : RangeOk getRow 2051521 1202588 1202660 := by
  decide +kernel

private theorem r_1202660 : RangeOk getRow 2051521 1202660 1202729 := by
  decide +kernel

private theorem r_1202729 : RangeOk getRow 2051521 1202729 1202796 := by
  decide +kernel

private theorem r_1202796 : RangeOk getRow 2051521 1202796 1202866 := by
  decide +kernel

private theorem r_1202866 : RangeOk getRow 2051521 1202866 1202936 := by
  decide +kernel

private theorem r_1202936 : RangeOk getRow 2051521 1202936 1203009 := by
  decide +kernel

private theorem r_1203009 : RangeOk getRow 2051521 1203009 1203083 := by
  decide +kernel

private theorem r_1203083 : RangeOk getRow 2051521 1203083 1203154 := by
  decide +kernel

private theorem r_1203154 : RangeOk getRow 2051521 1203154 1203227 := by
  decide +kernel

private theorem r_1203227 : RangeOk getRow 2051521 1203227 1203299 := by
  decide +kernel

private theorem r_1203299 : RangeOk getRow 2051521 1203299 1203371 := by
  decide +kernel

private theorem r_1203371 : RangeOk getRow 2051521 1203371 1203442 := by
  decide +kernel

private theorem r_1203442 : RangeOk getRow 2051521 1203442 1203514 := by
  decide +kernel

private theorem r_1203514 : RangeOk getRow 2051521 1203514 1203586 := by
  decide +kernel

private theorem r_1203586 : RangeOk getRow 2051521 1203586 1203658 := by
  decide +kernel

private theorem r_1203658 : RangeOk getRow 2051521 1203658 1203730 := by
  decide +kernel

private theorem r_1203730 : RangeOk getRow 2051521 1203730 1203798 := by
  decide +kernel

private theorem r_1203798 : RangeOk getRow 2051521 1203798 1203860 := by
  decide +kernel

private theorem r_1203860 : RangeOk getRow 2051521 1203860 1203911 := by
  decide +kernel

private theorem r_1203911 : RangeOk getRow 2051521 1203911 1203975 := by
  decide +kernel

private theorem r_1203975 : RangeOk getRow 2051521 1203975 1203988 := by
  decide +kernel

private theorem r_1203988 : RangeOk getRow 2051521 1203988 1203997 := by
  decide +kernel

private theorem r_1203997 : RangeOk getRow 2051521 1203997 1204011 := by
  decide +kernel

private theorem r_1204011 : RangeOk getRow 2051521 1204011 1204023 := by
  decide +kernel

private theorem r_1204023 : RangeOk getRow 2051521 1204023 1204036 := by
  decide +kernel

private theorem r_1204036 : RangeOk getRow 2051521 1204036 1204056 := by
  decide +kernel

private theorem r_1204056 : RangeOk getRow 2051521 1204056 1204065 := by
  decide +kernel

private theorem r_1204065 : RangeOk getRow 2051521 1204065 1204097 := by
  decide +kernel

private theorem r_1204097 : RangeOk getRow 2051521 1204097 1204148 := by
  decide +kernel

private theorem s_1201312 : RangeOk getRow 2051521 1201241 1201312 := r_1201241
private theorem s_1201383 : RangeOk getRow 2051521 1201241 1201383 :=
  s_1201312.append (by norm_num) r_1201312
private theorem s_1201450 : RangeOk getRow 2051521 1201241 1201450 :=
  s_1201383.append (by norm_num) r_1201383
private theorem s_1201519 : RangeOk getRow 2051521 1201241 1201519 :=
  s_1201450.append (by norm_num) r_1201450
private theorem s_1201588 : RangeOk getRow 2051521 1201241 1201588 :=
  s_1201519.append (by norm_num) r_1201519
private theorem s_1201658 : RangeOk getRow 2051521 1201241 1201658 :=
  s_1201588.append (by norm_num) r_1201588
private theorem s_1201729 : RangeOk getRow 2051521 1201241 1201729 :=
  s_1201658.append (by norm_num) r_1201658
private theorem s_1201800 : RangeOk getRow 2051521 1201241 1201800 :=
  s_1201729.append (by norm_num) r_1201729
private theorem s_1201868 : RangeOk getRow 2051521 1201241 1201868 :=
  s_1201800.append (by norm_num) r_1201800
private theorem s_1201940 : RangeOk getRow 2051521 1201241 1201940 :=
  s_1201868.append (by norm_num) r_1201868
private theorem s_1202012 : RangeOk getRow 2051521 1201241 1202012 :=
  s_1201940.append (by norm_num) r_1201940
private theorem s_1202084 : RangeOk getRow 2051521 1201241 1202084 :=
  s_1202012.append (by norm_num) r_1202012
private theorem s_1202156 : RangeOk getRow 2051521 1201241 1202156 :=
  s_1202084.append (by norm_num) r_1202084
private theorem s_1202228 : RangeOk getRow 2051521 1201241 1202228 :=
  s_1202156.append (by norm_num) r_1202156
private theorem s_1202300 : RangeOk getRow 2051521 1201241 1202300 :=
  s_1202228.append (by norm_num) r_1202228
private theorem s_1202372 : RangeOk getRow 2051521 1201241 1202372 :=
  s_1202300.append (by norm_num) r_1202300
private theorem s_1202444 : RangeOk getRow 2051521 1201241 1202444 :=
  s_1202372.append (by norm_num) r_1202372
private theorem s_1202516 : RangeOk getRow 2051521 1201241 1202516 :=
  s_1202444.append (by norm_num) r_1202444
private theorem s_1202588 : RangeOk getRow 2051521 1201241 1202588 :=
  s_1202516.append (by norm_num) r_1202516
private theorem s_1202660 : RangeOk getRow 2051521 1201241 1202660 :=
  s_1202588.append (by norm_num) r_1202588
private theorem s_1202729 : RangeOk getRow 2051521 1201241 1202729 :=
  s_1202660.append (by norm_num) r_1202660
private theorem s_1202796 : RangeOk getRow 2051521 1201241 1202796 :=
  s_1202729.append (by norm_num) r_1202729
private theorem s_1202866 : RangeOk getRow 2051521 1201241 1202866 :=
  s_1202796.append (by norm_num) r_1202796
private theorem s_1202936 : RangeOk getRow 2051521 1201241 1202936 :=
  s_1202866.append (by norm_num) r_1202866
private theorem s_1203009 : RangeOk getRow 2051521 1201241 1203009 :=
  s_1202936.append (by norm_num) r_1202936
private theorem s_1203083 : RangeOk getRow 2051521 1201241 1203083 :=
  s_1203009.append (by norm_num) r_1203009
private theorem s_1203154 : RangeOk getRow 2051521 1201241 1203154 :=
  s_1203083.append (by norm_num) r_1203083
private theorem s_1203227 : RangeOk getRow 2051521 1201241 1203227 :=
  s_1203154.append (by norm_num) r_1203154
private theorem s_1203299 : RangeOk getRow 2051521 1201241 1203299 :=
  s_1203227.append (by norm_num) r_1203227
private theorem s_1203371 : RangeOk getRow 2051521 1201241 1203371 :=
  s_1203299.append (by norm_num) r_1203299
private theorem s_1203442 : RangeOk getRow 2051521 1201241 1203442 :=
  s_1203371.append (by norm_num) r_1203371
private theorem s_1203514 : RangeOk getRow 2051521 1201241 1203514 :=
  s_1203442.append (by norm_num) r_1203442
private theorem s_1203586 : RangeOk getRow 2051521 1201241 1203586 :=
  s_1203514.append (by norm_num) r_1203514
private theorem s_1203658 : RangeOk getRow 2051521 1201241 1203658 :=
  s_1203586.append (by norm_num) r_1203586
private theorem s_1203730 : RangeOk getRow 2051521 1201241 1203730 :=
  s_1203658.append (by norm_num) r_1203658
private theorem s_1203798 : RangeOk getRow 2051521 1201241 1203798 :=
  s_1203730.append (by norm_num) r_1203730
private theorem s_1203860 : RangeOk getRow 2051521 1201241 1203860 :=
  s_1203798.append (by norm_num) r_1203798
private theorem s_1203911 : RangeOk getRow 2051521 1201241 1203911 :=
  s_1203860.append (by norm_num) r_1203860
private theorem s_1203975 : RangeOk getRow 2051521 1201241 1203975 :=
  s_1203911.append (by norm_num) r_1203911
private theorem s_1203988 : RangeOk getRow 2051521 1201241 1203988 :=
  s_1203975.append (by norm_num) r_1203975
private theorem s_1203997 : RangeOk getRow 2051521 1201241 1203997 :=
  s_1203988.append (by norm_num) r_1203988
private theorem s_1204011 : RangeOk getRow 2051521 1201241 1204011 :=
  s_1203997.append (by norm_num) r_1203997
private theorem s_1204023 : RangeOk getRow 2051521 1201241 1204023 :=
  s_1204011.append (by norm_num) r_1204011
private theorem s_1204036 : RangeOk getRow 2051521 1201241 1204036 :=
  s_1204023.append (by norm_num) r_1204023
private theorem s_1204056 : RangeOk getRow 2051521 1201241 1204056 :=
  s_1204036.append (by norm_num) r_1204036
private theorem s_1204065 : RangeOk getRow 2051521 1201241 1204065 :=
  s_1204056.append (by norm_num) r_1204056
private theorem s_1204097 : RangeOk getRow 2051521 1201241 1204097 :=
  s_1204065.append (by norm_num) r_1204065
private theorem s_1204148 : RangeOk getRow 2051521 1201241 1204148 :=
  s_1204097.append (by norm_num) r_1204097

/-- Rows `[1201241, 1204148)` are valid. -/
theorem rangeOk_1201241_1204148 : RangeOk getRow 2051521 1201241 1204148 := s_1204148

end Noperthedron.Solution
