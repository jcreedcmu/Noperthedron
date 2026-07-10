import KernelCaseAnalysis.Gen.Combine01
import KernelCaseAnalysis.Gen.Validate0128
import KernelCaseAnalysis.Gen.Validate0129
import KernelCaseAnalysis.Gen.Validate0130
import KernelCaseAnalysis.Gen.Validate0131
import KernelCaseAnalysis.Gen.Validate0132
import KernelCaseAnalysis.Gen.Validate0133
import KernelCaseAnalysis.Gen.Validate0134
import KernelCaseAnalysis.Gen.Validate0135
import KernelCaseAnalysis.Gen.Validate0136
import KernelCaseAnalysis.Gen.Validate0137
import KernelCaseAnalysis.Gen.Validate0138
import KernelCaseAnalysis.Gen.Validate0139
import KernelCaseAnalysis.Gen.Validate0140
import KernelCaseAnalysis.Gen.Validate0141
import KernelCaseAnalysis.Gen.Validate0142
import KernelCaseAnalysis.Gen.Validate0143
import KernelCaseAnalysis.Gen.Validate0144
import KernelCaseAnalysis.Gen.Validate0145
import KernelCaseAnalysis.Gen.Validate0146
import KernelCaseAnalysis.Gen.Validate0147
import KernelCaseAnalysis.Gen.Validate0148
import KernelCaseAnalysis.Gen.Validate0149
import KernelCaseAnalysis.Gen.Validate0150
import KernelCaseAnalysis.Gen.Validate0151
import KernelCaseAnalysis.Gen.Validate0152
import KernelCaseAnalysis.Gen.Validate0153
import KernelCaseAnalysis.Gen.Validate0154
import KernelCaseAnalysis.Gen.Validate0155
import KernelCaseAnalysis.Gen.Validate0156
import KernelCaseAnalysis.Gen.Validate0157
import KernelCaseAnalysis.Gen.Validate0158
import KernelCaseAnalysis.Gen.Validate0159
import KernelCaseAnalysis.Gen.Validate0160
import KernelCaseAnalysis.Gen.Validate0161
import KernelCaseAnalysis.Gen.Validate0162
import KernelCaseAnalysis.Gen.Validate0163
import KernelCaseAnalysis.Gen.Validate0164
import KernelCaseAnalysis.Gen.Validate0165
import KernelCaseAnalysis.Gen.Validate0166
import KernelCaseAnalysis.Gen.Validate0167
import KernelCaseAnalysis.Gen.Validate0168
import KernelCaseAnalysis.Gen.Validate0169
import KernelCaseAnalysis.Gen.Validate0170
import KernelCaseAnalysis.Gen.Validate0171
import KernelCaseAnalysis.Gen.Validate0172
import KernelCaseAnalysis.Gen.Validate0173
import KernelCaseAnalysis.Gen.Validate0174
import KernelCaseAnalysis.Gen.Validate0175
import KernelCaseAnalysis.Gen.Validate0176
import KernelCaseAnalysis.Gen.Validate0177
import KernelCaseAnalysis.Gen.Validate0178
import KernelCaseAnalysis.Gen.Validate0179
import KernelCaseAnalysis.Gen.Validate0180
import KernelCaseAnalysis.Gen.Validate0181
import KernelCaseAnalysis.Gen.Validate0182
import KernelCaseAnalysis.Gen.Validate0183
import KernelCaseAnalysis.Gen.Validate0184
import KernelCaseAnalysis.Gen.Validate0185
import KernelCaseAnalysis.Gen.Validate0186
import KernelCaseAnalysis.Gen.Validate0187
import KernelCaseAnalysis.Gen.Validate0188
import KernelCaseAnalysis.Gen.Validate0189
import KernelCaseAnalysis.Gen.Validate0190
import KernelCaseAnalysis.Gen.Validate0191

/-! GENERATED (scripts/gen_kernel_chunks.py): fold rows [0, 461559). -/

namespace Noperthedron.Solution

private theorem c_298431 : RangeOk getRow 2051521 0 298431 :=
  combined_295566.append (by norm_num) rangeOk_295566_298431
private theorem c_301463 : RangeOk getRow 2051521 0 301463 :=
  c_298431.append (by norm_num) rangeOk_298431_301463
private theorem c_304569 : RangeOk getRow 2051521 0 304569 :=
  c_301463.append (by norm_num) rangeOk_301463_304569
private theorem c_307429 : RangeOk getRow 2051521 0 307429 :=
  c_304569.append (by norm_num) rangeOk_304569_307429
private theorem c_310210 : RangeOk getRow 2051521 0 310210 :=
  c_307429.append (by norm_num) rangeOk_307429_310210
private theorem c_312822 : RangeOk getRow 2051521 0 312822 :=
  c_310210.append (by norm_num) rangeOk_310210_312822
private theorem c_315249 : RangeOk getRow 2051521 0 315249 :=
  c_312822.append (by norm_num) rangeOk_312822_315249
private theorem c_317800 : RangeOk getRow 2051521 0 317800 :=
  c_315249.append (by norm_num) rangeOk_315249_317800
private theorem c_320338 : RangeOk getRow 2051521 0 320338 :=
  c_317800.append (by norm_num) rangeOk_317800_320338
private theorem c_322529 : RangeOk getRow 2051521 0 322529 :=
  c_320338.append (by norm_num) rangeOk_320338_322529
private theorem c_325220 : RangeOk getRow 2051521 0 325220 :=
  c_322529.append (by norm_num) rangeOk_322529_325220
private theorem c_328001 : RangeOk getRow 2051521 0 328001 :=
  c_325220.append (by norm_num) rangeOk_325220_328001
private theorem c_330513 : RangeOk getRow 2051521 0 330513 :=
  c_328001.append (by norm_num) rangeOk_328001_330513
private theorem c_333127 : RangeOk getRow 2051521 0 333127 :=
  c_330513.append (by norm_num) rangeOk_330513_333127
private theorem c_335951 : RangeOk getRow 2051521 0 335951 :=
  c_333127.append (by norm_num) rangeOk_333127_335951
private theorem c_338621 : RangeOk getRow 2051521 0 338621 :=
  c_335951.append (by norm_num) rangeOk_335951_338621
private theorem c_341819 : RangeOk getRow 2051521 0 341819 :=
  c_338621.append (by norm_num) rangeOk_338621_341819
private theorem c_344931 : RangeOk getRow 2051521 0 344931 :=
  c_341819.append (by norm_num) rangeOk_341819_344931
private theorem c_347711 : RangeOk getRow 2051521 0 347711 :=
  c_344931.append (by norm_num) rangeOk_344931_347711
private theorem c_350417 : RangeOk getRow 2051521 0 350417 :=
  c_347711.append (by norm_num) rangeOk_347711_350417
private theorem c_352878 : RangeOk getRow 2051521 0 352878 :=
  c_350417.append (by norm_num) rangeOk_350417_352878
private theorem c_355655 : RangeOk getRow 2051521 0 355655 :=
  c_352878.append (by norm_num) rangeOk_352878_355655
private theorem c_358271 : RangeOk getRow 2051521 0 358271 :=
  c_355655.append (by norm_num) rangeOk_355655_358271
private theorem c_360897 : RangeOk getRow 2051521 0 360897 :=
  c_358271.append (by norm_num) rangeOk_358271_360897
private theorem c_363274 : RangeOk getRow 2051521 0 363274 :=
  c_360897.append (by norm_num) rangeOk_360897_363274
private theorem c_365815 : RangeOk getRow 2051521 0 365815 :=
  c_363274.append (by norm_num) rangeOk_363274_365815
private theorem c_368246 : RangeOk getRow 2051521 0 368246 :=
  c_365815.append (by norm_num) rangeOk_365815_368246
private theorem c_370694 : RangeOk getRow 2051521 0 370694 :=
  c_368246.append (by norm_num) rangeOk_368246_370694
private theorem c_373473 : RangeOk getRow 2051521 0 373473 :=
  c_370694.append (by norm_num) rangeOk_370694_373473
private theorem c_376177 : RangeOk getRow 2051521 0 376177 :=
  c_373473.append (by norm_num) rangeOk_373473_376177
private theorem c_379121 : RangeOk getRow 2051521 0 379121 :=
  c_376177.append (by norm_num) rangeOk_376177_379121
private theorem c_382312 : RangeOk getRow 2051521 0 382312 :=
  c_379121.append (by norm_num) rangeOk_379121_382312
private theorem c_385173 : RangeOk getRow 2051521 0 385173 :=
  c_382312.append (by norm_num) rangeOk_382312_385173
private theorem c_387388 : RangeOk getRow 2051521 0 387388 :=
  c_385173.append (by norm_num) rangeOk_385173_387388
private theorem c_389917 : RangeOk getRow 2051521 0 389917 :=
  c_387388.append (by norm_num) rangeOk_387388_389917
private theorem c_392371 : RangeOk getRow 2051521 0 392371 :=
  c_389917.append (by norm_num) rangeOk_389917_392371
private theorem c_394737 : RangeOk getRow 2051521 0 394737 :=
  c_392371.append (by norm_num) rangeOk_392371_394737
private theorem c_397196 : RangeOk getRow 2051521 0 397196 :=
  c_394737.append (by norm_num) rangeOk_394737_397196
private theorem c_399727 : RangeOk getRow 2051521 0 399727 :=
  c_397196.append (by norm_num) rangeOk_397196_399727
private theorem c_402035 : RangeOk getRow 2051521 0 402035 :=
  c_399727.append (by norm_num) rangeOk_399727_402035
private theorem c_404646 : RangeOk getRow 2051521 0 404646 :=
  c_402035.append (by norm_num) rangeOk_402035_404646
private theorem c_406945 : RangeOk getRow 2051521 0 406945 :=
  c_404646.append (by norm_num) rangeOk_404646_406945
private theorem c_409316 : RangeOk getRow 2051521 0 409316 :=
  c_406945.append (by norm_num) rangeOk_406945_409316
private theorem c_411765 : RangeOk getRow 2051521 0 411765 :=
  c_409316.append (by norm_num) rangeOk_409316_411765
private theorem c_414220 : RangeOk getRow 2051521 0 414220 :=
  c_411765.append (by norm_num) rangeOk_411765_414220
private theorem c_416588 : RangeOk getRow 2051521 0 416588 :=
  c_414220.append (by norm_num) rangeOk_414220_416588
private theorem c_419042 : RangeOk getRow 2051521 0 419042 :=
  c_416588.append (by norm_num) rangeOk_416588_419042
private theorem c_422556 : RangeOk getRow 2051521 0 422556 :=
  c_419042.append (by norm_num) rangeOk_419042_422556
private theorem c_425734 : RangeOk getRow 2051521 0 425734 :=
  c_422556.append (by norm_num) rangeOk_422556_425734
private theorem c_427937 : RangeOk getRow 2051521 0 427937 :=
  c_425734.append (by norm_num) rangeOk_425734_427937
private theorem c_430475 : RangeOk getRow 2051521 0 430475 :=
  c_427937.append (by norm_num) rangeOk_427937_430475
private theorem c_433006 : RangeOk getRow 2051521 0 433006 :=
  c_430475.append (by norm_num) rangeOk_430475_433006
private theorem c_435294 : RangeOk getRow 2051521 0 435294 :=
  c_433006.append (by norm_num) rangeOk_433006_435294
private theorem c_437664 : RangeOk getRow 2051521 0 437664 :=
  c_435294.append (by norm_num) rangeOk_435294_437664
private theorem c_440118 : RangeOk getRow 2051521 0 440118 :=
  c_437664.append (by norm_num) rangeOk_437664_440118
private theorem c_442381 : RangeOk getRow 2051521 0 442381 :=
  c_440118.append (by norm_num) rangeOk_440118_442381
private theorem c_444824 : RangeOk getRow 2051521 0 444824 :=
  c_442381.append (by norm_num) rangeOk_442381_444824
private theorem c_447160 : RangeOk getRow 2051521 0 447160 :=
  c_444824.append (by norm_num) rangeOk_444824_447160
private theorem c_449370 : RangeOk getRow 2051521 0 449370 :=
  c_447160.append (by norm_num) rangeOk_447160_449370
private theorem c_451826 : RangeOk getRow 2051521 0 451826 :=
  c_449370.append (by norm_num) rangeOk_449370_451826
private theorem c_454119 : RangeOk getRow 2051521 0 454119 :=
  c_451826.append (by norm_num) rangeOk_451826_454119
private theorem c_456651 : RangeOk getRow 2051521 0 456651 :=
  c_454119.append (by norm_num) rangeOk_454119_456651
private theorem c_459104 : RangeOk getRow 2051521 0 459104 :=
  c_456651.append (by norm_num) rangeOk_456651_459104
private theorem c_461559 : RangeOk getRow 2051521 0 461559 :=
  c_459104.append (by norm_num) rangeOk_459104_461559

/-- Rows `[0, 461559)` are valid. -/
theorem combined_461559 : RangeOk getRow 2051521 0 461559 := c_461559

end Noperthedron.Solution
