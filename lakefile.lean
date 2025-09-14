import Lake
open Lake DSL

package NegativeRupert where
  version := v!"0.1.0"

require rupert from git
  "https://github.com/dwrensha/Rupert.lean" @ "lean-v4.22.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.22.0"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib NegativeRupert

lean_lib Parquet

lean_exe ParquetTest {
  root := `ParquetTest
  moreLeancArgs := #[]
  moreLinkArgs := #[]
}
