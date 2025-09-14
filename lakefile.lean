import Lake
open System Lake DSL

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

-- FFI library

input_file ffi_seek.c where
  path := "ffi" / "ffi_seek.c"
  text := true

target ffi_seek.o pkg : FilePath := do
  let srcJob ← ffi_seek.c.fetch
  let oFile := pkg.buildDir / "ffi" / "ffi_seek.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc"

target libleanffi_seek pkg : FilePath := do
  let ffiO ← ffi_seek.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- Parquet

lean_lib Parquet where
  moreLinkObjs := #[libleanffi_seek]

lean_exe ParquetTest {
  root := `ParquetTest
  moreLeancArgs := #[]
  moreLinkArgs := #[]
}
