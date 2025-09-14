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
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

target libleanffi_seek pkg : Dynlib := do
  let libName := "leanffi"
  let ffiO ← ffi_seek.o.fetch
  let weakArgs := #["-L", (← getLeanLibDir).toString]
  let leanArgs ← getLeanLinkSharedFlags
  buildSharedLib libName (pkg.sharedLibDir / nameToSharedLib libName)
    #[ffiO] #[] weakArgs leanArgs "cc" getLeanTrace

-- Parquet

lean_lib Parquet where
  moreLinkLibs := #[libleanffi_seek]

lean_exe ParquetTest {
  root := `ParquetTest
  moreLeancArgs := #[]
  moreLinkArgs := #[]
}
