import Lake
open Lake DSL

package «blanc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Blanc» where
lean_exe «Blanx» where
  root := `Blanc
  moreLinkArgs := #["-lsecp256k1"]


-- target ffi.o pkg : System.FilePath := do
--   let oFile := pkg.buildDir / "c" / "ffi.o"
--   let srcJob ← inputTextFile <| pkg.dir / "c" / "ffi.c"
--   let weakArgs := #["-I", (← getLeanIncludeDir).toString]
--   buildO oFile srcJob weakArgs #["-fPIC"] "gcc" getLeanTrace
--
-- extern_lib libleanffi pkg := do
--   let ffiO ← ffi.o.fetch
--   let name := nameToStaticLib "leanffi"
--   buildStaticLib (pkg.nativeLibDir / name) #[ffiO]
--
-- First, create a target for aux.o

target keccak.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "keccak.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "keccak.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "gcc" getLeanTrace

-- Then modify ffi.o to include secp256k1 in compilation flags
target recover.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "recover.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "recover.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString
    -- "-lsecp256k1"  -- Add secp256k1 library
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] "gcc" getLeanTrace

-- Modify extern_lib to include both object files
extern_lib libleanffi pkg := do
  let ffiO ← recover.o.fetch
  let auxO ← keccak.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO, auxO]  -- Build with both object files

script rebuild_c := do
  let _ ← IO.Process.output { cmd := "lake" }
  let buildDir := System.FilePath.mk ".lake/build"
  let nativeLibDir := System.FilePath.mk ".lake/build/lib"
  IO.FS.removeFile <| buildDir / "c" / "recover.o"
  IO.FS.removeFile <| buildDir / "c" / "keccak.o"
  IO.FS.removeFile <| nativeLibDir / (nameToStaticLib "leanffi")
  let _ ← IO.Process.output { cmd := "lake", args := #["build"] }
  return 0
