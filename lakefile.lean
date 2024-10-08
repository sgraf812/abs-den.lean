import Lake
open System Lake DSL

package «abs-den» where
  -- add package configuration options here
  require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
  require mathlib from git "https://github.com/leanprover-community/mathlib4"

target igdtt.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "igdtt.o"
  let srcJob ← inputTextFile <| pkg.dir / "igdtt" / "c" / "igdtt.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "leanc" getLeanTrace

extern_lib igdttffi pkg := do
  let igdttO ← igdtt.o.fetch
  let name := nameToStaticLib "igdttffi"
  buildStaticLib (pkg.nativeLibDir / name) #[igdttO]

lean_lib IGDTT where
  srcDir := "igdtt"
--  precompileModules := true

lean_lib AbsDen where
  srcDir := "lib"
--  precompileModules := true

@[default_target]
lean_exe «abs-den» where
  srcDir := "app"
  root := `Main
  supportInterpreter := true
