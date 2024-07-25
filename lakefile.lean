import Lake
open Lake DSL

package «abs-den» where
  -- add package configuration options here
  require batteries from git "https://github.com/leanprover-community/batteries" @ "main"
  require mathlib from git "https://github.com/leanprover-community/mathlib4"
lean_lib «AbsDen» where
  -- add library configuration options here

@[default_target]
lean_exe «abs-den» where
  root := `Main
