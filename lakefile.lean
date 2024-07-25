import Lake
open Lake DSL

package «abs-den» where
  -- add package configuration options here

lean_lib «AbsDen» where
  -- add library configuration options here

@[default_target]
lean_exe «abs-den» where
  root := `Main
