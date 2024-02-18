import Lake
open Lake DSL

package «Le» where
  -- add package configuration options here

lean_lib «Le» where
  -- add library configuration options here

@[default_target]
lean_exe «le» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
