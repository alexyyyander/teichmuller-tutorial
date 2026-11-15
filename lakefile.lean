import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "last_bump_for_v4.31.0"

package teichmuller_program where
  srcDir := "lean"

lean_lib Teichmuller

@[default_target]
lean_exe teichmuller_demo where
  root := `Main
