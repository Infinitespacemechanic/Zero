import Lake
open Lake DSL

package Zero where
  -- keep it lean
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib Zero where
  -- this will build all .lean files in root
  -- We explicitly list to avoid space in filename issues
  globs := #[.submodules "Zero", .andSubmodules "Sine-pi-zeros-addresses"]
