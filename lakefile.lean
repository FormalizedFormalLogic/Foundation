import Lake
open Lake DSL

package «arithmetization» {
  -- add any package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

require logic from git "https://github.com/iehality/lean4-logic"

@[default_target]
lean_lib «Arithmetization» {
  -- add any library configuration options here
}
