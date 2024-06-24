import Lake
open Lake DSL

package «arithmetization» {
  -- add any package configuration options here
}

@[default_target]
lean_lib «Arithmetization» {
  -- add any library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "739a018e1c14b34b2efccad6e4c0b1cdbf9fa671"

require logic from git "https://github.com/iehality/lean4-logic" @ "master"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
