import Lake
open Lake DSL

package «arithmetization» {
  -- add any package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "678f4912899df76cc45934a56bdf929ffe3cac50"

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require logic from git "https://github.com/iehality/lean4-logic" @ "master"

@[default_target]
lean_lib «Arithmetization» {
  -- add any library configuration options here
}
