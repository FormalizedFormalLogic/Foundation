import Lake
open Lake DSL

package «arithmetization» {
  -- add any package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "cc28353bec92c3774a88e3b21f9a15cbcc29e24e"

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "780bbec107cba79d18ec55ac2be3907a77f27f98"

require logic from git "https://github.com/iehality/lean4-logic" @ "system"

@[default_target]
lean_lib «Arithmetization» {
  -- add any library configuration options here
}
