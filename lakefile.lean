import Lake
open Lake DSL

package «arithmetization» {
  -- add any package configuration options here
}

@[default_target]
lean_lib «Arithmetization» {
  -- add any library configuration options here
}

require logic from git "https://github.com/iehality/lean4-logic" @ "master"

require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.39"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
