import Lake
open Lake DSL

package «arithmetization» {
  -- add any package configuration options here
}

@[default_target]
lean_lib «Arithmetization» {
  -- add any library configuration options here
}

require logic from git "https://github.com/FormalizedFormalLogic/Foundation" @ "master"

require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.39"

meta if get_config? env = some "ci" then
require importGraph from git "https://github.com/leanprover-community/import-graph" @ "main"

meta if get_config? env = some "ci" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
