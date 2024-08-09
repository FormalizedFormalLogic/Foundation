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
require importGraph from git "https://github.com/leanprover-community/import-graph" @ "68b518c9b352fbee16e6d632adcb7a6d0760e2b7"

meta if get_config? env = some "ci" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "b941c425f6f0f1dc45fe13b850ffa7db1bb20d04"
