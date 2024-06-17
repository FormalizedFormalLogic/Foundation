import Lake
open Lake DSL

package «logic» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Logic» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
require importGraph from git "https://github.com/leanprover-community/import-graph" @ "7983e959f8f4a79313215720de3ef1eca2d6d474"

meta if get_config? env = some "ci" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
