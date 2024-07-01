import Lake
open Lake DSL

package «logic» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Logic» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "f0957a7575317490107578ebaee9efaf8e62a4ab"

meta if get_config? env = some "ci" then
require importGraph from git "https://github.com/leanprover-community/import-graph" @ "main"

meta if get_config? env = some "ci" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
