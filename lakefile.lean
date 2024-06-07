import Lake
open Lake DSL

package «logic» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Logic» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

meta if get_config? env = some "docs" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
