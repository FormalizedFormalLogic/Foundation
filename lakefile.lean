import Lake
open Lake DSL

package «logic» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Logic» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "b5eba595428809e96f3ed113bc7ba776c5f801ac"

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "c7f4ac84b973b6efd8f24ba2b006cad1b32c9c53"
