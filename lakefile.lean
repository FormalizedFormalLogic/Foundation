import Lake
open Lake DSL

package «logic» {
  -- add package configuration options here
}

lean_lib «Logic» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «logic» {
  root := `Main
}

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
