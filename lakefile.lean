import Lake
open Lake DSL

package foundation {
  -- add package configuration options here
}

@[default_target]
lean_lib Foundation {
  -- add library configuration options here
}

require "leanprover-community" / "mathlib" @ git "master"

require "leanprover-community" / "importGraph" @ git "main"
