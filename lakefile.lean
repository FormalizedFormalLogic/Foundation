import Lake
open Lake DSL

package foundation {
  -- add package configuration options here
}

@[default_target]
lean_lib Foundation where
  leanOptions := #[
    ⟨`linter.flexible, true⟩
  ]

require "leanprover-community" / "mathlib" @ git "master"
