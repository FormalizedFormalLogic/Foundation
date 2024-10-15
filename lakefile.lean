import Lake
open Lake DSL

require arithmetization from git "https://github.com/FormalizedFormalLogic/Arithmetization" @ "master"

package incompleteness where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib Incompleteness where
  -- add any library configuration options here
