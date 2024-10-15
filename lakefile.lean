import Lake
open Lake DSL

require foundation from git "https://github.com/FormalizedFormalLogic/Foundation" @ "master"

package arithmetization {
  -- add any package configuration options here
}

@[default_target]
lean_lib Arithmetization {
  -- add any library configuration options here
}
