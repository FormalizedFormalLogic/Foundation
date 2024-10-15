import Lake
open Lake DSL

package arithmetization {
  -- add any package configuration options here
}

@[default_target]
lean_lib Arithmetization {
  -- add any library configuration options here
}

require foundation from git "https://github.com/FormalizedFormalLogic/Foundation" @ "rename"
