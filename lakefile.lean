import Lake
open Lake DSL

package «logic» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Logic» {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "ab9dec5b351bc7e92f30b47031edf13458bc7a1d"

require importGraph from git "https://github.com/leanprover-community/import-graph" @ "68b518c9b352fbee16e6d632adcb7a6d0760e2b7"
