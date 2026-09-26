module

public import Zoo.Collect

/-!
# Provability logic zoo

Executable collecting every `⪯`, `⪱` and `≊` between two provability logics `Logic α` stated by a
constant of `Foundation`, for an arbitrary atom type `α`, and writing their transitive reduction to
a JSON file.
-/

public def main (args : List String) : IO Unit :=
  Zoo.run `FFL.ProvabilityLogic.Logic "Zoo/provability_logic.json" args
