module

public import Zoo.Collect

/-!
# Arithmetic theory zoo

Executable collecting every `⪯`, `⪱` and `≊` between two closed `ArithmeticTheory`s stated by a
constant of `Foundation`, and writing their transitive reduction to a JSON file.
-/

public def main (args : List String) : IO Unit :=
  Zoo.run `FFL.FirstOrder.ArithmeticTheory "Zoo/arithmetic.json" args
