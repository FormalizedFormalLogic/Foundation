module

public import Foundation.Vorspiel.Tactic.Computable.Init
public import Foundation.Vorspiel.Tactic.Primrec

/-!
# The `computable` tactic

`computable` is `primrec` one level up: it reads the shape of the function off a `Computable`
goal. It runs over the `Primrec` rule set as well, so a primitive recursive subterm — which is
most of them — is discharged by the rules `primrec` already knows, through the bridge
`Primrec.to_comp`. The `Computable` rule set only has to cover the shapes in which a computable
but not primitive recursive argument can sit.

This module carries the tactic alone; the rule set is populated in
`Foundation/Vorspiel/Computability/Computable.lean` and wherever a `@[computable]` lemma is
stated.
-/

public meta section

open Lean.Parser.Tactic (config)

/-- The `primrec` configuration, for the same reasons: the default `simp` set dwarfs the search
on the goals this tactic is aimed at, and a nest of projections reaches Aesop's default bounds
honestly. -/
def computableConfig : Aesop.Options := primrecConfig

/-- Add a lemma to the `computable` rule set. Its conclusion should be pointwise,
`Computable fun a ↦ F (f a) (g a)`, with a `Computable` hypothesis for each argument. -/
macro "computable" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Computable):ident]) safe apply
      (transparency := reducible))

/-- Prove `Computable f` or `Computable₂ f` by reading the shape of the function off the goal.
`Primrec` goals are proved too, by the `primrec` rules. -/
macro "computable" (config)? : tactic =>
  `(tactic| aesop (config := computableConfig)
      (rule_sets := [$(Lean.mkIdent `Computable):ident, $(Lean.mkIdent `Primrec):ident]))

/-- `computable`, printing the proof term it found. -/
macro "computable?" (config)? : tactic =>
  `(tactic| aesop? (config := computableConfig)
      (rule_sets := [$(Lean.mkIdent `Computable):ident, $(Lean.mkIdent `Primrec):ident]))

end
