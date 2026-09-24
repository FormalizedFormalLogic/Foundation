module

public import Foundation.Vorspiel.Tactic.Computable.Init
public import Foundation.Vorspiel.Tactic.Primrec

/-!
# The `computable` tactic

`primrec` for `Computable f`. It also runs the `Primrec` rules, reached through
`Primrec.to_comp`. The rules are in `Foundation/Vorspiel/Computability/Computable.lean`;
`@[computable]` adds more.
-/

public meta section

open Lean.Parser.Tactic (config)

/-- Adds a lemma of the form `Computable fun a ↦ F (f a) (g a)` to the `computable` rule set. -/
macro "computable" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Computable):ident]) safe apply
      (transparency := reducible))

/-- Proves `Computable f` or `Computable₂ f`. -/
macro "computable" (config)? : tactic =>
  `(tactic| aesop (config := primrecConfig)
      (rule_sets := [$(Lean.mkIdent `Computable):ident, $(Lean.mkIdent `Primrec):ident]))

macro "computable?" (config)? : tactic =>
  `(tactic| aesop? (config := primrecConfig)
      (rule_sets := [$(Lean.mkIdent `Computable):ident, $(Lean.mkIdent `Primrec):ident]))

end
