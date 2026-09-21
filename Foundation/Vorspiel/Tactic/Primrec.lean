module

public import Foundation.Vorspiel.Tactic.Primrec.Init

/-!
# The `primrec` tactic

Mathlib proves `Primrec f` by composing point-free combinators by hand: one reads the shape of
`f` off the term and threads `Primrec.comp`, `Primrec.fst` and `Primrec.snd` through it. That
composition is mechanical, so this module hands it to Aesop, as `definability` does for
definability.

This module carries the tactic alone. The rule set is populated in
`Foundation/Vorspiel/Computability/Primrec.lean` and wherever a `@[primrec]` lemma is stated.
-/

public meta section

open Lean.Parser.Tactic (config)

/-- Aesop's normalisation runs the default `simp` set, which is too much for the goals this
tactic is aimed at: their subterms are syntax trees of arithmetical formulas, and normalising
them dwarfs the search. The rule set carries the few simp lemmas the search needs instead. The
bounds on the search are raised from Aesop's defaults because a nest of projections reaches them
honestly. -/
def primrecConfig : Aesop.Options where
  terminal := true
  maxRuleApplicationDepth := 100
  maxRuleApplications := 4000
  useDefaultSimpSet := false
  useSimpAll := false

/-- Add a lemma to the `primrec` rule set. Its conclusion should be pointwise,
`Primrec fun a ↦ F (f a) (g a)`, with a `Primrec` hypothesis for each argument. -/
macro "primrec" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Primrec):ident]) safe apply
      (transparency := reducible))

/-- Prove `Primrec f`, `Primrec₂ f`, `PrimrecPred p` or `PrimrecRel r` by reading the shape of
the function off the goal. -/
macro "primrec" (config)? : tactic =>
  `(tactic| aesop (config := primrecConfig)
      (rule_sets := [$(Lean.mkIdent `Primrec):ident]))

/-- `primrec`, printing the proof term it found. -/
macro "primrec?" (config)? : tactic =>
  `(tactic| aesop? (config := primrecConfig)
      (rule_sets := [$(Lean.mkIdent `Primrec):ident]))

end
