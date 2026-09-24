module

public import Foundation.Vorspiel.Tactic.Primrec.Init

/-!
# The `primrec` tactic

Proves `Primrec f` by reading the shape of `f` off the goal, via Aesop. The rules are in
`Foundation/Vorspiel/Computability/Primrec.lean`; `@[primrec]` adds more.
-/

public meta section

open Lean.Parser.Tactic (config)

-- The default simp set is too costly on goals built from arithmetical syntax trees.
def primrecConfig : Aesop.Options where
  terminal := true
  maxRuleApplicationDepth := 100
  maxRuleApplications := 4000
  useDefaultSimpSet := false
  useSimpAll := false

/-- Adds a lemma of the form `Primrec fun a ↦ F (f a) (g a)` to the `primrec` rule set. -/
macro "primrec" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Primrec):ident]) safe apply
      (transparency := reducible))

/-- Proves `Primrec f`, `Primrec₂ f`, `PrimrecPred p` or `PrimrecRel r`. -/
macro "primrec" (config)? : tactic =>
  `(tactic| aesop (config := primrecConfig)
      (rule_sets := [$(Lean.mkIdent `Primrec):ident]))

macro "primrec?" (config)? : tactic =>
  `(tactic| aesop? (config := primrecConfig)
      (rule_sets := [$(Lean.mkIdent `Primrec):ident]))

end
