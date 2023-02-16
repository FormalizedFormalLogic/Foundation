import Logic.Predicate.FirstOrder.Language
import Logic.Vorspiel.Zermelo

open FirstOrder

def φ : SyntacticFormula Language.equal :=
  ∀' ∀' ∀' (
    SubFormula.rel! Language.equal 2 Language.EqRel.equal (#0 :> #1 :> Fin.nil) ⟶
    SubFormula.rel! Language.equal 2 Language.EqRel.equal (#1 :> #2 :> Fin.nil) ⟶
    SubFormula.rel! Language.equal 2 Language.EqRel.equal (#0 :> #2 :> Fin.nil))

#eval toString φ