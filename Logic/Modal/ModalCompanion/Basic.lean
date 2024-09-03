import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Modal.Deduction

namespace LO.Modal

open LO.Propositional

/-- Gödel Translation -/
def GoedelTranslation : Superintuitionistic.Formula α → Formula α
  | .atom a  => □(Formula.atom a)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ~p => □(~(GoedelTranslation p))
  | p ⋏ q => (GoedelTranslation p) ⋏ (GoedelTranslation q)
  | p ⋎ q => (GoedelTranslation p) ⋎ (GoedelTranslation q)
  | p ⟶ q => □((GoedelTranslation p) ⟶ (GoedelTranslation q))
postfix:90 "ᵍ" => GoedelTranslation

class ModalCompanion (iΛ : Superintuitionistic.DeductionParameter α) (mΛ : Modal.DeductionParameter α) where
  companion : ∀ {p : Superintuitionistic.Formula α}, iΛ ⊢! p ↔ mΛ ⊢! pᵍ

end LO.Modal
