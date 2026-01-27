module

public import Foundation.InterpretabilityLogic.Formula.Substitution
public import Foundation.Modal.Formula.Basic

@[expose] public section

namespace LO.Modal

variable {α : Type*}

def Formula.toInterpretabilityLogicFormula : Modal.Formula α → InterpretabilityLogic.Formula α
  | .atom a  => .atom a
  | ⊥       => ⊥
  | φ ➝ ψ => (φ.toInterpretabilityLogicFormula) ➝ (ψ.toInterpretabilityLogicFormula)
  | □φ   => □(φ.toInterpretabilityLogicFormula)
instance : Coe (Modal.Formula α) (InterpretabilityLogic.Formula α) := ⟨Formula.toInterpretabilityLogicFormula⟩

def Substitution.toInterpretabilityLogicSubstitution (s : Modal.Substitution α) : InterpretabilityLogic.Substitution α := λ a => (s a)
instance : Coe (Modal.Substitution α) (InterpretabilityLogic.Substitution α) := ⟨Substitution.toInterpretabilityLogicSubstitution⟩

end LO.Modal
end
