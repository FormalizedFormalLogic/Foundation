module

public import Foundation.InterpretabilityLogic.Formula.Basic
public import Foundation.Modal.Formula.Basic

@[expose] public section

namespace LO.InterpretabilityLogic.Formula

variable {α : Type*}

/-- Formula has no `▷`. -/
@[grind]
def RhdFree : Formula α → Prop
  | atom _     => True
  | falsum     => True
  | imp φ ψ    => RhdFree φ ∧ RhdFree ψ
  | box φ      => RhdFree φ
  | rhd _ _    => False

def toModalFormula (φ : Formula α) (_ : φ.RhdFree := by grind) : Modal.Formula α :=
  match φ with
  | atom a  => .atom a
  | ⊥       => ⊥
  | imp φ ψ => (φ.toModalFormula) ➝ (ψ.toModalFormula)
  | box φ   => □(φ.toModalFormula)

end LO.InterpretabilityLogic.Formula
end
