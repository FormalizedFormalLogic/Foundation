import Foundation.ProvabilityLogic.Interpretation
import Foundation.FirstOrder.Internal.FixedPoint

/-!
Provability logic of first order theory
-/

namespace LO.FirstOrder

variable (T : ArithmeticTheory) [T.Δ₁]

/-- Provability logic of arithmetic theory-/
def ArithmeticTheory.ProvabilityLogic : Modal.Logic ℕ := {A | ∀ f : T.PLRealization, T ⊢!. f A}

variable {T}

namespace ArithmeticTheory.ProvabilityLogic

lemma provable_iff :
    T.ProvabilityLogic ⊢! A ↔ ∀ f : T.PLRealization, T ⊢!. f A := by
  simp [ArithmeticTheory.ProvabilityLogic]

end ArithmeticTheory.ProvabilityLogic

end LO.FirstOrder
