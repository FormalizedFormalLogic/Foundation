import Foundation.ProvabilityLogic.Realization
import Foundation.FirstOrder.Internal.FixedPoint

/-!
# Provability logic of arithmetic theory
-/

namespace LO.FirstOrder

variable (T U : ArithmeticTheory) [T.Δ₁]

/-- Provability logic of arithmetic theory-/
def ArithmeticTheory.ProvabilityLogic : Modal.Logic ℕ := {A | ∀ f : T.StandardRealization, U ⊢! f A}

variable {T U}

namespace ArithmeticTheory.ProvabilityLogic

lemma provable_iff :
    ProvabilityLogic T U ⊢! A ↔ ∀ f : T.StandardRealization, U ⊢! f A := by
  simp [ArithmeticTheory.ProvabilityLogic]

end ArithmeticTheory.ProvabilityLogic

end LO.FirstOrder
