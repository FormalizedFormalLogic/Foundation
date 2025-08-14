import Foundation.ProvabilityLogic.Interpretation
import Foundation.FirstOrder.Internal.FixedPoint

/-!
Provability logic of first order theory
-/

namespace LO.FirstOrder

variable (T : ArithmeticTheory) [T.Δ₁]

/-- Provability logic of arithmetic theory-/
def ArithmeticTheory.PL : Modal.Logic ℕ := {A | ∀ f : T.PLRealization, T ⊢!. f A}

variable {T}

namespace ArithmeticTheory.ProvabilityLogic

lemma provable_iff :
    T.PL ⊢! A ↔ ∀ f : T.PLRealization, T ⊢!. f A := by simp [ArithmeticTheory.PL]

end ArithmeticTheory.ProvabilityLogic

end LO.FirstOrder
