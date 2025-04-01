import Foundation.Incompleteness.Arith.DC
import Foundation.Incompleteness.DC.Basic
import Foundation.Modal.Logic.WellKnown

namespace LO

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition
open LO.Modal
open LO.Modal.Hilbert

variable {α : Type u}
variable [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T U : Theory L}


namespace ProvabilityLogic

/-- Mapping modal prop vars to first-order sentence -/
def Realization (L) := ℕ → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def Realization.interpret
  {T U : FirstOrder.Theory L}
  (f : Realization L) (𝔅 : ProvabilityPredicate T U) : Formula ℕ → FirstOrder.Sentence L
  | .atom a => f a
  | □φ => 𝔅 (f.interpret 𝔅 φ)
  | ⊥ => ⊥
  | φ ➝ ψ => (f.interpret 𝔅 φ) ➝ (f.interpret 𝔅 ψ)


variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class ArithmeticalSound (Λ : Modal.Logic) (𝔅 : ProvabilityPredicate T U) where
  sound : ∀ {φ}, (φ ∈ Λ) → (∀ {f : Realization L}, U ⊢!. (f.interpret 𝔅 φ))

class ArithmeticalComplete (Λ : Modal.Logic) (𝔅 : ProvabilityPredicate T U) where
  complete : ∀ {φ}, (∀ {f : Realization L}, U ⊢!. (f.interpret 𝔅 φ)) → (φ ∈ Λ)

end LO.ProvabilityLogic
