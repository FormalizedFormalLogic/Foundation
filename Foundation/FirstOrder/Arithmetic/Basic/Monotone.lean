import Foundation.FirstOrder.Arithmetic.Basic.ORingStruc

namespace LO.FirstOrder

namespace Structure

class Monotone (L : Language) (M : Type*) [LE M] [Structure L M] where
  monotone : ∀ {k} (f : L.Func k) (v₁ v₂ : Fin k → M), (∀ i, v₁ i ≤ v₂ i) → Structure.func f v₁ ≤ Structure.func f v₂

namespace Monotone

variable {L : Language} {M : Type*} [LE M] [Structure L M] [Monotone L M]

lemma term_monotone (t : Semiterm L ξ n) {e₁ e₂ : Fin n → M} {ε₁ ε₂ : ξ → M}
    (he : ∀ i, e₁ i ≤ e₂ i) (hε : ∀ i, ε₁ i ≤ ε₂ i) :
    t.valm M e₁ ε₁ ≤ t.valm M e₂ ε₂ := by
  induction t <;> simp [*, Semiterm.val_func, Monotone.monotone]

end Monotone

end Structure

end FirstOrder
