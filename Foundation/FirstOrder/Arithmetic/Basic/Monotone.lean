module

public import Foundation.FirstOrder.Arithmetic.Basic.Misc

@[expose] public section
namespace LO.FirstOrder

namespace Structure

class Monotone (L : Language) (M : Type*) [LE M] [Structure L M] where
  monotone : ∀ {k} (f : L.Func k) (v₁ v₂ : Fin k → M), (∀ i, v₁ i ≤ v₂ i) → Structure.func f v₁ ≤ Structure.func f v₂

namespace Monotone

variable {L : Language} {M : Type*} [LE M] [Structure L M] [Monotone L M]

lemma term_monotone (t : Semiterm L ξ n) {fv₁ fv₂ : Fin n → M} {bv₁ bv₂ : ξ → M}
    (he : ∀ i, fv₁ i ≤ fv₂ i) (hε : ∀ i, bv₁ i ≤ bv₂ i) :
    t.val fv₁ bv₁ ≤ t.val fv₂ bv₂ := by
  induction t <;> simp [*, Semiterm.val_func, Monotone.monotone]

end Monotone

end Structure

end FirstOrder
