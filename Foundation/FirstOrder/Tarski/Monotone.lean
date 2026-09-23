module

public import Foundation.FirstOrder.Tarski.Basic

/-!
# Structures with monotone function symbols

Term monotonicity follows by structural induction from monotonicity of the interpretations
of function symbols. This elementary closure lemma is specific to the semantic API.
-/

@[expose] public section
namespace FFL.FirstOrder

namespace Tarski.Structure

class Monotone (L : Language) (M : Type*) [LE M] [Tarski.Structure L M] where
  monotone : ∀ {k} (f : L.Func k) (v₁ v₂ : Fin k → M), (∀ i, v₁ i ≤ v₂ i) → Tarski.Structure.func f v₁ ≤ Tarski.Structure.func f v₂

namespace Monotone

variable {L : Language} {M : Type*} [LE M] [Tarski.Structure L M] [Monotone L M]

lemma term_monotone (t : Semiterm L ξ n) {fv₁ fv₂ : Fin n → M} {bv₁ bv₂ : ξ → M}
    (he : ∀ i, fv₁ i ≤ fv₂ i) (hε : ∀ i, bv₁ i ≤ bv₂ i) :
    t.val fv₁ bv₁ ≤ t.val fv₂ bv₂ := by
  induction t <;> simp [*, Semiterm.val_func, Monotone.monotone]

end Monotone

end Tarski.Structure

end FirstOrder
