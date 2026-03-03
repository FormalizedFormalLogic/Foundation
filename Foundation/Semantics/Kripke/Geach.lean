module

public import Foundation.Semantics.Kripke.Basic

@[expose] public section

namespace LO

variable {α : Type*}

namespace KripkeFrame

structure GeachTuple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

class IsGeachConvergent (K : KripkeFrame α) (g : GeachTuple) where
  gconv : ∀ x y z : K.points, x ≺^[g.i] y → x ≺^[g.j] z → ∃ u, y ≺^[g.m] u ∧ z ≺^[g.n] u
alias gconv := IsGeachConvergent.gconv

variable {K : KripkeFrame α}

instance [hGeach : K.IsGeachConvergent ⟨0, 0, 1, 0⟩] : K.Reflexive where
  refl := by simpa using hGeach.gconv;

instance [hGeach : K.IsGeachConvergent ⟨0, 2, 1, 0⟩] : K.Transitive where
  trans x y z := by
    have := @hGeach.gconv x x z rfl;
    grind [restrictedRelI];

end KripkeFrame

end LO

end
