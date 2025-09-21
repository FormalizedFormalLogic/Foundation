import Foundation.Modal.Letterless

namespace LO.Modal

def ZeroSubstitution (α) := {s : Substitution α // ∀ {a : α}, ((.atom a)⟦s⟧).letterless }

lemma Formula.letterless_zeroSubst {φ : Formula α} {s : ZeroSubstitution α} : (φ⟦s.1⟧).letterless := by
  induction φ <;> simp [Formula.letterless, *];
  case hatom => exact s.2;

lemma Formula.toModalFormula.letterless {φ : Propositional.Formula α} (h : φ.letterless) : φ.toModalFormula.letterless := by
  induction φ using Propositional.Formula.rec' <;> simp_all [Propositional.Formula.letterless, Formula.letterless];

instance : Coe (Propositional.ZeroSubstitution α) (Modal.ZeroSubstitution α) := ⟨λ ⟨s, p⟩ => ⟨λ φ => s φ, λ {_} => Formula.toModalFormula.letterless p⟩⟩

end LO.Modal
