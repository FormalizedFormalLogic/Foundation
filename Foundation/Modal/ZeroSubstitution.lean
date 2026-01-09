module
import Foundation.Modal.Letterless

namespace LO.Modal

def ZeroSubstitution (α) := {s : Substitution α // ∀ {a : α}, ((.atom a)⟦s⟧).Letterless }

lemma Formula.Letterless_zeroSubst {φ : Formula α} {s : ZeroSubstitution α} : (φ⟦s.1⟧).Letterless := by
  induction φ <;> simp [Formula.Letterless, *];
  case hatom => exact s.2;

lemma Formula.toModalFormula.Letterless {φ : Propositional.Formula α} (h : φ.Letterless) : φ.toModalFormula.Letterless := by
  induction φ using Propositional.Formula.rec' <;> simp_all [Propositional.Formula.Letterless, Formula.Letterless];

instance : Coe (Propositional.ZeroSubstitution α) (Modal.ZeroSubstitution α) := ⟨λ ⟨s, p⟩ => ⟨λ φ => s φ, λ {_} => Formula.toModalFormula.Letterless p⟩⟩

end LO.Modal
