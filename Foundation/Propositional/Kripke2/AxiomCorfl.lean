import Foundation.Propositional.Kripke2.Basic
import Foundation.Vorspiel.HRel.Convergent
import Foundation.Vorspiel.HRel.Euclidean
import Foundation.Vorspiel.HRel.Coreflexive
import Foundation.Vorspiel.HRel.Isolated

namespace LO.Propositional


open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {F : Kripke2.Frame} {φ ψ}


namespace Frame

protected abbrev IsCoreflexive (F : Kripke2.Frame) := _root_.IsCoreflexive F.Rel
@[simp, grind =>] lemma corefl [F.IsCoreflexive] : ∀ {x y : F}, x ≺ y → x = y := by apply IsCoreflexive.corefl

end Frame


@[simp high, grind .]
lemma valid_axiomCorfl_of_IsCoreflexive [F.IsCoreflexive] : F ⊧ Axioms.Corfl φ ψ := by
  intro V x;
  dsimp [Satisfies];
  grind;

lemma isCoreflexive_of_valid_axiomCorfl (h : F ⊧ Axioms.Corfl #0 #1) : F.IsCoreflexive := by
  constructor;
  intro x y Rxy;
  rcases @h (λ w a => match a with | 0 => w = x | 1 => w = y | _ => False) F.root with ⟨h₁, (h₂ | h₂)⟩;
  . exact @h₁ x F.rooted rfl y Rxy rfl |>.symm;
  . have := @h₂ x F.rooted rfl;
    tauto;

end Kripke2

end LO.Propositional
