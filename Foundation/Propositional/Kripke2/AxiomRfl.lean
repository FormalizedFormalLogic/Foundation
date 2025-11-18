import Foundation.Propositional.Kripke2.Basic
import Foundation.Vorspiel.HRel.Convergent
import Foundation.Vorspiel.HRel.Euclidean
import Foundation.Vorspiel.HRel.Coreflexive

namespace LO.Propositional

namespace Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

/-- Axioms of reflexivity -/
protected abbrev Rfl := (φ ⋏ (φ ➝ ψ)) ➝ ψ

end Axioms


open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {F : Kripke2.Frame}


namespace Frame

protected abbrev IsReflexive (F : Kripke2.Frame) := _root_.IsRefl _ F.Rel
@[simp, grind .] lemma refl [F.IsReflexive] : ∀ x : F, x ≺ x := IsRefl.refl

end Frame


@[simp high, grind .]
lemma valid_axiomRfl_of_isReflexive [F.IsReflexive] : F ⊧ Axioms.Rfl φ ψ := by
  intro V x y Rxy h;
  have ⟨h₁, h₂⟩ := Satisfies.def_and.mp h;
  apply h₂;
  . simp;
  . assumption;

lemma isReflexive_of_valid_axiomRfl (h : F ⊧ Axioms.Rfl #0 #1) : F.IsReflexive := by
  constructor;
  intro x;
  have := @h (λ w a => match a with | 0 => w = x | 1 => x ≺ w | _ => False) F.root x F.rooted $ by
    apply Satisfies.def_and.mpr;
    constructor;
    . tauto;
    . rintro y Rxy;
      tauto;
  exact this;

end Kripke2

end LO.Propositional
