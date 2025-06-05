import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Supplemental


section

variable {α : Type u} (rel : α → α → Prop)

def StrictlyTransitive := ∀ x y z, x ≠ y → y ≠ z → rel x y → rel y z → rel x z
def WeaklyStrictlyTransitive := ∀ x y z, x ≠ y → y ≠ z → z ≠ x → rel x y → rel y z → rel x z

end


namespace LO.Modal.Axioms

variable {F : Type*} [BasicModalLogicalConnective F]
variable (p q : F)

protected abbrev ST := □p ➝ (q ➝ □(q ⋎ (p ➝ □p)))

protected abbrev WST := □p ➝ (p ➝ q ➝ □(q ⋎ (p ➝ □p)))

end LO.Modal.Axioms



namespace LO.Modal

namespace Kripke

open Formula (atom)
open Formula.Kripke

section definability

variable {F : Kripke.Frame}

lemma validate_AxiomST_of_StrictlyTransitive : StrictlyTransitive F → F ⊧ (Axioms.ST (.atom 0) (.atom 1)) := by
  rintro hST V x hx₁ hx₂ y Rxy;
  apply Satisfies.or_def.mpr;
  apply or_iff_not_imp_left.mpr;
  intro hy₁ hy₂ z Ryz;
  by_contra hz;
  apply hz $ @hx₁ z $ @hST x y z ?_ ?_ Rxy Ryz;
  . by_contra hC; subst hC;
    contradiction;
  . by_contra hC; subst hC;
    contradiction;

lemma strictlyTransitive_of_validate_axiomST : F ⊧ (Axioms.ST (.atom 0) (.atom 1)) → StrictlyTransitive F := by
  dsimp [StrictlyTransitive];
  contrapose!;
  rintro ⟨x, y, z, nexy, neyz, Rxy, Ryz, Rxz⟩;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (λ w a => match a with | 0 => x ≺ w | 1 => w = x | _ => True), x;
  suffices ∃ y, x ≺ y ∧ ¬y = x ∧ x ≺ y ∧ ∃ z, y ≺ z ∧ ¬x ≺ z by
    simpa [Satisfies];
  use y;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . assumption;
  . tauto;
  . tauto;
  . use z;

theorem iff_validate_axiomST_of_StrictlyTransitive : StrictlyTransitive F ↔ F ⊧ (Axioms.ST (.atom 0) (.atom 1)) := by
  constructor;
  . apply validate_AxiomST_of_StrictlyTransitive;
  . apply strictlyTransitive_of_validate_axiomST;


lemma validate_AxiomWST_of_WeaklyStrictlyTransitive : WeaklyStrictlyTransitive F → F ⊧ (Axioms.WST (.atom 0) (.atom 1)) := by
  rintro hWST V x hx₁ hx₂ hx₃ y Rxy;
  apply Satisfies.or_def.mpr;
  apply or_iff_not_imp_left.mpr;
  intro hy₁ hy₂ z Ryz;
  by_contra hz;
  apply hz;
  apply hx₁;
  apply hWST x y z;
  . by_contra hC; subst hC;
    contradiction;
  . by_contra hC; subst hC;
    have := hx₁ y Rxy;
    contradiction;
  . by_contra hC; subst hC;
    have := hx₁ y Rxy;
    contradiction;
  . assumption;
  . assumption;

lemma weaklyStrictlyTransitive_of_validate_axiomST : F ⊧ (Axioms.WST (.atom 0) (.atom 1)) → WeaklyStrictlyTransitive F := by
  dsimp [WeaklyStrictlyTransitive];
  contrapose!;
  rintro ⟨x, y, z, nexy, neyz, nezx, Rxy, Ryz, Rxz⟩;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (λ w a => match a with | 0 => w = x ∨ x ≺ w | 1 => w = x | _ => True), x;
  suffices (∀ y, x ≺ y → y = x ∨ x ≺ y) ∧ ∃ y, x ≺ y ∧ ¬y = x ∧ (y = x ∨ x ≺ y) ∧ ∃ z, y ≺ z ∧ ¬z = x ∧ ¬x ≺ z by
    simpa [Satisfies];
  constructor;
  . tauto;
  . use y;
    refine ⟨?_, ?_, ?_, ?_⟩;
    . assumption;
    . tauto;
    . tauto;
    . use z;

theorem iff_validate_axiomWST_of_WeaklyStrictlyTransitive : WeaklyStrictlyTransitive F ↔ F ⊧ (Axioms.WST (.atom 0) (.atom 1)) := by
  constructor;
  . apply validate_AxiomWST_of_WeaklyStrictlyTransitive;
  . apply weaklyStrictlyTransitive_of_validate_axiomST;

end definability


end Kripke

end LO.Modal
