import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Kripke.Completeness

namespace LO.Modal

open Formula.Kripke

namespace Kripke

abbrev FrameClass.isolated : FrameClass := { F | Isolated F }

@[simp]
lemma FrameClass.isolated.nonempty : FrameClass.isolated.Nonempty := by
  use ⟨Unit, λ _ _ => False⟩;
  tauto;

instance FrameClass.isolated.definability : FrameClass.isolated.DefinedByFormula (Axioms.Ver (.atom 0)) := ⟨by
  intro F;
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, ValidOnFrame.models_iff, forall_eq];
  constructor;
  . intro h V x y Rxy;
    have := h Rxy;
    contradiction;
  . intro h x y Rxy;
    have := h (λ _ _ => False) x y Rxy;
    simp [Formula.Kripke.Satisfies] at this;
⟩

end Kripke

namespace Kripke


open Entailment

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢]

instance [Entailment.Ver 𝓢] : Canonical 𝓢 FrameClass.isolated := ⟨by
  intro x y Rxy;
  have : (canonicalModel 𝓢) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr axiomVer!
  exact this x _ Rxy;
⟩

end Kripke

end LO.Modal
