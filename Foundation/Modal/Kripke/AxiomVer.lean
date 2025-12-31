import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Rel.Isolated

namespace LO.Modal

namespace Kripke

open Formula.Kripke

variable {F : Frame}

protected abbrev Frame.IsIsolated (F : Frame) := _root_.IsIsolated F.Rel

instance : blackpoint.IsIsolated where
  isolated := by tauto;

section definability

lemma validate_AxiomVer_of_isIsolated {F : Frame} [F.IsIsolated] : F ⊧ (Axioms.Ver (.atom 0)) := by
  intro V x y Rxy;
  exfalso;
  exact IsIsolated.isolated Rxy;

lemma isIsolated_of_validate_AxiomVer {F : Frame} (h : F ⊧ (Axioms.Ver (.atom 0))) : F.IsIsolated where
  isolated := by
    intro x y Rxy;
    have := h (λ _ _ => False) x y Rxy;
    simp [Formula.Kripke.Satisfies] at this;


end definability

section canonicality

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance [Entailment.HasAxiomVer 𝓢] : (canonicalFrame 𝓢).IsIsolated where
  isolated := by
    intro x y Rxy;
    have : (canonicalModel 𝓢) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr axiomVer!
    exact this x _ Rxy;

end canonicality

end Kripke

end LO.Modal
