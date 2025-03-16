import Foundation.Vorspiel.Relation.Supplemental
import Foundation.Modal.Kripke.Completeness

namespace LO.Modal

open Formula.Kripke

namespace Kripke

instance : IsIsolated _ blackpoint.Rel := ⟨by tauto⟩

lemma validate_AxiomVer_of_isolated {F : Frame} [IsIsolated _ F] : F ⊧ (Axioms.Ver (.atom 0)) := by
  intro V x y Rxy;
  exfalso;
  exact IsIsolated.isolated Rxy;

lemma isolated_of_validate_AxiomVer {F : Frame} (h : F ⊧ (Axioms.Ver (.atom 0))) : Isolated F := by
  intro x y Rxy;
  have := h (λ _ _ => False) x y Rxy;
  simp [Formula.Kripke.Satisfies] at this;

section canonicality

open Entailment

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance [Entailment.HasAxiomVer 𝓢] : IsIsolated _ (canonicalFrame 𝓢).Rel := ⟨by
  intro x y Rxy;
  have : (canonicalModel 𝓢) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr axiomVer!
  exact this x _ Rxy;
⟩

end canonicality

end Kripke

end LO.Modal
