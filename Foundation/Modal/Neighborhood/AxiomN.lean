import Foundation.Modal.Neighborhood.Basic
import Foundation.Modal.Neighborhood.Completeness
import Foundation.Modal.Entailment.EN

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

class Frame.ContainsUnit (F : Frame) : Prop where
  contains_unit : F.box Set.univ = Set.univ

lemma Frame.contains_unit [Frame.ContainsUnit F] : F.box Set.univ = Set.univ := Frame.ContainsUnit.contains_unit

@[simp]
lemma Frame.univ_mem [Frame.ContainsUnit F] (x) : Set.univ ∈ F.𝒩 x := by
  haveI := @F.contains_unit.symm.subset;
  simpa using @this x;

instance : Frame.simple_blackhole.ContainsUnit := ⟨by ext x; simp⟩

@[simp]
lemma valid_axiomN_of_ContainsUnit [F.ContainsUnit] : F ⊧ Axioms.N := by
  intro V x;
  simp [Satisfies, F.contains_unit];

lemma containsUnit_of_valid_axiomN (h : F ⊧ Axioms.N) : F.ContainsUnit := by
  constructor;
  ext x;
  simpa [Satisfies] using @h (λ _ => Set.univ) x;

section

variable [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.E 𝓢]

open Entailment
open MaximalConsistentSet
open proofset

instance [Entailment.HasAxiomN 𝓢] : (minimalCanonicity 𝓢).toModel.ContainsUnit := by
  constructor;
  ext x;
  simp only [minimalCanonicity, Canonicity.toModel, Frame.box, Set.mem_setOf_eq, Set.mem_univ, iff_true];
  use ⊤;
  simp [MaximalConsistentSet.mem_of_prove]

end


end LO.Modal.Neighborhood
