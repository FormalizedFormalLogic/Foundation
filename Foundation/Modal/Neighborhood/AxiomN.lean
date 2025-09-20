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
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.EN 𝓢]

open Entailment
open MaximalConsistentSet
open MaximalConsistentSet.proofset

instance : (minimalCanonicalFrame 𝓢).ContainsUnit := by
  constructor;
  dsimp [minimalCanonicalFrame, Frame.mk_ℬ, Frame.box];
  split;
  . rename_i h;
    apply iff_provable_eq_univ.mp;
    apply nec!;
    apply iff_provable_eq_univ.mpr;
    apply h.choose_spec.symm;
  . rename_i h;
    push_neg at h;
    simpa using @h ⊤;

end


end LO.Modal.Neighborhood
