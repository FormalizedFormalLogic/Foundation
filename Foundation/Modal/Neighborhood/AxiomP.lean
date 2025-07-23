import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

class Frame.NotContainsEmpty (F : Frame) : Prop where
  not_contains_empty : ∀ x, ∅ ∉ F.𝒩 x

lemma Frame.not_contains_empty [F.NotContainsEmpty] {x : F} : ∅ ∉ F.𝒩 x := Frame.NotContainsEmpty.not_contains_empty x

instance : Frame.simple_blackhole.NotContainsEmpty := ⟨by simp only [Set.mem_singleton_iff, forall_const]; tauto_set⟩

@[simp]
lemma valid_axiomP_of_notContainsEmpty [F.NotContainsEmpty] : F ⊧ Axioms.P := by
  intro V x;
  simp only [
    Satisfies, Model.truthset.eq_neg, Model.truthset.eq_box, Model.truthset.eq_bot,
    Set.mem_compl_iff, Set.mem_setOf_eq
  ];
  apply Frame.not_contains_empty;

lemma notContainsEmpty_of_valid_axiomP (h : F ⊧ Axioms.P) : F.NotContainsEmpty := by
  constructor;
  intro x;
  have := @h (λ _ => ∅) x;
  simpa [Satisfies] using this;

end LO.Modal.Neighborhood
