import Foundation.Modal.Tableau
import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

/-- Most inside keeps most-insideness -/
class Frame.ContainsUnit (F : Frame) : Prop where
  contains_unit : ∀ x, Set.univ ∈ F.𝒩 x

lemma Frame.contains_unit [Frame.ContainsUnit F] {x : F} : Set.univ ∈ F.𝒩 x := Frame.ContainsUnit.contains_unit x

instance : Frame.simple_blackhole.ContainsUnit := ⟨by simp⟩

@[simp]
lemma valid_axiomN_of_ContainsUnit [F.ContainsUnit] : F ⊧ Axioms.N := by
  intro V x;
  simp [Satisfies, F.contains_unit];

end LO.Modal.Neighborhood
