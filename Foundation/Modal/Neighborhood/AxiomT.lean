import Foundation.Modal.Tableau
import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

class Frame.IsReflexive (F : Frame) : Prop where
  reflexive : ∀ X : Set F, F.β X ⊆ X

lemma Frame.refl [Frame.IsReflexive F] {X : Set F} : F.β X ⊆ X := IsReflexive.reflexive X

lemma valid_axiomT_of_isReflexive [Frame.IsReflexive F] : F ⊧ Axioms.T (.atom 0) := by
  intro V x;
  apply not_or_of_imp;
  intro h;
  apply F.refl;
  apply h;

end LO.Modal.Neighborhood
