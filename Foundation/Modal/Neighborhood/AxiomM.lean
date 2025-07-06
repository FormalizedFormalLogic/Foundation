import Foundation.Modal.Tableau
import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

class Frame.IsMonotonic (F : Frame) : Prop where
  mono : ∀ X Y : Set F, X ⊆ Y → F.η X ⊆ F.η Y

lemma Frame.mono [Frame.IsMonotonic F] {X Y : Set F} : X ⊆ Y → F.η X ⊆ F.η Y := by apply IsMonotonic.mono

instance : Frame.trivial.IsMonotonic := ⟨by simp⟩

lemma valid_axiomM_of_isMonotonic [F.IsMonotonic] : F ⊧ Axioms.M (.atom 0) (.atom 1) := by
  intro V x;
  simp only [
    Satisfies, Model.truthset.eq_imp, Model.truthset.eq_box, Model.truthset.eq_and,
    Model.truthset.eq_atom, Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_inter_iff
  ]
  apply not_or_of_imp;
  intro h;
  constructor <;>
  . apply F.mono (by simp) h;

end LO.Modal.Neighborhood
