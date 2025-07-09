import Foundation.Modal.Tableau
import Foundation.Modal.Neighborhood.Basic

namespace LO.Modal.Neighborhood

open Formula.Neighborhood

variable {F : Frame}

class Frame.IsRegular (F : Frame) : Prop where
  regular : ∀ X Y : Set F, (F.η X) ∩ (F.η Y) ⊆ F.η (X ∩ Y)

lemma Frame.regular [Frame.IsRegular F] {X Y : Set F} : (F.η X) ∩ (F.η Y) ⊆ F.η (X ∩ Y) := by apply IsRegular.regular

instance : Frame.simple_blackhole.IsRegular := ⟨by
  intro X Y e;
  simp_all;
⟩

lemma valid_axiomC_of_isRegular [F.IsRegular] : F ⊧ Axioms.C (.atom 0) (.atom 1) := by
  intro V x;
  simp only [
    Satisfies, Model.truthset.eq_imp, Model.truthset.eq_and, Model.truthset.eq_box,
    Model.truthset.eq_atom, Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_setOf_eq
  ];
  apply not_or_of_imp;
  rintro ⟨h₁, h₂⟩;
  apply F.regular;
  constructor;
  . apply h₁;
  . apply h₂;

end LO.Modal.Neighborhood
