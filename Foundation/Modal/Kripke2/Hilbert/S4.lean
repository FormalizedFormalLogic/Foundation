import Foundation.Modal.Kripke2.Hilbert.Geach
import Foundation.Modal.Kripke2.Filteration
import Foundation.Modal.Kripke2.FiniteFrame

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveTransitiveFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F }
abbrev Kripke.ReflexiveTransitiveFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel }

namespace Hilbert.S4

instance Kripke.consistent : System.Consistent (Hilbert.S4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.S4) (Kripke.ReflexiveTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩});
  . exact eq_Geach;
  . unfold ReflexiveTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def];

open finestFilterationTransitiveClosureModel in
instance Kripke.finiteComplete : Complete (Hilbert.S4) (ReflexiveTransitiveFiniteFrameClass) := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_trans⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply @filteration M φ.subformulas _ FM ?filterOf x φ (by simp) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulas) by
      simp only [FiniteFrameClass.toFrameClass];
      use ⟨FM.toFrame⟩;
      refine ⟨⟨?_, transitive⟩, rfl⟩;
      . exact reflexive_of_transitive_reflexive (by apply F_trans) F_refl;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val;
  . apply finestFilterationTransitiveClosureModel.filterOf;
    exact F_trans;
⟩

end Hilbert.S4

end LO.Modal
