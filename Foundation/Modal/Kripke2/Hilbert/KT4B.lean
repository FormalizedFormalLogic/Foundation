import Foundation.Modal.Kripke2.Hilbert.Geach
import Foundation.Modal.Kripke2.Filteration
import Foundation.Modal.Kripke2.FiniteFrame

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveTransitiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Symmetric F }
abbrev Kripke.ReflexiveTransitiveSymmetricFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Transitive F.Rel ∧ Symmetric F.Rel }

namespace Hilbert.KT4B

instance Kripke.consistent : System.Consistent (Hilbert.KT4B) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KT4B) (Kripke.ReflexiveTransitiveSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold ReflexiveTransitiveSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.symmetric_def, Geachean.transitive_def];

open finestFilterationTransitiveClosureModel in
instance Kripke.finiteComplete : Complete (Hilbert.KT4B) (ReflexiveTransitiveSymmetricFiniteFrameClass) := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_trans, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply @filteration M φ.subformulas _ FM ?filterOf x φ (by simp) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulas) by
      simp only [FiniteFrameClass.toFrameClass, Set.mem_image, Set.mem_setOf_eq];
      use ⟨FM.toFrame⟩;
      refine ⟨⟨?refl, transitive, ?symm⟩, rfl⟩;
      . exact reflexive_of_transitive_reflexive (by apply F_trans) F_refl;
      . exact symmetric_of_symmetric F_symm;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val;
  . apply finestFilterationTransitiveClosureModel.filterOf
    exact F_trans;
⟩

end Hilbert.KT4B


end LO.Modal
