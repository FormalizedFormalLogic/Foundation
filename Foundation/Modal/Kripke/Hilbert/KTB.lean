import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration
import Foundation.Modal.Kripke.FiniteFrame

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveSymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Symmetric F }
abbrev Kripke.ReflexiveSymmetricFiniteFrameClass : FiniteFrameClass := { F | Reflexive F.Rel ∧ Symmetric F.Rel }

namespace Hilbert.KTB

instance Kripke.consistent : System.Consistent (Hilbert.KTB) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KTB) (Kripke.ReflexiveSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold ReflexiveSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.symmetric_def];

instance Kripke.finiteComplete : Complete (Hilbert.KTB) (ReflexiveSymmetricFiniteFrameClass) := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationModel M φ.subformulas;
  apply filteration FM (finestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulas) by
      simp only [FiniteFrameClass.toFrameClass, ReflexiveSymmetricFiniteFrameClass, Set.mem_image, Set.mem_setOf_eq];
      use ⟨FM.toFrame⟩;
      refine ⟨⟨?_, ?_⟩, ?_⟩;
      . apply reflexive_filterOf_of_reflexive (finestFilterationModel.filterOf);
        exact F_refl;
      . apply finestFilterationModel.symmetric_of_symmetric;
        exact F_symm;
      . rfl;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val
⟩

end Hilbert.KTB

end LO.Modal
