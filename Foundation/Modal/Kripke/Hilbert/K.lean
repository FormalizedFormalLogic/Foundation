import Foundation.Modal.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Filteration
import Foundation.Modal.Kripke.FiniteFrame

namespace LO.Modal

open Kripke

namespace Hilbert.K

instance Kripke.sound : Sound (Hilbert.K) AllFrameClass := inferInstance

instance : System.Consistent (Hilbert.K) := Hilbert.consistent_of_FrameClass AllFrameClass

instance : Kripke.Canonical (Hilbert.K) (AllFrameClass) := ⟨by trivial⟩

instance Kripke.completeAll : Complete (Hilbert.K) (AllFrameClass) := inferInstance

instance Kripke.completeAllFinite : Complete (Hilbert.K) (AllFiniteFrameClass) := ⟨by
  intro φ hp;
  apply Kripke.completeAll.complete;
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFilterationModel M ↑φ.subformulas;

  apply filteration FM (coarsestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp (by
    suffices Finite (FilterEqvQuotient M φ.subformulas) by
      use ⟨FM.toFrame⟩;
      simp [FiniteFrameClass.toFrameClass];
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val
⟩

end Hilbert.K

end LO.Modal
