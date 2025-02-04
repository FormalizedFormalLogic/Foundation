import Foundation.Modal.Hilbert2.K
import Foundation.Modal.Kripke2.Hilbert.Soundness
import Foundation.Modal.Kripke2.Completeness
import Foundation.Modal.Kripke2.Filteration
import Foundation.Modal.Kripke2.FiniteFrame

namespace LO.Modal

open Kripke

namespace Hilbert.K

instance Kripke.sound : Sound (Hilbert.K) AllFrameClass := inferInstance

instance : System.Consistent (Hilbert.K) := Hilbert.consistent_of_FrameClass AllFrameClass

instance : Kripke.Canonical (Hilbert.K) (AllFrameClass) := ⟨by trivial⟩

instance Kripke.CompleteAll : Complete (Hilbert.K) (AllFrameClass) := inferInstance

instance Kripke.CompleteAllFinite : Complete (Hilbert.K) (AllFiniteFrameClass) := ⟨by
  intro φ hp;
  apply Kripke.CompleteAll.complete;
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
