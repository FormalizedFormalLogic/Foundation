import Foundation.Modal.Hilbert2.K
import Foundation.Modal.Kripke2.Soundness
import Foundation.Modal.Kripke2.Completeness
import Foundation.Modal.Kripke2.Filteration
import Foundation.Modal.Kripke2.FiniteFrame

namespace LO.Modal

open Kripke

namespace Hilbert.K

instance : System.Consistent (Hilbert.K) := Hilbert.instConsistent AllFrameClass

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
      simp only [FiniteFrameClass.toFrameClass, AllFiniteFrameClass, Set.image_univ, Set.mem_range];
      tauto;
    apply FilterEqvQuotient.finite;
    simp;
  ) FM.Val
⟩

end Hilbert.K

end LO.Modal
