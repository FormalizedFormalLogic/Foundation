import Foundation.Modal.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke

namespace Hilbert.K

instance Kripke.sound : Sound (Hilbert.K) FrameClass.all := inferInstance

instance : Entailment.Consistent (Hilbert.K) := Hilbert.consistent_of_FrameClass FrameClass.all (by simp)

instance : Kripke.Canonical (Hilbert.K) FrameClass.all := ⟨by trivial⟩

instance Kripke.complete : Complete (Hilbert.K) FrameClass.all := inferInstance

instance Kripke.complete_finiteAux : Complete (Hilbert.K) (FiniteFrameClass.all) := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFilterationModel M ↑φ.subformulas;

  apply filteration FM (coarsestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply validOnModel_of_validOnFiniteFrameClass hp;
  . tauto;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end Hilbert.K

end LO.Modal
