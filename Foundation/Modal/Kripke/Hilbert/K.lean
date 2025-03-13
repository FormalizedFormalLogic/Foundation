import Foundation.Modal.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Hilbert.K

instance Kripke.sound : Sound (Hilbert.K) FrameClass.all := instSound_of_validates_axioms FrameClass.all.validates_axiomK

instance : Entailment.Consistent (Hilbert.K) := consistent_of_sound_frameclass FrameClass.all (by simp)

instance : Kripke.Canonical (Hilbert.K) FrameClass.all := ⟨by trivial⟩

instance Kripke.complete : Complete (Hilbert.K) FrameClass.all := inferInstance

instance Kripke.complete_finite : Complete (Hilbert.K) (FrameClass.finite_all) := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFilterationModel M ↑φ.subformulas;

  apply filteration FM (coarsestFilterationModel.filterOf) (by aesop) |>.mpr;
  apply hp;
  apply Frame.isFinite_iff _ |>.mpr
  apply FilterEqvQuotient.finite;
  simp;
⟩

end Hilbert.K

end LO.Modal
