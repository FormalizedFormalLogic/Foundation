import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Completeness
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke


namespace Kripke

protected abbrev FrameClass.K : FrameClass := Set.univ
protected abbrev FrameClass.finite_K : FrameClass := { F | F.IsFinite }

end Kripke



instance : Sound Modal.K FrameClass.K := instSound_of_validates_axioms $ by
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  intro F _;
  exact Formula.Kripke.ValidOnFrame.axiomK;

instance : Sound Modal.K FrameClass.finite_K := instSound_of_validates_axioms $ by
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  intro F hF;
  exact Formula.Kripke.ValidOnFrame.axiomK;

instance : Entailment.Consistent Modal.K := consistent_of_sound_frameclass FrameClass.K $ by
  use whitepoint
  simp;

instance : Kripke.Canonical Modal.K FrameClass.K := ⟨by trivial⟩

instance : Complete Modal.K FrameClass.K := inferInstance

instance : Complete Modal.K (FrameClass.finite_K) := ⟨by
  intro φ hp;
  apply Complete.complete (𝓜 := FrameClass.K);
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := coarsestFiltrationModel M ↑φ.subformulas;
  apply filtration FM (coarsestFiltrationModel.filterOf) (by simp) |>.mpr;
  apply hp;
  apply Frame.isFinite_iff _ |>.mpr
  apply FilterEqvQuotient.finite;
  simp;
⟩


end LO.Modal
