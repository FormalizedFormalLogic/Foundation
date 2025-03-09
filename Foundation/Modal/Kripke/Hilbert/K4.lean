import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Geachean

protected abbrev Kripke.FrameClass.trans : FrameClass := { F | Transitive F }
protected abbrev Kripke.FiniteFrameClass.trans : FiniteFrameClass := { F | Transitive F.Rel }

instance : Kripke.FrameClass.trans.DefinedBy Hilbert.K4.axioms := by
  convert FrameClass.multiGeachean.definability' {⟨0, 2, 1, 0⟩};
  . unfold Kripke.FrameClass.trans FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.transitive_def];
  . exact Hilbert.K4.eq_Geach;

namespace Hilbert.K4.Kripke

instance sound : Sound (Hilbert.K4) Kripke.FrameClass.trans := inferInstance

instance consistent : Entailment.Consistent (Hilbert.K4) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance canonical : Canonical (Hilbert.K4) Kripke.FrameClass.trans := ⟨Canonical.transitive⟩

instance complete : Complete (Hilbert.K4) Kripke.FrameClass.trans := inferInstance

open finestFilterationTransitiveClosureModel in
instance finite_complete : Complete (Hilbert.K4) Kripke.FiniteFrameClass.trans := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F F_trans V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf F_trans) (by aesop) |>.mpr;
  apply validOnModel_of_validOnFiniteFrameClass hp;
  . exact finestFilterationTransitiveClosureModel.transitive;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end Hilbert.K4.Kripke

end LO.Modal
