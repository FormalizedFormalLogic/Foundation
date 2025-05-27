import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert.Basic
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.trans : FrameClass := { F | IsTrans _ F }
protected abbrev Kripke.FrameClass.finite_trans : FrameClass := { F | Finite F ∧ IsTrans _ F }

namespace Hilbert.K4.Kripke

instance sound : Sound (Hilbert.K4) Kripke.FrameClass.trans := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_trans φ rfl;
  apply validate_AxiomFour_of_transitive (trans := F_trans);

instance consistent : Entailment.Consistent (Hilbert.K4) :=
  consistent_of_sound_frameclass FrameClass.trans $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

instance canonical : Canonical (Hilbert.K4) Kripke.FrameClass.trans := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.K4) Kripke.FrameClass.trans := inferInstance

open finestFiltrationTransitiveClosureModel in
instance finite_complete : Complete (Hilbert.K4) Kripke.FrameClass.finite_trans := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F F_trans V x;
  replace F_trans := Set.mem_setOf_eq.mp F_trans;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationTransitiveClosureModel M φ.subformulas;
  apply filtration FM (finestFiltrationTransitiveClosureModel.filterOf) (by subformula) |>.mpr;
  apply hp;
  refine ⟨?_, inferInstance⟩;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end Hilbert.K4.Kripke

lemma Logic.K4.Kripke.trans : Logic.K4 = FrameClass.trans.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal
