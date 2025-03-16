import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke

variable {F : Frame}

protected abbrev FrameClass.trans : FrameClass := { F | IsTrans _ F }

namespace FrameClass.trans

@[simp] lemma nonempty : FrameClass.trans.Nonempty := by
  use whitepoint;
  simp only [Set.mem_setOf_eq];
  infer_instance;

lemma validates_AxiomFour : FrameClass.trans.ValidatesFormula (Axioms.Four (.atom 0)) := by
  apply ValidatesFormula_of;
  apply Kripke.validate_AxiomFour_of_transitive;

lemma validates_HilbertK4 : FrameClass.trans.Validates Hilbert.K4.axioms := Validates.withAxiomK validates_AxiomFour

end FrameClass.trans


protected abbrev FrameClass.finite_trans : FrameClass := { F | Finite F ∧ IsTrans _ F }

end Kripke


namespace Hilbert.K4.Kripke

instance sound : Sound (Hilbert.K4) Kripke.FrameClass.trans :=
  instSound_of_validates_axioms FrameClass.trans.validates_HilbertK4

instance consistent : Entailment.Consistent (Hilbert.K4) :=
  consistent_of_sound_frameclass FrameClass.trans (by simp)

instance canonical : Canonical (Hilbert.K4) Kripke.FrameClass.trans := ⟨Canonical.transitive⟩

instance complete : Complete (Hilbert.K4) Kripke.FrameClass.trans := inferInstance

open finestFilterationTransitiveClosureModel in
instance finite_complete : Complete (Hilbert.K4) Kripke.FrameClass.finite_trans := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F F_trans V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf (trans := F_trans)) (by aesop) |>.mpr;
  apply hp;
  refine ⟨?_, inferInstance⟩;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end Hilbert.K4.Kripke

end LO.Modal
