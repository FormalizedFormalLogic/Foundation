import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean


namespace Kripke.FrameClass

protected abbrev trans : FrameClass := { F | Transitive F }

protected abbrev finite_trans : FrameClass := { F | F.IsFinite ∧ Transitive F.Rel }

namespace trans

lemma isMultiGeachean : FrameClass.trans = FrameClass.multiGeachean {⟨0, 2, 1, 0⟩} := by
  ext F;
  simp [Geachean.transitive_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.trans.Nonempty := by simp [trans.isMultiGeachean]

lemma validates_AxiomFour : FrameClass.trans.ValidatesFormula (Axioms.Four (.atom 0)) := by
  rintro F F_trans _ rfl;
  apply validate_AxiomFour_of_transitive $ by assumption

lemma validates_HilbertK4 : FrameClass.trans.Validates Hilbert.K4.axioms := by
  apply FrameClass.Validates.withAxiomK;
  apply validates_AxiomFour;

end trans

end Kripke.FrameClass



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
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf F_trans) (by aesop) |>.mpr;
  apply hp;
  refine ⟨?_, ?_⟩;
  . apply Frame.isFinite_iff _ |>.mpr
    apply FilterEqvQuotient.finite;
    simp;
  . exact finestFilterationTransitiveClosureModel.transitive;
⟩

end Hilbert.K4.Kripke

end LO.Modal
