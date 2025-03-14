import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Filteration
import Foundation.Propositional.Kripke.Rooted

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev connected : FrameClass := { F | Connected F }
protected abbrev finite_connected : FrameClass := { F | F.IsFinite ∧ Connected F }

namespace connected

@[simp]
instance nonempty : FrameClass.connected.Nonempty := by
  use whitepoint;
  simp [Connected];

lemma validates_AxiomWLEM : FrameClass.connected.ValidatesFormula (Axioms.Dummett (.atom 0) (.atom 1)) := by
  rintro F _ _ rfl;
  apply validate_Dummett_of_connected $ by assumption

instance validate_HilbertLC : FrameClass.connected.Validates (Hilbert.LC.axioms) := by
  apply FrameClass.Validates.withAxiomEFQ;
  apply validates_AxiomWLEM;

end connected

end Kripke.FrameClass


namespace Hilbert.LC.Kripke

instance sound : Sound Hilbert.LC FrameClass.connected :=
  instSound_of_validates_axioms FrameClass.connected.validate_HilbertLC

instance consistent : Entailment.Consistent Hilbert.LC := consistent_of_sound_frameclass FrameClass.connected (by simp)

instance canonical : Canonical Hilbert.LC FrameClass.connected := ⟨Canonical.connected⟩

instance complete : Complete Hilbert.LC FrameClass.connected := inferInstance

section FFP

open
  finestFilterationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.LC) FrameClass.finite_connected := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F F_conn V r;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFilterationTransitiveClosureModel RM (φ.subformulas);
  apply filteration FRM finestFilterationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_⟩;
  . apply Frame.isFinite_iff _ |>.mpr
    apply FilterEqvQuotient.finite;
    simp;
  . rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ ⟨RXY, RXZ⟩;
    . simp;
      apply Relation.TransGen.single
      use ⟨z, by tauto⟩;
      constructor;
      . tauto
      . use ⟨z, by tauto⟩;
        constructor;
        . tauto;
        . exact F.rel_refl';
    . left;
      apply Relation.TransGen.single;
      use ⟨y, by tauto⟩, ⟨z, by tauto⟩;
      tauto;
    . right;
      apply Relation.TransGen.single;
      use ⟨z, by tauto⟩, ⟨y, by tauto⟩;
      tauto;
    . rcases F_conn ⟨Rry, Rrz⟩ with (Ryz | Rrw);
      . left;
        apply Relation.TransGen.single;
        use ⟨y, by tauto⟩, ⟨z, by tauto⟩;
        tauto;
      . right;
        apply Relation.TransGen.single;
        use ⟨z, by tauto⟩, ⟨y, by tauto⟩;
        tauto;
⟩

end FFP


end Hilbert.LC.Kripke

end LO.Propositional
