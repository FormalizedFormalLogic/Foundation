import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Filtration
import Foundation.Propositional.Kripke.Rooted

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev connected : FrameClass := { F | IsConnected _ F }
protected abbrev finite_connected : FrameClass := { F | Finite F ∧ IsConnected _ F }

end Kripke.FrameClass


namespace Hilbert.LC.Kripke

instance sound : Sound Hilbert.LC FrameClass.connected := instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_Dummett_of_connected

instance sound_finite : Sound Hilbert.LC FrameClass.finite_connected :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F ⟨_, hF⟩ _ rfl;
    apply validate_Dummett_of_connected

instance consistent : Entailment.Consistent Hilbert.LC := consistent_of_sound_frameclass FrameClass.connected $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.LC FrameClass.connected := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.LC FrameClass.connected := inferInstance

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.LC) FrameClass.finite_connected := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F F_conn V r;
  replace F_conn := Set.mem_setOf_eq.mp F_conn;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM finestFiltrationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_⟩;
  . apply FilterEqvQuotient.finite;
    simp;
  . apply isConnected_iff _ _ |>.mpr;
    rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ ⟨RXY, RXZ⟩;
    . simp only [exists_and_left, or_self];
      apply Relation.TransGen.single
      use ⟨z, by tauto⟩;
      constructor;
      . tauto
      . use ⟨z, by tauto⟩;
        constructor;
        . tauto;
        . exact F.refl;
    . left;
      apply Relation.TransGen.single;
      use ⟨y, by tauto⟩, ⟨z, by tauto⟩;
      tauto;
    . right;
      apply Relation.TransGen.single;
      use ⟨z, by tauto⟩, ⟨y, by tauto⟩;
      tauto;
    . let Y : RM.World := ⟨y, by tauto⟩;
      let Z : RM.World := ⟨z, by tauto⟩;
      rcases IsConnected.connected ⟨Rry, Rrz⟩ with (Ryz | Rrw);
      . left;
        apply Relation.TransGen.single;
        use Y, Z;
        tauto;
      . right;
        apply Relation.TransGen.single;
        use Z, Y;
        tauto;
⟩

end FFP


end Hilbert.LC.Kripke

end LO.Propositional
