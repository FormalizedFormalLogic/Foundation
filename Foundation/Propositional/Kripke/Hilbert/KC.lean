import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomWeakLEM
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Filteration
import Foundation.Propositional.Kripke.Rooted

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev confluent : FrameClass := { F | IsConfluent _ F }
protected abbrev finite_confluent : FrameClass := { F | Finite F ∧ IsConfluent _ F }

end Kripke.FrameClass


namespace Hilbert.KC.Kripke

instance sound : Sound Hilbert.KC FrameClass.confluent :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_WeakLEM_of_confluent

instance sound_finite : Sound Hilbert.KC FrameClass.finite_confluent :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F ⟨_, hF⟩ _ rfl;
    apply validate_WeakLEM_of_confluent

instance consistent : Entailment.Consistent Hilbert.KC := consistent_of_sound_frameclass FrameClass.confluent $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.KC FrameClass.confluent := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.KC FrameClass.confluent := inferInstance

section FFP

open
  finestFilterationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.KC) FrameClass.finite_confluent := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F F_con V r;
  replace F_con := Set.mem_setOf_eq.mp F_con;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFilterationTransitiveClosureModel RM (φ.subformulas);
  apply filteration FRM finestFilterationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_⟩;
  . apply FilterEqvQuotient.finite; simp;
  . apply isConfluent_iff _ _ |>.mpr;
    rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ ⟨RXY, RXZ⟩;
    . simp only [exists_and_left, and_self];
      let Z : RM.World := ⟨z, by tauto⟩;
      use ⟦Z⟧;
      apply Relation.TransGen.single;
      use Z;
      constructor;
      . tauto;
      . use Z;
        constructor;
        . tauto;
        . apply F.refl;
    . let Y : RM.World := ⟨y, by tauto⟩;
      let Z : RM.World := ⟨z, by tauto⟩;
      use ⟦Z⟧;
      constructor;
      . apply TransGen.single;
        use Y, Z;
        tauto;
      . apply Frame.refl;
    . let Y : RM.World := ⟨y, by tauto⟩;
      let Z : RM.World := ⟨z, by tauto⟩;
      use ⟦Y⟧;
      constructor;
      . apply Frame.refl;
      . apply TransGen.single;
        use Z, Y;
        tauto;
    . obtain ⟨u, Ryu, Rzu⟩ := IsConfluent.confluent ⟨Rry, Rrz⟩;
      have : r ≺ u := F.trans Rry Ryu;
      let Y : RM.World := ⟨y, by tauto⟩;
      let Z : RM.World := ⟨z, by tauto⟩;
      let U : RM.World := ⟨u, by tauto⟩;
      use ⟦U⟧;
      constructor;
      . apply TransGen.single;
        use Y, U;
        tauto;
      . apply TransGen.single;
        use Z, U;
        tauto;
⟩

end FFP


end Hilbert.KC.Kripke

end LO.Propositional
