import Foundation.Propositional.Kripke.AxiomKrieselPutnam
import Foundation.Propositional.Kripke.Logic.Int

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev krieselputnam : FrameClass := { F | SatisfiesKriselPutnamCondition _ F }

end Kripke.FrameClass


namespace Hilbert.KP.Kripke

instance sound : Sound Hilbert.KP FrameClass.krieselputnam := instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_KrieselPutnam_of_KrieselPutnamCondition

instance consistent : Entailment.Consistent Hilbert.KP := consistent_of_sound_frameclass FrameClass.krieselputnam $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.KP FrameClass.krieselputnam := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.KP FrameClass.krieselputnam := inferInstance

end Hilbert.KP.Kripke


namespace Logic.KP

lemma Kripke.krieselputnam : Logic.KP = Kripke.FrameClass.krieselputnam.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

end Logic.KP

end LO.Propositional
