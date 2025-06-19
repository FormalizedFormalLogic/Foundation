import Foundation.Propositional.Kripke.AxiomKrieselPutnam
import Foundation.Propositional.Kripke.Logic.Int

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke

protected abbrev Frame.IsKP := Frame.SatisfiesKriselPutnamCondition

protected abbrev FrameClass.KP : FrameClass := { F | F.SatisfiesKriselPutnamCondition }

end Kripke


namespace Hilbert.KP.Kripke

instance sound : Sound Hilbert.KP FrameClass.KP := instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomKrieselPutnam_of_satisfiesKrieselPutnamCondition

instance consistent : Entailment.Consistent Hilbert.KP := consistent_of_sound_frameclass FrameClass.KP $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.KP FrameClass.KP := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.KP FrameClass.KP := inferInstance

end Hilbert.KP.Kripke


namespace Logic.KP

lemma Kripke.KP : Logic.KP = FrameClass.KP.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

end Logic.KP

end LO.Propositional
