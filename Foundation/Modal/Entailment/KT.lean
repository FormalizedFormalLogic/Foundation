import Foundation.Modal.Entailment.K
import Foundation.Modal.Entailment.KP
import Foundation.Modal.Entailment.KD
import Foundation.Modal.Entailment.ET

namespace LO.Modal.Entailment

open LO.Entailment

variable {S F : Type*} [DecidableEq F] [BasicModalLogicalConnective F] [Entailment S F]
variable {𝓢 : S}


namespace KT'

variable [Entailment.KT' 𝓢]

instance : HasAxiomT 𝓢 := ⟨fun _ ↦ C_trans box_dni (C_of_CNN (C_trans diaTc diaDuality_mp))⟩
instance : Entailment.KT 𝓢 where
instance : Entailment.KP 𝓢 where
instance : Entailment.KD 𝓢 where

end KT'


section

variable [Entailment.KT 𝓢]

instance : Entailment.ET 𝓢 where
instance : Entailment.KD 𝓢 where

omit [DecidableEq F] in
@[simp] lemma reduce_box_in_CAnt! : 𝓢 ⊢ □^[(i + n)]φ ➝ □^[i]φ := by
  induction n with
  | zero => simp;
  | succ n ih =>
    simp only [show (i + (n + 1)) = (i + n) + 1 by omega, Box.multibox_succ];
    apply C!_trans ?_ ih;
    apply axiomT!;

end

end LO.Modal.Entailment
