import Foundation.Modal.Entailment.K
import Foundation.Modal.Entailment.KP
import Foundation.Modal.Entailment.KD

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S}

namespace KT

variable [Entailment.Modal.KT 𝓢]

def axiomDiaTc : 𝓢 ⊢ φ ➝ ◇φ := by
  apply C_trans ?_ (K_right diaDuality);
  exact C_trans dni $ contra axiomT;
instance : HasAxiomDiaTc 𝓢 := ⟨fun _ ↦ KT.axiomDiaTc⟩

protected def axiomP : 𝓢 ⊢ ∼□⊥ := N_of_CO axiomT
instance : HasAxiomP 𝓢 := ⟨KT.axiomP⟩
instance : Entailment.Modal.KP 𝓢 where
instance : Entailment.Modal.KD 𝓢 where

end KT


namespace KT'

variable [Entailment.Modal.KT' 𝓢]

protected def axiomT : 𝓢 ⊢ □φ ➝ φ := C_trans box_dni (C_of_CNN (C_trans diaTc diaDuality_mp))

instance : HasAxiomT 𝓢 := ⟨fun _ ↦ KT'.axiomT⟩
instance : Entailment.Modal.KT 𝓢 where
instance : Entailment.Modal.KD 𝓢 where

end KT'


end LO.Entailment
