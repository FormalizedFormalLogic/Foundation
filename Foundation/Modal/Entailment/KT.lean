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
  apply cTrans ?_ (ψOfKφψ diaDuality);
  exact cTrans dni $ contra₀' axiomT;
instance : HasAxiomDiaTc 𝓢 := ⟨fun _ ↦ KT.axiomDiaTc⟩

protected def axiomP : 𝓢 ⊢ ∼□⊥ := nφOfCφO axiomT
instance : HasAxiomP 𝓢 := ⟨KT.axiomP⟩
instance : Entailment.Modal.KP 𝓢 where
instance : Entailment.Modal.KD 𝓢 where

end KT


namespace KT'

variable [Entailment.Modal.KT' 𝓢]

protected def axiomT : 𝓢 ⊢ □φ ➝ φ := cTrans box_dni (contra₃' (cTrans diaTc diaDuality_mp))

instance : HasAxiomT 𝓢 := ⟨fun _ ↦ KT'.axiomT⟩
instance : Entailment.Modal.KT 𝓢 where
instance : Entailment.Modal.KD 𝓢 where

end KT'


end LO.Entailment
