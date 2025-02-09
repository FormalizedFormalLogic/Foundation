import Foundation.Modal.System.K
import Foundation.Modal.System.KP
import Foundation.Modal.System.KD

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S}

namespace KT

variable [System.KT 𝓢]

def axiomDiaTc : 𝓢 ⊢ φ ➝ ◇φ := by
  apply impTrans'' ?_ (and₂' diaDuality);
  exact impTrans'' dni $ contra₀' axiomT;
instance : HasAxiomDiaTc 𝓢 := ⟨fun _ ↦ KT.axiomDiaTc⟩

protected def axiomP : 𝓢 ⊢ ∼□⊥ := neg_equiv'.mpr axiomT
instance : HasAxiomP 𝓢 := ⟨KT.axiomP⟩
instance : System.KP 𝓢 where
instance : System.KD 𝓢 where

end KT


namespace KT'

variable [System.KT' 𝓢]

protected def axiomT : 𝓢 ⊢ □φ ➝ φ := impTrans'' box_dni (contra₃' (impTrans'' diaTc diaDuality_mp))

instance : HasAxiomT 𝓢 := ⟨fun _ ↦ KT'.axiomT⟩
instance : System.KT 𝓢 where
instance : System.KD 𝓢 where

end KT'


end LO.System
