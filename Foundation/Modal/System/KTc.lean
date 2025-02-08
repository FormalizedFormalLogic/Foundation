import Foundation.Modal.System.K

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S}

namespace KTc

variable [System.KTc 𝓢]

protected def axiomFour : 𝓢 ⊢ Axioms.Four φ := axiomTc
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ KTc.axiomFour⟩

protected def axiomFive : 𝓢 ⊢ ◇φ ➝ □◇φ := axiomTc
instance : HasAxiomFive 𝓢 := ⟨fun _ ↦ KTc.axiomFive⟩

protected def axiomDiaT : 𝓢 ⊢ ◇φ ➝ φ := by
  apply impTrans'' (and₁' diaDuality) ?_;
  apply contra₂';
  exact axiomTc;
instance : HasAxiomDiaT 𝓢 := ⟨fun _ ↦ KTc.axiomDiaT⟩

end KTc


namespace KTc'

variable [System.KTc' 𝓢]

protected def axiomTc : 𝓢 ⊢ φ ➝ □φ := impTrans'' (contra₃' (impTrans'' (and₂' diaDuality) diaT)) box_dne
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ KTc'.axiomTc⟩

end KTc'


end LO.System
