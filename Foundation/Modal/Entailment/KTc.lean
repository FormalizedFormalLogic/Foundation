module

public import Foundation.Modal.Entailment.K

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

namespace KTc

variable [Entailment.KTc 𝓢]

protected def axiomFour : 𝓢 ⊢! Axioms.Four φ := axiomTc
instance : HasAxiomFour 𝓢 := ⟨KTc.axiomFour⟩

protected def axiomFive : 𝓢 ⊢! ◇φ ➝ □◇φ := axiomTc
instance : HasAxiomFive 𝓢 := ⟨KTc.axiomFive⟩

protected def axiomDiaT : 𝓢 ⊢! ◇φ ➝ φ := by
  apply C_trans (K_left diaDuality) ?_;
  apply CN_of_CN_left;
  exact axiomTc;
instance : HasAxiomDiaT 𝓢 := ⟨KTc.axiomDiaT⟩

end KTc


namespace KTc'

variable [Entailment.KTc' 𝓢]

protected def axiomTc : 𝓢 ⊢! φ ➝ □φ := C_trans (C_of_CNN (C_trans (K_right diaDuality) diaT)) box_dne
instance : HasAxiomTc 𝓢 := ⟨KTc'.axiomTc⟩

end KTc'


end LO.Modal.Entailment
end
