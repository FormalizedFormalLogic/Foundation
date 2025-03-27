import Foundation.Modal.Entailment.K

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S}

namespace KTc

variable [Entailment.Modal.KTc 𝓢]

protected def axiomFour : 𝓢 ⊢ Axioms.Four φ := axiomTc
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ KTc.axiomFour⟩

protected def axiomFive : 𝓢 ⊢ ◇φ ➝ □◇φ := axiomTc
instance : HasAxiomFive 𝓢 := ⟨fun _ ↦ KTc.axiomFive⟩

protected def axiomDiaT : 𝓢 ⊢ ◇φ ➝ φ := by
  apply cTrans (φOfKφψ diaDuality) ?_;
  apply contra₂';
  exact axiomTc;
instance : HasAxiomDiaT 𝓢 := ⟨fun _ ↦ KTc.axiomDiaT⟩

end KTc


namespace KTc'

variable [Entailment.Modal.KTc' 𝓢]

protected def axiomTc : 𝓢 ⊢ φ ➝ □φ := cTrans (contra₃' (cTrans (ψOfKφψ diaDuality) diaT)) box_dne
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ KTc'.axiomTc⟩

end KTc'


end LO.Entailment
