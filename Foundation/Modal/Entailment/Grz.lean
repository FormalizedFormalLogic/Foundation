module

public import Foundation.Modal.Entailment.K

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.Grz 𝓢]

namespace Grz

noncomputable def lemma_axiomFour_axiomT : 𝓢 ⊢! □φ 🡒 (φ ⋏ (□φ 🡒 □□φ)) := C_trans (lemma_Grz₁ (φ := φ)) axiomGrz

protected noncomputable def axiomFour : 𝓢 ⊢! □φ 🡒 □□φ := C_of_CC $ C_trans lemma_axiomFour_axiomT and₂
noncomputable instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ Grz.axiomFour⟩

protected noncomputable def axiomT : 𝓢 ⊢! □φ 🡒 φ := C_trans lemma_axiomFour_axiomT and₁
noncomputable instance : HasAxiomT 𝓢 := ⟨fun _ ↦ Grz.axiomT⟩

noncomputable instance : Entailment.S4 𝓢 where

instance : HasAxiomDum 𝓢 := ⟨fun _ ↦ C_trans axiomGrz implyK⟩

end Grz

end LO.Modal.Entailment
end
