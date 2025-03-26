import Foundation.Modal.Entailment.K

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Modal.Grz 𝓢]

namespace Grz

noncomputable def lemma_axiomFour_axiomT : 𝓢 ⊢ □φ ➝ (φ ⋏ (□φ ➝ □□φ)) := impTrans'' (lemma_Grz₁ (φ := φ)) axiomGrz

protected noncomputable def axiomFour : 𝓢 ⊢ □φ ➝ □□φ := ppq $ impTrans'' lemma_axiomFour_axiomT and₂
noncomputable instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ Grz.axiomFour⟩

protected noncomputable def axiomT : 𝓢 ⊢ □φ ➝ φ := impTrans'' lemma_axiomFour_axiomT and₁
noncomputable instance : HasAxiomT 𝓢 := ⟨fun _ ↦ Grz.axiomT⟩

end Grz

end LO.Entailment
