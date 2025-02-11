import Foundation.Modal.Entailment.KT
import Foundation.Modal.Entailment.K4

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.S4 𝓢]

def iff_box_boxdot : 𝓢 ⊢ □φ ⭤ ⊡φ := by
  apply iffIntro;
  . exact implyRightAnd (axiomT) (impId _);
  . exact and₂;
@[simp] lemma iff_box_boxdot! : 𝓢 ⊢! □φ ⭤ ⊡φ := ⟨iff_box_boxdot⟩

def iff_dia_diadot : 𝓢 ⊢ ◇φ ⭤ ⟐φ := by
  apply iffIntro;
  . exact or₂;
  . exact or₃'' diaTc (impId _)
@[simp] lemma iff_dia_diadot! : 𝓢 ⊢! ◇φ ⭤ ⟐φ := ⟨iff_dia_diadot⟩

end LO.Entailment
