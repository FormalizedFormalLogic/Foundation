import Foundation.Modal.System.KT
import Foundation.Modal.System.K4

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S} [System.S4 𝓢]

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

end LO.System
