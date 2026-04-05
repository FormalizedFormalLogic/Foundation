module

public import Foundation.Modal.Entailment.KT
public import Foundation.Modal.Entailment.K4

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.S4 𝓢]

def iff_box_boxdot : 𝓢 ⊢! □φ 🡘 ⊡φ := by
  apply E_intro;
  . exact right_K_intro (axiomT) C_id;
  . exact and₂;
@[simp] lemma iff_box_boxdot! : 𝓢 ⊢ □φ 🡘 ⊡φ := ⟨iff_box_boxdot⟩

def iff_dia_diadot : 𝓢 ⊢! ◇φ 🡘 ⟐φ := by
  apply E_intro;
  . exact or₂;
  . exact left_A_intro diaTc C_id
@[simp] lemma iff_dia_diadot! : 𝓢 ⊢ ◇φ 🡘 ⟐φ := ⟨iff_dia_diadot⟩

end LO.Modal.Entailment
end
