import Foundation.Modal.Entailment.K

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.K4 𝓢]

def imply_BoxBoxdot_Box: 𝓢 ⊢  □⊡φ ➝ □φ := by
  exact impTrans'' distribute_box_and and₁
@[simp] lemma imply_boxboxdot_box : 𝓢 ⊢! □⊡φ ➝ □φ := ⟨imply_BoxBoxdot_Box⟩

def imply_Box_BoxBoxdot : 𝓢 ⊢ □φ ➝ □⊡φ := by
  exact impTrans'' (implyRightAnd (impId _) axiomFour) collect_box_and
@[simp] lemma imply_box_boxboxdot! : 𝓢 ⊢! □φ ➝ □⊡φ := ⟨imply_Box_BoxBoxdot⟩

def imply_Box_BoxBoxdot' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □⊡φ := imply_Box_BoxBoxdot ⨀ h
def imply_Box_BoxBoxdot'! (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □⊡φ := ⟨imply_Box_BoxBoxdot' h.some⟩

def iff_Box_BoxBoxdot : 𝓢 ⊢ □φ ⭤ □⊡φ := by
  apply iffIntro;
  . exact imply_Box_BoxBoxdot
  . exact imply_BoxBoxdot_Box;
@[simp] lemma iff_box_boxboxdot! : 𝓢 ⊢! □φ ⭤ □⊡φ := ⟨iff_Box_BoxBoxdot⟩

def iff_Box_BoxdotBox : 𝓢 ⊢ □φ ⭤ ⊡□φ := by
  apply iffIntro;
  . exact impTrans'' (implyRightAnd (impId _) axiomFour) (impId _)
  . exact and₁
@[simp] lemma iff_box_boxdotbox! : 𝓢 ⊢! □φ ⭤ ⊡□φ := ⟨iff_Box_BoxdotBox⟩

def iff_Boxdot_BoxdotBoxdot : 𝓢 ⊢ ⊡φ ⭤ ⊡⊡φ := by
  apply iffIntro;
  . exact implyRightAnd (impId _) (impTrans'' boxdotBox (and₁' iff_Box_BoxBoxdot));
  . exact and₁;
@[simp] lemma iff_boxdot_boxdotboxdot : 𝓢 ⊢! ⊡φ ⭤ ⊡⊡φ := ⟨iff_Boxdot_BoxdotBoxdot⟩

def boxdotAxiomFour : 𝓢 ⊢ ⊡φ ➝ ⊡⊡φ := and₁' iff_Boxdot_BoxdotBoxdot
@[simp] lemma boxdot_axiomFour! : 𝓢 ⊢! ⊡φ ➝ ⊡⊡φ := ⟨boxdotAxiomFour⟩

end LO.Entailment
