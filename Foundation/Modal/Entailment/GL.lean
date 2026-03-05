module

public import Foundation.Modal.Entailment.K4

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.GL 𝓢]

def gödel2 : 𝓢 ⊢! (∼(□⊥) ⭤ ∼(□(∼(□⊥))) : F) := by
  apply ENN_of_E;
  apply E_intro;
  . apply implyBoxDistribute';
    exact efq;
  . exact C_trans (by
      apply implyBoxDistribute';
      exact K_left negEquiv;
    ) axiomL;
lemma gödel2! : 𝓢 ⊢ (∼(□⊥) ⭤ ∼(□(∼(□⊥))) : F) := ⟨gödel2⟩

def gödel2'.mp : 𝓢 ⊢! (∼(□⊥) : F) → 𝓢 ⊢! ∼(□(∼(□⊥)) : F) := by intro h; exact (K_left gödel2) ⨀ h;
def gödel2'.mpr : 𝓢 ⊢! ∼(□(∼(□⊥)) : F) → 𝓢 ⊢! (∼(□⊥) : F) := by intro h; exact (K_right gödel2) ⨀ h;
lemma gödel2'! : 𝓢 ⊢ (∼(□⊥) : F) ↔ 𝓢 ⊢ ∼(□(∼(□⊥)) : F) := ⟨λ ⟨h⟩ ↦ ⟨gödel2'.mp h⟩, λ ⟨h⟩ ↦ ⟨gödel2'.mpr h⟩⟩


namespace GL

variable {φ ψ : F}

instance : HasAxiomZ 𝓢 := ⟨C_trans axiomL implyK⟩

protected def axiomFour : 𝓢 ⊢! Axioms.Four φ := by
  dsimp [Axioms.Four];
  have : 𝓢 ⊢! φ ➝ (⊡□φ ➝ ⊡φ) := by
    apply deduct';
    apply deduct;
    exact K_intro (FiniteContext.byAxm) (K_left (ψ := □□φ) $ FiniteContext.byAxm);
  have : 𝓢 ⊢! φ ➝ (□⊡φ ➝ ⊡φ) := C_trans this (CCC_of_C_left BoxBoxdot_BoxDotbox);
  exact C_trans (C_trans (implyBoxDistribute' this) axiomL) (implyBoxDistribute' $ and₂);
instance : HasAxiomFour 𝓢 := ⟨GL.axiomFour⟩
instance : Entailment.K4 𝓢 where

protected def axiomHen : 𝓢 ⊢! Axioms.Hen φ := C_trans (implyBoxDistribute' and₁) axiomL
instance : HasAxiomHen 𝓢 := ⟨GL.axiomHen⟩

protected def axiomZ : 𝓢 ⊢! Axioms.Z φ := C_trans axiomL implyK
instance : HasAxiomZ 𝓢 := ⟨GL.axiomZ⟩

end GL

noncomputable def lem_boxdot_Grz_of_L : 𝓢 ⊢! (⊡(⊡(φ ➝ ⊡φ) ➝ φ)) ➝ (□(φ ➝ ⊡φ) ➝ φ) := by
  have : 𝓢 ⊢! (□(φ ➝ ⊡φ) ⋏ ∼φ) ➝ ⊡(φ ➝ ⊡φ) := by
    apply deduct';
    apply K_intro;
    . exact (of CNC) ⨀ and₂;
    . exact (of C_id) ⨀ and₁;
  have : 𝓢 ⊢! ∼⊡(φ ➝ ⊡φ) ➝ (∼□(φ ➝ ⊡φ) ⋎ φ) := C_trans (contra this) $ C_trans CNKANN (CAA_of_C_right dne);
  have : 𝓢 ⊢! (∼⊡(φ ➝ ⊡φ) ⋎ φ) ➝ (∼□(φ ➝ ⊡φ) ⋎ φ) := left_A_intro this or₂;
  have : 𝓢 ⊢! ∼⊡(φ ➝ ⊡φ) ⋎ φ ➝ □(φ ➝ ⊡φ) ➝ φ := C_trans this CANC;
  have : 𝓢 ⊢! (⊡(φ ➝ ⊡φ) ➝ φ) ➝ (□(φ ➝ ⊡φ) ➝ φ) := C_trans CCAN this;
  exact C_trans boxdotAxiomT this;

noncomputable def boxdot_Grz_of_L : 𝓢 ⊢! ⊡(⊡(φ ➝ ⊡φ) ➝ φ) ➝ φ := by
  have : 𝓢 ⊢! □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □⊡(φ ➝ ⊡φ) ➝ □φ := axiomK;
  have : 𝓢 ⊢! □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(φ ➝ ⊡φ) ➝ □φ := C_trans this $ CCC_of_C_left $ imply_Box_BoxBoxdot;
  have : 𝓢 ⊢! □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(φ ➝ ⊡φ) ➝ (φ ➝ ⊡φ) := by
    apply deduct'; apply deduct; apply deduct;
    exact K_intro FiniteContext.byAxm $ (of this) ⨀ (FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
  have : 𝓢 ⊢! □□(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(□(φ ➝ ⊡φ) ➝ (φ ➝ ⊡φ)) := implyBoxDistribute' this;
  have : 𝓢 ⊢! □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(□(φ ➝ ⊡φ) ➝ (φ ➝ ⊡φ)) := C_trans axiomFour this;
  have : 𝓢 ⊢! □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(φ ➝ ⊡φ) := C_trans this axiomL;
  have : 𝓢 ⊢! ⊡(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(φ ➝ ⊡φ) := C_trans boxdotBox this;
  exact mdp₁ lem_boxdot_Grz_of_L this;
@[simp] lemma boxdot_Grz_of_L! : 𝓢 ⊢ ⊡(⊡(φ ➝ ⊡φ) ➝ φ) ➝ φ := ⟨boxdot_Grz_of_L⟩


def imply_boxdot_boxdot_of_imply_boxdot_plain (h : 𝓢 ⊢! ⊡φ ➝ ψ) : 𝓢 ⊢! ⊡φ ➝ ⊡ψ := by
  have : 𝓢 ⊢! □⊡φ ➝ □ψ := implyBoxDistribute' h;
  have : 𝓢 ⊢! □φ ➝ □ψ := C_trans imply_Box_BoxBoxdot this;
  have : 𝓢 ⊢! ⊡φ ➝ □ψ := C_trans boxdotBox this;
  exact right_K_intro h this;
lemma imply_boxdot_boxdot_of_imply_boxdot_plain! (h : 𝓢 ⊢ ⊡φ ➝ ψ) : 𝓢 ⊢ ⊡φ ➝ ⊡ψ := ⟨imply_boxdot_boxdot_of_imply_boxdot_plain h.some⟩


def imply_boxdot_axiomT_of_imply_boxdot_boxdot (h : 𝓢 ⊢! ⊡φ ➝ ⊡ψ) : 𝓢 ⊢! ⊡φ ➝ (□ψ ➝ ψ) := by
  apply deduct';
  apply deduct;
  have : [□ψ, ⊡φ] ⊢[𝓢]! ⊡ψ := (FiniteContext.of h) ⨀ (FiniteContext.byAxm);
  exact K_left this;
lemma imply_boxdot_axiomT_of_imply_boxdot_boxdot! (h : 𝓢 ⊢ ⊡φ ➝ ⊡ψ) : 𝓢 ⊢ ⊡φ ➝ (□ψ ➝ ψ) := ⟨imply_boxdot_axiomT_of_imply_boxdot_boxdot h.some⟩


def imply_box_box_of_imply_boxdot_axiomT (h : 𝓢 ⊢! ⊡φ ➝ (□ψ ➝ ψ)) : 𝓢 ⊢! □φ ➝ □ψ := by
  have : 𝓢 ⊢! □⊡φ ➝ □(□ψ ➝ ψ) := implyBoxDistribute' h;
  have : 𝓢 ⊢! □⊡φ ➝ □ψ := C_trans this axiomL;
  exact C_trans imply_Box_BoxBoxdot this;
lemma imply_box_box_of_imply_boxdot_axiomT! (h : 𝓢 ⊢ ⊡φ ➝ (□ψ ➝ ψ)) : 𝓢 ⊢ □φ ➝ □ψ := ⟨imply_box_box_of_imply_boxdot_axiomT h.some⟩


lemma imply_box_box_of_imply_boxdot_plain! (h : 𝓢 ⊢ ⊡φ ➝ ψ) : 𝓢 ⊢ □φ ➝ □ψ := by
  exact imply_box_box_of_imply_boxdot_axiomT! $ imply_boxdot_axiomT_of_imply_boxdot_boxdot! $ imply_boxdot_boxdot_of_imply_boxdot_plain! h

end LO.Modal.Entailment
end
