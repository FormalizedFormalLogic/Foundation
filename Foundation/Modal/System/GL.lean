import Foundation.Modal.System.K4

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S} [System.GL 𝓢]

def goedel2 : 𝓢 ⊢ (∼(□⊥) ⭤ ∼(□(∼(□⊥))) : F) := by
  apply negReplaceIff';
  apply iffIntro;
  . apply implyBoxDistribute';
    exact efq;
  . exact impTrans'' (by
      apply implyBoxDistribute';
      exact and₁' neg_equiv;
    ) axiomL;
lemma goedel2! : 𝓢 ⊢! (∼(□⊥) ⭤ ∼(□(∼(□⊥))) : F) := ⟨goedel2⟩

def goedel2'.mp : 𝓢 ⊢ (∼(□⊥) : F) → 𝓢 ⊢ ∼(□(∼(□⊥)) : F) := by intro h; exact (and₁' goedel2) ⨀ h;
def goedel2'.mpr : 𝓢 ⊢ ∼(□(∼(□⊥)) : F) → 𝓢 ⊢ (∼(□⊥) : F) := by intro h; exact (and₂' goedel2) ⨀ h;
lemma goedel2'! : 𝓢 ⊢! (∼(□⊥) : F) ↔ 𝓢 ⊢! ∼(□(∼(□⊥)) : F) := ⟨λ ⟨h⟩ ↦ ⟨goedel2'.mp h⟩, λ ⟨h⟩ ↦ ⟨goedel2'.mpr h⟩⟩


namespace GL

protected def axiomFour : 𝓢 ⊢ Axioms.Four φ := by
  dsimp [Axioms.Four];
  have : 𝓢 ⊢ φ ➝ (⊡□φ ➝ ⊡φ) := by
    apply deduct';
    apply deduct;
    exact and₃' (FiniteContext.byAxm) (and₁' (ψ := □□φ) $ FiniteContext.byAxm);
  have : 𝓢 ⊢ φ ➝ (□⊡φ ➝ ⊡φ) := impTrans'' this (implyLeftReplace BoxBoxdot_BoxDotbox);
  exact impTrans'' (impTrans'' (implyBoxDistribute' this) axiomL) (implyBoxDistribute' $ and₂);
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ GL.axiomFour⟩
instance : System.K4 𝓢 where

protected def axiomH : 𝓢 ⊢ Axioms.H φ := impTrans'' (implyBoxDistribute' and₁) axiomL
instance : HasAxiomH 𝓢 := ⟨fun _ ↦ GL.axiomH⟩

end GL

private noncomputable def lem_boxdot_Grz_of_L : 𝓢 ⊢ (⊡(⊡(φ ➝ ⊡φ) ➝ φ)) ➝ (□(φ ➝ ⊡φ) ➝ φ) := by
  have : 𝓢 ⊢ (□(φ ➝ ⊡φ) ⋏ ∼φ) ➝ ⊡(φ ➝ ⊡φ) := by
    apply deduct';
    apply and₃';
    . exact (of efq_imply_not₁) ⨀ and₂;
    . exact (of (impId _)) ⨀ and₁;
  have : 𝓢 ⊢ ∼⊡(φ ➝ ⊡φ) ➝ (∼□(φ ➝ ⊡φ) ⋎ φ) := impTrans'' (contra₀' this) $ impTrans'' demorgan₄ (orReplaceRight dne);
  have : 𝓢 ⊢ (∼⊡(φ ➝ ⊡φ) ⋎ φ) ➝ (∼□(φ ➝ ⊡φ) ⋎ φ) := or₃'' this or₂;
  have : 𝓢 ⊢ ∼⊡(φ ➝ ⊡φ) ⋎ φ ➝ □(φ ➝ ⊡φ) ➝ φ := impTrans'' this implyOfNotOr;
  have : 𝓢 ⊢ (⊡(φ ➝ ⊡φ) ➝ φ) ➝ (□(φ ➝ ⊡φ) ➝ φ) := impTrans'' NotOrOfImply this;
  exact impTrans'' boxdotAxiomT this;

noncomputable def boxdot_Grz_of_L : 𝓢 ⊢ ⊡(⊡(φ ➝ ⊡φ) ➝ φ) ➝ φ := by
  have : 𝓢 ⊢ □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □⊡(φ ➝ ⊡φ) ➝ □φ := axiomK;
  have : 𝓢 ⊢ □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(φ ➝ ⊡φ) ➝ □φ := impTrans'' this $ implyLeftReplace $ imply_Box_BoxBoxdot;
  have : 𝓢 ⊢ □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(φ ➝ ⊡φ) ➝ (φ ➝ ⊡φ) := by
    apply deduct'; apply deduct; apply deduct;
    exact and₃' FiniteContext.byAxm $ (of this) ⨀ (FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
  have : 𝓢 ⊢ □□(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(□(φ ➝ ⊡φ) ➝ (φ ➝ ⊡φ)) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(□(φ ➝ ⊡φ) ➝ (φ ➝ ⊡φ)) := impTrans'' axiomFour this;
  have : 𝓢 ⊢ □(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(φ ➝ ⊡φ) := impTrans'' this axiomL;
  have : 𝓢 ⊢ ⊡(⊡(φ ➝ ⊡φ) ➝ φ) ➝ □(φ ➝ ⊡φ) := impTrans'' boxdotBox this;
  exact mdp₁ lem_boxdot_Grz_of_L this;
@[simp] lemma boxdot_Grz_of_L! : 𝓢 ⊢! ⊡(⊡(φ ➝ ⊡φ) ➝ φ) ➝ φ := ⟨boxdot_Grz_of_L⟩

end LO.System
