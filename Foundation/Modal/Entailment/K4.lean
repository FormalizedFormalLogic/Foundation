import Foundation.Modal.Entailment.K
import Foundation.Modal.Entailment.AxiomGeach

namespace LO.Modal.Entailment

open LO.Entailment Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.K4 𝓢]

lemma diaFour'! (h : 𝓢 ⊢ ◇◇φ) : 𝓢 ⊢ ◇φ := axiomFourDual ⨀ h

def imply_BoxBoxdot_Box: 𝓢 ⊢!  □⊡φ ➝ □φ := by
  exact C_trans distribute_box_and and₁
@[simp] lemma imply_boxboxdot_box : 𝓢 ⊢ □⊡φ ➝ □φ := ⟨imply_BoxBoxdot_Box⟩

def imply_Box_BoxBoxdot : 𝓢 ⊢! □φ ➝ □⊡φ := by
  exact C_trans (right_K_intro (C_id _) axiomFour) collect_box_and
@[simp] lemma imply_box_boxboxdot! : 𝓢 ⊢ □φ ➝ □⊡φ := ⟨imply_Box_BoxBoxdot⟩

def imply_Box_BoxBoxdot' (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □⊡φ := imply_Box_BoxBoxdot ⨀ h
def imply_Box_BoxBoxdot'! (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □⊡φ := ⟨imply_Box_BoxBoxdot' h.some⟩

def iff_Box_BoxBoxdot : 𝓢 ⊢! □φ ⭤ □⊡φ := by
  apply E_intro;
  . exact imply_Box_BoxBoxdot
  . exact imply_BoxBoxdot_Box;
@[simp] lemma iff_box_boxboxdot! : 𝓢 ⊢ □φ ⭤ □⊡φ := ⟨iff_Box_BoxBoxdot⟩

def iff_Box_BoxdotBox : 𝓢 ⊢! □φ ⭤ ⊡□φ := by
  apply E_intro;
  . exact C_trans (right_K_intro (C_id _) axiomFour) (C_id _)
  . exact and₁
@[simp] lemma iff_box_boxdotbox! : 𝓢 ⊢ □φ ⭤ ⊡□φ := ⟨iff_Box_BoxdotBox⟩

def iff_Boxdot_BoxdotBoxdot : 𝓢 ⊢! ⊡φ ⭤ ⊡⊡φ := by
  apply E_intro;
  . exact right_K_intro (C_id _) (C_trans boxdotBox (K_left iff_Box_BoxBoxdot));
  . exact and₁;
@[simp] lemma iff_boxdot_boxdotboxdot : 𝓢 ⊢ ⊡φ ⭤ ⊡⊡φ := ⟨iff_Boxdot_BoxdotBoxdot⟩

def boxdotAxiomFour : 𝓢 ⊢! ⊡φ ➝ ⊡⊡φ := K_left iff_Boxdot_BoxdotBoxdot
@[simp] lemma boxdot_axiomFour! : 𝓢 ⊢ ⊡φ ➝ ⊡⊡φ := ⟨boxdotAxiomFour⟩

lemma Context.multibox_2_in_context_to_box_finset {Γ : Finset F} (h : Γ.multibox 2 *⊢[𝓢] φ) : Γ.box *⊢[𝓢] φ := by
  apply FConj_DT.mp;
  refine C!_trans ?_ $ FConj_DT.mpr h;
  apply CFconjFconj!_of_provable;
  intro ξ hξ;
  obtain ⟨ξ, h, rfl⟩ := Finset.exists_multibox_of_mem_multibox hξ;
  apply axiomFour'!;
  apply Context.by_axm!
  simpa using h;

lemma Context.multibox_2_in_context_to_box {Γ : Set F} (h : Γ.multibox 2 *⊢[𝓢] φ) : Γ.box *⊢[𝓢] φ := by
  apply Context.provable_iff_finset.mpr;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff_finset.mp h;
  use Δ.premultibox 2 |>.box;
  constructor;
  . intro ψ hψ;
    simp at hψ;
    obtain ⟨ψ, hψ, rfl⟩ := hψ;
    have := hΔ₁ hψ;
    simpa;
  . apply Context.multibox_2_in_context_to_box_finset;
    apply Context.weakening! ?_ hΔ₂;
    intro ψ hψ;
    have := hΔ₁ hψ;
    simp at this;
    obtain ⟨ψ, hψ, rfl⟩ := this;
    simpa;

lemma Context.boxbox_in_context_to_box {Γ : Set F} (h : Γ.box.box *⊢[𝓢] φ) : Γ.box *⊢[𝓢] φ := by
  rw [(show Γ.box.box = Γ.multibox 2 by ext; simp)] at h;
  apply Context.multibox_2_in_context_to_box h;

end LO.Modal.Entailment
