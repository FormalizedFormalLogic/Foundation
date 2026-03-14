module

public import Foundation.Modal.Entailment.K
public import Foundation.Modal.Entailment.AxiomGeach

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.K4 𝓢] {φ : F}

lemma diaFour'! (h : 𝓢 ⊢ ◇◇φ) : 𝓢 ⊢ ◇φ := axiomFourDual ⨀ h

def imply_BoxBoxdot_Box: 𝓢 ⊢!  □⊡φ 🡒 □φ := by
  exact C_trans distribute_box_and and₁
@[simp] lemma imply_boxboxdot_box : 𝓢 ⊢ □⊡φ 🡒 □φ := ⟨imply_BoxBoxdot_Box⟩

def imply_Box_BoxBoxdot : 𝓢 ⊢! □φ 🡒 □⊡φ := by
  exact C_trans (right_K_intro C_id axiomFour) collect_box_and
@[simp] lemma imply_box_boxboxdot! : 𝓢 ⊢ □φ 🡒 □⊡φ := ⟨imply_Box_BoxBoxdot⟩

def imply_Box_BoxBoxdot' (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □⊡φ := imply_Box_BoxBoxdot ⨀ h
def imply_Box_BoxBoxdot'! (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □⊡φ := ⟨imply_Box_BoxBoxdot' h.some⟩

def iff_Box_BoxBoxdot : 𝓢 ⊢! □φ 🡘 □⊡φ := by
  apply E_intro;
  . exact imply_Box_BoxBoxdot
  . exact imply_BoxBoxdot_Box;
@[simp] lemma iff_box_boxboxdot! : 𝓢 ⊢ □φ 🡘 □⊡φ := ⟨iff_Box_BoxBoxdot⟩

def iff_Box_BoxdotBox : 𝓢 ⊢! □φ 🡘 ⊡□φ := by
  apply E_intro;
  . exact C_trans (right_K_intro C_id axiomFour) C_id
  . exact and₁
@[simp] lemma iff_box_boxdotbox! : 𝓢 ⊢ □φ 🡘 ⊡□φ := ⟨iff_Box_BoxdotBox⟩

def iff_Boxdot_BoxdotBoxdot : 𝓢 ⊢! ⊡φ 🡘 ⊡⊡φ := by
  apply E_intro;
  . exact right_K_intro C_id (C_trans boxdotBox (K_left iff_Box_BoxBoxdot));
  . exact and₁;
@[simp] lemma iff_boxdot_boxdotboxdot : 𝓢 ⊢ ⊡φ 🡘 ⊡⊡φ := ⟨iff_Boxdot_BoxdotBoxdot⟩

def boxdotAxiomFour : 𝓢 ⊢! ⊡φ 🡒 ⊡⊡φ := K_left iff_Boxdot_BoxdotBoxdot
@[simp] lemma boxdot_axiomFour! : 𝓢 ⊢ ⊡φ 🡒 ⊡⊡φ := ⟨boxdotAxiomFour⟩

lemma Context.boxItr_2_in_context_to_box_finset {Γ : Finset F} (h : ↑(□^[2]'Γ) *⊢[𝓢] φ) : ↑(□'Γ) *⊢[𝓢] φ := by
  apply FConj_DT.mp;
  refine C!_trans ?_ $ FConj_DT.mpr h;
  apply CFconjFconj!_of_provable;
  intro ξ hξ;
  obtain ⟨ξ, h, rfl⟩ := Finset.LO.exists_of_mem_boxItr hξ;
  apply axiomFour'!;
  apply Context.by_axm!
  grind;

lemma Context.boxItr_2_in_context_to_box [InjectiveBox F] {Γ : Set F} (h : (□^[2]'Γ) *⊢[𝓢] φ) : (□'Γ) *⊢[𝓢] φ := by
  apply Context.provable_iff_finset.mpr;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff_finset.mp h;
  use □'(□⁻¹^[2]'Δ);
  constructor;
  . intro ψ hψ;
    obtain ⟨ξ, hξ, rfl⟩ := Finset.LO.exists_of_mem_box hψ;
    have : □^[2]ξ ∈ Δ := Finset.LO.mem_boxItr_of_mem_preboxItr hξ;
    have : □^[2]ξ ∈ □^[2]'Γ := hΔ₁ this;
    apply Set.LO.mem_boxItr_of_mem_boxItr this;
  . apply Context.boxItr_2_in_context_to_box_finset;
    apply Context.weakening! ?_ hΔ₂;
    intro ψ hψ;
    obtain ⟨ψ, hψ, rfl⟩ := hΔ₁ hψ;
    apply Finset.LO.mem_boxItr_preboxItr_of_mem_of_mem_boxItr;
    simpa;

lemma Context.boxbox_in_context_to_box [InjectiveBox F] {Γ : Set F} (h : (□'□'Γ) *⊢[𝓢] φ) : (□'Γ) *⊢[𝓢] φ := by
  apply Context.boxItr_2_in_context_to_box;
  suffices (□'□'Γ) = (□^[2]'Γ) by rwa [this] at h;
  ext;
  simp [Set.LO.boxItr];

end LO.Modal.Entailment
end
