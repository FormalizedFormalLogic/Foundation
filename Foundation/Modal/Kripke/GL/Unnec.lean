import Foundation.Modal.Kripke.GL.Tree

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S}
variable [System.GL 𝓢]

def imply_boxdot_boxdot_of_imply_boxdot_plain (h : 𝓢 ⊢ ⊡φ ➝ ψ) : 𝓢 ⊢ ⊡φ ➝ ⊡ψ := by
  have : 𝓢 ⊢ □⊡φ ➝ □ψ := implyBoxDistribute' h;
  have : 𝓢 ⊢ □φ ➝ □ψ := impTrans'' imply_Box_BoxBoxdot this;
  have : 𝓢 ⊢ ⊡φ ➝ □ψ := impTrans'' boxdotBox this;
  exact implyRightAnd h this;
lemma imply_boxdot_boxdot_of_imply_boxdot_plain! (h : 𝓢 ⊢! ⊡φ ➝ ψ) : 𝓢 ⊢! ⊡φ ➝ ⊡ψ := ⟨imply_boxdot_boxdot_of_imply_boxdot_plain h.some⟩

def imply_boxdot_axiomT_of_imply_boxdot_boxdot (h : 𝓢 ⊢ ⊡φ ➝ ⊡ψ) : 𝓢 ⊢ ⊡φ ➝ (□ψ ➝ ψ) := by
  apply deduct';
  apply deduct;
  have : [□ψ, ⊡φ] ⊢[𝓢] ⊡ψ := (FiniteContext.of h) ⨀ (FiniteContext.byAxm);
  exact and₁' this;
lemma imply_boxdot_axiomT_of_imply_boxdot_boxdot! (h : 𝓢 ⊢! ⊡φ ➝ ⊡ψ) : 𝓢 ⊢! ⊡φ ➝ (□ψ ➝ ψ) := ⟨imply_boxdot_axiomT_of_imply_boxdot_boxdot h.some⟩

def imply_box_box_of_imply_boxdot_axiomT (h : 𝓢 ⊢ ⊡φ ➝ (□ψ ➝ ψ)) : 𝓢 ⊢ □φ ➝ □ψ := by
  have : 𝓢 ⊢ □⊡φ ➝ □(□ψ ➝ ψ) := implyBoxDistribute' h;
  have : 𝓢 ⊢ □⊡φ ➝ □ψ := impTrans'' this axiomL;
  exact impTrans'' imply_Box_BoxBoxdot this;
lemma imply_box_box_of_imply_boxdot_axiomT! (h : 𝓢 ⊢! ⊡φ ➝ (□ψ ➝ ψ)) : 𝓢 ⊢! □φ ➝ □ψ := ⟨imply_box_box_of_imply_boxdot_axiomT h.some⟩

lemma imply_box_box_of_imply_boxdot_plain! (h : 𝓢 ⊢! ⊡φ ➝ ψ) : 𝓢 ⊢! □φ ➝ □ψ := by
  exact imply_box_box_of_imply_boxdot_axiomT! $ imply_boxdot_axiomT_of_imply_boxdot_boxdot! $ imply_boxdot_boxdot_of_imply_boxdot_plain! h

end LO.System


namespace LO.Modal.Hilbert.GL

open System
open Formula.Kripke
open Kripke
open Kripke.FiniteTransitiveTreeModel

variable {φ ψ : Formula ℕ}

/-
  逆は以下を順に辿って構文論的に証明できる．
  - `System.imply_boxdot_boxdot_of_imply_boxdot_plain`
  - `System.imply_boxdot_axiomT_of_imply_boxdot_boxdot`
  - `System.imply_box_box_of_imply_boxdot_axiomT`
-/
lemma imply_boxdot_plain_of_imply_box_box : (Hilbert.GL ℕ) ⊢! □φ ➝ □ψ → (Hilbert.GL ℕ) ⊢! ⊡φ ➝ ψ := by
  contrapose;
  intro h;
  have := Kripke.unprovable_iff_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mp h;
  obtain ⟨M, hs⟩ := this;

  have hs : Satisfies M.toModel M.root (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies, Semantics.Realize];
  replace hs := @SimpleExtension.modal_equivalence_original_world M M.root (⊡φ ⋏ ∼ψ) |>.mp hs;
  have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs;
  have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;

  have hbp : Satisfies M↧.toModel (M↧.root) (□φ) := by
    intro x hx;
    rcases @Kripke.FiniteTransitiveTree.SimpleExtension.through_original_root M.toFiniteTransitiveTree x hx with (rfl | hr);
    . assumption;
    . apply hs₂;
      exact hr;
  have hbq : ¬(Satisfies M↧.toModel (M↧.root) (□ψ)) := by
    apply Satisfies.box_def.not.mpr;
    push_neg;
    use M.root;
    constructor;
    . apply M↧.toRootedFrame.root_rooted M.root;
      simp [SimpleExtension, Kripke.FiniteTransitiveTree.SimpleExtension]; -- TODO: extract lemma
    . assumption;

  apply Kripke.unprovable_iff_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mpr;
  use M↧;
  exact _root_.not_imp.mpr ⟨hbp, hbq⟩;

theorem unnecessitation! : (Hilbert.GL ℕ) ⊢! □φ → (Hilbert.GL ℕ) ⊢! φ := by
  intro h;
  have : (Hilbert.GL ℕ) ⊢! □⊤ ➝ □φ := imply₁'! (ψ := □⊤) h;
  have : (Hilbert.GL ℕ) ⊢! ⊡⊤ ➝ φ := imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : System.Unnecessitation (Hilbert.GL ℕ) := ⟨λ h => unnecessitation! ⟨h⟩ |>.some⟩

end LO.Modal.Hilbert.GL
