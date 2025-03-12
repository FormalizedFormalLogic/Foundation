import Foundation.Modal.Kripke.Hilbert.GL.Tree
import Foundation.Modal.Kripke.SimpleExtension

namespace LO.Modal

open Entailment
open Kripke
open Formula.Kripke

namespace Hilbert.GL

open Model in
lemma imply_boxdot_plain_of_imply_box_box : Hilbert.GL ⊢! □φ ➝ □ψ → Hilbert.GL ⊢! ⊡φ ➝ ψ := by
  contrapose;
  intro h;
  have := Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h;
  obtain ⟨M, r, M_tree, hs⟩ := this;

  have hs : Satisfies M r (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies, Semantics.Realize];
  have := @Model.extendRoot.modal_equivalence_original_world (M := M) (r := r) inferInstance r (⊡φ ⋏ ∼ψ) |>.mp hs;
  have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs;
  have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;

  let M₀ := M.extendRoot r;
  let r₀ : M₀.World := extendRoot.root (r := r)

  have hbp : Satisfies M₀ r₀ (□φ) := by
    intro x hx;
    rcases Frame.extendRoot.through_original_root (F := M.toFrame) (x := x) hx with (rfl | hr);
    . sorry;
      -- assumption;
    . sorry;
      -- apply hs₂;
      -- exact hr;
  have hbq : ¬(Satisfies M₀ r₀ (□ψ)) := by
    apply Satisfies.box_def.not.mpr;
    push_neg;
    use (Sum.inr r);
    constructor;
    . sorry;
      -- apply M↧.toRootedFrame.root_rooted M.root;
      -- simp [FiniteTransitiveTreeModel.SimpleExtension, Kripke.FiniteTransitiveTree.SimpleExtension]; -- TODO: extract lemma
    . sorry;
      -- assumption;

  apply Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mpr;
  use M₀, r₀;
  tauto;

theorem unnecessitation! : Hilbert.GL ⊢! □φ → Hilbert.GL ⊢! φ := by
  intro h;
  have : Hilbert.GL ⊢! □⊤ ➝ □φ := imply₁'! (ψ := □⊤) h;
  have : Hilbert.GL ⊢! ⊡⊤ ➝ φ := imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : Entailment.Unnecessitation Hilbert.GL := ⟨λ h => unnecessitation! ⟨h⟩ |>.some⟩

end Hilbert.GL

end LO.Modal
