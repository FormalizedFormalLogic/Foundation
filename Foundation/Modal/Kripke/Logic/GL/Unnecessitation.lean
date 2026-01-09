module
import Foundation.Modal.Kripke.Logic.GL.Tree
import Foundation.Modal.Kripke.ExtendRoot

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Kripke
open Formula.Kripke
open Relation

open Model in
lemma imply_boxdot_plain_of_imply_box_box : Modal.GL ⊢ □φ ➝ □ψ → Modal.GL ⊢ ⊡φ ➝ ψ := by
  contrapose;
  intro h;
  have := GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h;
  obtain ⟨M, r, M_tree, hs⟩ := this;

  let M₀ := M.extendRoot 1;
  let r₀ : M₀.World := extendRoot.root;

  have hs : Satisfies M r (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies];
  replace hs := @Model.extendRoot.modal_equivalence_original_world (M := M) (r := r) (n := 1) inferInstance r (⊡φ ⋏ ∼ψ) |>.mp hs;
  have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs;
  have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;

  have hbp : Satisfies M₀ r₀ (□φ) := by
    intro x hx;
    rcases Frame.extendRoot.not_root_of_from_root₁ (F := M.toFrame) (x := x) hx with (rfl | hr);
    . tauto;
    . apply hs₂; exact hr;
  have hbq : ¬(Satisfies M₀ r₀ (□ψ)) := by
    apply Satisfies.box_def.not.mpr;
    push_neg;
    use (Sum.inr r);
    constructor;
    . exact @Frame.IsRootedBy.root_generates (F := M₀.toFrame) (r := r₀) (Frame.extendRoot.instIsRooted) (Sum.inr r) (by tauto) |>.unwrap;
    . assumption;

  apply GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mpr;
  use M₀, r₀;
  refine ⟨?_, ?_⟩;
  . exact {};
  . tauto;

theorem unnecessitation! : Modal.GL ⊢ □φ → Modal.GL ⊢ φ := by
  intro h;
  have : Modal.GL ⊢ □⊤ ➝ □φ := C!_of_conseq! (ψ := □⊤) h;
  have : Modal.GL ⊢ ⊡⊤ ➝ φ := imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : Entailment.Unnecessitation Modal.GL := ⟨λ h => unnecessitation! ⟨h⟩ |>.some⟩

end LO.Modal
