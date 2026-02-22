module

public import Foundation.Modal.Kripke.Logic.GL.Completeness
public import Foundation.Modal.Kripke.ExtendRoot

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Kripke
open Formula.Kripke
open Relation

open Model in
lemma imply_boxdot_plain_of_imply_box_box : Modal.GL ⊢ □φ ➝ □ψ → Modal.GL ⊢ ⊡φ ➝ ψ := by
  contrapose;

  intro h;
  obtain ⟨M, _, _, _, r, hs⟩ := GL.Kripke.iff_unprovable_exists_finite_rooted_model.mp h;

  let M₀ := M.extendRoot r 1;
  let r₀ : M₀.Root := Frame.extendRoot.root M.toFrame 1;

  apply GL.Kripke.iff_unprovable_exists_finite_rooted_model.mpr;
  use M₀, inferInstance, inferInstance, inferInstance, r₀;

  have hs : Satisfies M r (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies];
  replace hs := @Model.extendRoot.modal_equivalence_original_world (M := M) (r := r) (n := 1) r (⊡φ ⋏ ∼ψ) |>.mpr hs;
  have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs;
  have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;

  apply Satisfies.not_imp_def.mpr;
  constructor;
  . have hs : Satisfies M r (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies];
    replace hs := @Model.extendRoot.modal_equivalence_original_world (M := M) (r := r) (n := 1) r (⊡φ ⋏ ∼ψ) |>.mpr hs;
    have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs;
    have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;

    intro x hx;
    rcases Frame.extendRoot.not_root_of_from_root₁ (F := M.toFrame) (x := x) r hx with (rfl | hr);
    . assumption;
    . apply hs₂; exact hr;
  . apply Satisfies.box_def.not.mpr;
    push_neg;
    use (Sum.inr r);
    constructor;
    . grind;
    . assumption;

theorem unnecessitation! : Modal.GL ⊢ □φ → Modal.GL ⊢ φ := by
  intro h;
  have : Modal.GL ⊢ □⊤ ➝ □φ := C!_of_conseq! (ψ := □⊤) h;
  have : Modal.GL ⊢ ⊡⊤ ➝ φ := imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : Entailment.Unnecessitation Modal.GL := ⟨λ h => unnecessitation! ⟨h⟩ |>.some⟩

end LO.Modal
end
