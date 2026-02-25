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
  obtain ⟨M, _, _, _, _, hs⟩ := GL.Kripke.iff_unprovable_exists_finite_rooted_model.mp h;


  apply GL.Kripke.iff_unprovable_exists_finite_rooted_model.mpr;
  use (M.extendRoot 1), inferInstance, inferInstance, inferInstance, inferInstance;

  have hs : Satisfies M M.root (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies];
  replace hs := Model.extendRoot.modal_equivalence_original_world (n := 1) (x := M.root.1) |>.mpr hs;
  have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs;
  have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;

  apply Satisfies.not_imp_def.mpr;
  constructor;
  . have hs : Satisfies M M.root (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies];
    replace hs := Model.extendRoot.modal_equivalence_original_world (n := 1) (x := M.root.1) |>.mpr hs;
    have ⟨hs₁₂, hs₃⟩ := Satisfies.and_def.mp hs;
    have ⟨hs₁, hs₂⟩ := Satisfies.and_def.mp hs₁₂;
    intro x hx;
    obtain ⟨x₀, rfl⟩ := Frame.extendRoot.eq_original_of_neq_extendRoot_root₁ x (by grind);
    by_cases e : x₀ = M.root;
    . exact e ▸ hs₁;
    . apply hs₂;
      grind;
  . apply Satisfies.box_def.not.mpr;
    push_neg;
    use (Sum.inr M.root);
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
