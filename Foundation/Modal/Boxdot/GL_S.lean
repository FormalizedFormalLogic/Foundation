import Foundation.ProvabilityLogic.S.Completeness

namespace LO

namespace Modal.Logic

open Kripke Formula.Kripke

variable {A : Formula _}

lemma iff_provable_rflSubformula_GL_provable_S : (A.rflSubformula.conj ➝ A) ∈ Logic.GL ↔ A ∈ Logic.S := ProvabilityLogic.GL_S_TFAE (T := 𝐈𝚺₁) |>.out 0 1

lemma iff_provable_boxdot_GL_provable_boxdot_S : Aᵇ ∈ Logic.GL ↔ Aᵇ ∈ Logic.S := by
  constructor;
  . apply Logic.GL_subset_S;
  . intro h;
    replace h := iff_provable_rflSubformula_GL_provable_S.mpr h;
    replace h := Hilbert.GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree.mp h;
    apply Hilbert.GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree.mpr;
    intro M r _;
    obtain ⟨i, hi⟩ := Kripke.Model.extendRoot.inr_satisfies_axiomT_set (M := M) (Γ := Aᵇ.subformulas.prebox)
    let M₁ := M.extendRoot r ⟨Aᵇ.subformulas.prebox.card + 1, by omega⟩;
    let i₁ : M₁.World := Sum.inl i;
    refine Model.extendRoot.inl_satisfies_boxdot_iff.mpr
      $ Model.pointGenerate.modal_equivalent_at_root (r := i₁) |>.mp
      $ @h (M₁↾i₁) Model.pointGenerate.root ?_ ?_;
    . apply Frame.isFiniteTree_iff _ _ |>.mpr
      constructor;
      . apply Frame.pointGenerate.isFinite (finite := Frame.extendRoot.isFinite)
      . apply Frame.isTree_iff _ _ |>.mpr;
        refine ⟨?_, ?_, ?_⟩;
        . apply Frame.pointGenerate.instIsRooted;
        . apply Frame.pointGenerate.isAsymm (assym := Frame.extendRoot.isAsymm);
        . apply Frame.pointGenerate.isTrans (trans := Frame.extendRoot.isTrans);
    . apply @Model.pointGenerate.modal_equivalent_at_root (r := i₁) |>.mpr
      apply Satisfies.fconj_def.mpr;
      intro B hB;
      apply Satisfies.fconj_def.mp hi;
      simp only [Finset.mem_image, Finset.eq_prebox_premultibox_one, Finset.mem_preimage, Function.iterate_one] at hB ⊢;
      obtain ⟨C, hC, rfl⟩ := hB;
      use C;

end Modal.Logic


end LO
