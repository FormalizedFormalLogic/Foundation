import Foundation.ProvabilityLogic.S.Completeness

namespace LO

namespace Modal.Logic

open Kripke Formula.Kripke

variable {φ : Formula _}

lemma iff_provable_rflSubformula_GL_provable_S : Logic.GL ⊢! (φ.rflSubformula.conj ➝ φ) ↔ Logic.S ⊢! φ := ProvabilityLogic.GL_S_TFAE (T := 𝐈𝚺₁) |>.out 0 1

lemma iff_provable_boxdot_GL_provable_boxdot_S : Logic.GL ⊢! φᵇ ↔ Logic.S ⊢! φᵇ := by
  constructor;
  . apply Entailment.WeakerThan.wk;
    infer_instance;
  . intro h;
    apply Logic.GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree.mpr;
    replace h := iff_provable_rflSubformula_GL_provable_S.mpr h;
    replace h := Logic.GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree.mp h;
    intro M r _;
    obtain ⟨i, hi⟩ := Kripke.Model.extendRoot.inr_satisfies_axiomT_set (M := M) (Γ := φᵇ.subformulas.prebox);
    let M₁ := M.extendRoot r ⟨φᵇ.subformulas.prebox.card + 1, by omega⟩;
    let i₁ : M₁.World := Sum.inl i;
    refine Model.extendRoot.inl_satisfies_boxdot_iff.mpr
      $ Model.pointGenerate.modal_equivalent_at_root (r := i₁) |>.mp
      $ @h (M₁↾i₁) Model.pointGenerate.root ?_ ?_;
    . exact {};
    . apply @Model.pointGenerate.modal_equivalent_at_root (r := i₁) |>.mpr
      apply Satisfies.fconj_def.mpr;
      intro ψ hψ;
      apply Satisfies.fconj_def.mp hi;
      simp only [Finset.mem_image, Finset.eq_prebox_premultibox_one, Finset.mem_preimage, Function.iterate_one] at hψ ⊢;
      obtain ⟨ξ, hξ, rfl⟩ := hψ;
      use ξ;

end Modal.Logic

end LO
