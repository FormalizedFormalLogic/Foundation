module

public import Foundation.ProvabilityLogic.S.Completeness

@[expose] public section

namespace LO

namespace Modal.Kripke.Model

variable {M : Kripke.Model} {x : M.World}

instance [M.IsTransitive] : (M↾x).IsTransitive := inferInstance

instance [M.IsTransitive] [M.IsPointRooted] : (M.extendRoot n).IsTransitive := inferInstance

end Modal.Kripke.Model


namespace Modal.Logic

open Kripke Formula.Kripke

variable {φ : Formula _}

lemma iff_provable_rflSubformula_GL_provable_S : Modal.GL ⊢ (φ.rflSubformula.conj ➝ φ) ↔ Modal.S ⊢ φ := ProvabilityLogic.GL_S_TFAE (T := 𝗜𝚺₁) |>.out 0 1

lemma iff_provable_boxdot_GL_provable_boxdot_S : Modal.GL ⊢ φᵇ ↔ Modal.S ⊢ φᵇ := by
  constructor;
  . apply Entailment.WeakerThan.wk;
    infer_instance;
  . intro h;
    replace h := GL.Kripke.finite_completeness_TFAE.out 0 2 |>.mp $ iff_provable_rflSubformula_GL_provable_S.mpr h;

    apply GL.Kripke.fintype_completeness_TFAE.out 2 0 |>.mp;
    intro M _ _ _ _;

    obtain ⟨i, hi⟩ := Kripke.Model.extendRoot.inr_satisfies_forall_axiomT_set (M := M) (Γ := □⁻¹'φᵇ.subformulas);
    apply Model.extendRoot.inl_satisfies_boxdot_iff (i := i) |>.mp;
    apply h;
    apply Satisfies.fconj_def.mpr;
    simp only [Formula.rflSubformula, Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂];
    rintro ψ hψ;
    apply hi;
    exact hψ;

end Modal.Logic

end LO
end
