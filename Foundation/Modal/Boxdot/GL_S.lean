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
    apply GL.Kripke.fintype_completeness_TFAE.out 2 0 |>.mp;
    replace h := GL.Kripke.finite_completeness_TFAE.out 0 3 |>.mp $ iff_provable_rflSubformula_GL_provable_S.mpr h;

    intro M _ _ _ _;

    let n : ℕ+ := ⟨(□⁻¹'φᵇ.subformulas).card + 1, by omega⟩;

    obtain ⟨i, hi⟩ := Kripke.Model.extendRoot.inr_satisfies_axiomT_set (M := M) (Γ := □⁻¹'φᵇ.subformulas);
    apply Model.extendRoot.inl_satisfies_boxdot_iff (n := n) (i := i) |>.mp;

    let M₁ := M.extendRoot n;
    have : M₁.IsTransitive := inferInstance;

    let i₁ : M₁.World := Sum.inl i;
    have : (M₁↾i₁).IsTransitive := inferInstance;
    have : W.IsRooted := by sorry;

    have := @h (M₁↾i₁) (by sorry) (by sorry) (by sorry) (by sorry);
    have := @Model.pointGenerate.modal_equivalent_at_root (M₁↾i₁) inferInstance W.root φ;

    apply Model.pointGenerate.modal_equivalent_at_root (r := i₁) |>.mp $ h (M₁↾i₁) _;
    apply Satisfies.fconj_def.mpr;
    intro ψ hψ;
    apply Satisfies.fconj_def.mp hi;
    grind;

end Modal.Logic

end LO
end
