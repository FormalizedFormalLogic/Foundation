import Foundation.Modal.Hilbert.Preliminaries

namespace LO.Modal

open System

namespace Hilbert

variable [DecidableEq α]
variable {H : Hilbert α} [H.IsNormal]
variable {φ : Formula α} {σ : α → Formula α}

lemma admissible_subst! [H.axioms.SubstClosed] (d : H ⊢! φ) : H ⊢! φ.subst σ := by
  induction d using Deduction.inducition_with_necOnly! with
  | hImply₁ => simp;
  | hImply₂ => simp;
  | hElimContra => simp;
  | hMdp ihφ ihψ => exact System.mdp! ihφ ihψ;
  | hNec ih => exact nec! ih;
  | @hMaxm φ h =>
    apply Deduction.maxm!;
    induction φ using Formula.rec' with
    | hfalsum => exact h;
    | hatom a => exact Theory.SubstClosed.mem_atom h;
    | himp φ ψ => exact Theory.SubstClosed.mem_imp h;
    | hbox φ => exact Theory.SubstClosed.mem_box h;

instance : Theory.SubstClosed (α := α) 𝗞 := by
  refine Theory.instSubstClosed ?_ ?_ ?_;
  . simp;
  . rintro _ _ ⟨_, _, rfl, rfl⟩ σ; simp;
  . simp;

instance : Theory.SubstClosed (α := α) 𝗟 := by
  refine Theory.instSubstClosed ?_ ?_ ?_;
  . simp;
  . rintro _ _ ⟨_, _, rfl, rfl⟩ σ; simp;
  . simp;

instance : Theory.SubstClosed (α := α) 𝗚𝗿𝘇 := by
  refine Theory.instSubstClosed ?_ ?_ ?_;
  . simp;
  . rintro _ _ ⟨_, _, rfl, rfl⟩ σ; simp;
  . simp;

instance : Theory.SubstClosed (α := α) 𝗛 := by
  refine Theory.instSubstClosed ?_ ?_ ?_;
  . simp;
  . rintro _ _ ⟨_, _, rfl, rfl⟩ σ; simp;
  . simp;

/-
instance : (Hilbert.K α).axioms.SubstClosed := inferInstance

instance : (Hilbert.GL α).axioms.SubstClosed := inferInstance

instance : (Hilbert.Grz α).axioms.SubstClosed := inferInstance
-/

end Hilbert

end LO.Modal
