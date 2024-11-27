import Foundation.IntProp.Hilbert.Basic

namespace LO.IntProp

namespace Hilbert

open System

variable [DecidableEq α]

theorem iff_provable_dn_efq_dne_provable : (Hilbert.Int α) ⊢! ∼∼φ ↔ (Hilbert.Cl α) ⊢! φ := by
  constructor;
  . intro d; exact dne'! $ Int_weaker_than_Cl d;
  . intro d;
    induction d.some with
    | eaxm h =>
      simp at h;
      rcases h with (hEFQ | hLEM);
      . obtain ⟨ψ, hq⟩ := by simpa using hEFQ;
        subst hq;
        exact dni'! efq!;
      . obtain ⟨ψ, hq⟩ := by simpa using hLEM;
        subst hq;
        apply neg_equiv'!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ ∼ψ)] ⊢[Hilbert.Int α]! ∼ψ ⋏ ∼∼ψ := demorgan₃'! $ FiniteContext.id!;
        exact neg_mdp! (and₂'! this) (and₁'! this);
    | @mdp φ ψ h₁ h₂ ih₁ ih₂ =>
      exact (dn_distribute_imply'! $ ih₁ ⟨h₁⟩) ⨀ ih₂ ⟨h₂⟩;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq : (Hilbert.Int α) ⊢! ∼φ ↔ (Hilbert.Cl α) ⊢! ∼φ := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end Hilbert

end LO.IntProp
