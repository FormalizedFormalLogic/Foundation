import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.IntProp.Hilbert.Basic

namespace LO.IntProp

namespace Hilbert

open System

variable [DecidableEq α]

theorem iff_provable_dn_efq_dne_provable : (Hilbert.Int α) ⊢! ∼∼φ ↔ (Hilbert.Cl α) ⊢! φ := by
  constructor;
  . intro d; exact dne'! $ Int_weaker_than_Cl d;
  . intro d;
    induction d using Deduction.rec! with
    | eaxm hp =>
      rcases hp with (⟨_, rfl⟩ | ⟨ψ, rfl⟩);
      . apply dni'!; exact efq!;
      . apply neg_equiv'!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ ∼ψ)] ⊢[Hilbert.Int α]! ∼ψ ⋏ ∼∼ψ := demorgan₃'! $ FiniteContext.id!;
        exact neg_mdp! (and₂'! this) (and₁'! this);
    | mdp ihφψ ihφ =>
      exact dn_distribute_imply'! ihφψ ⨀ ihφ;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq : (Hilbert.Int α) ⊢! ∼φ ↔ (Hilbert.Cl α) ⊢! ∼φ := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end Hilbert

end LO.IntProp
