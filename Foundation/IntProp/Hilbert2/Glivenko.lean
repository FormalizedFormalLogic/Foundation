import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.IntProp.Hilbert2.Basic

namespace LO.IntProp

namespace Hilbert

open System

variable [DecidableEq α] [hα : Elements 1 α]

theorem iff_provable_dn_efq_dne_provable : (Hilbert.Int α) ⊢! ∼∼φ ↔ (Hilbert.Cl α) ⊢! φ := by
  constructor;
  . intro d; exact dne'! $ Int_weaker_than_Cl d;
  . intro d;
    induction d using Deduction.rec! with
    | hAxm hp =>
      rcases hp with (⟨rfl⟩ | ⟨rfl⟩);
      . apply dni'!; exact efq!;
      . generalize Formula.atom (hα.fn 0) = ψ;
        apply neg_equiv'!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ ∼ψ)] ⊢[Hilbert.Int α]! ∼ψ ⋏ ∼∼ψ := demorgan₃'! $ FiniteContext.id!;
        exact neg_mdp! (and₂'! this) (and₁'! this);
    | hMdp ihφψ ihφ => exact dn_distribute_imply'! ihφψ ⨀ ihφ;
    | hSubst ih => exact Hilbert.Deduction.subst! ih _;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq : (Hilbert.Int α) ⊢! ∼φ ↔ (Hilbert.Cl α) ⊢! ∼φ := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end Hilbert

end LO.IntProp
