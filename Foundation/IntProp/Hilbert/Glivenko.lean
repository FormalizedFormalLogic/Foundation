import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.IntProp.Hilbert.WellKnown

namespace LO.IntProp

namespace Hilbert

open System

variable [DecidableEq α]

theorem iff_provable_dn_efq_dne_provable : (Hilbert.Int) ⊢! ∼∼φ ↔ (Hilbert.Cl) ⊢! φ := by
  constructor;
  . intro d; exact dne'! $ Int_weakerThan_Cl d;
  . intro d;
    induction d using Deduction.rec! with
    | maxm hp =>
      rcases (by simpa using hp) with (⟨_, rfl⟩ | ⟨s, rfl⟩);
      . apply dni'!;
        exact efq!;
      . generalize (s 0) = ψ;
        apply neg_equiv'!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ (ψ ➝ ⊥))] ⊢[Hilbert.Int]! ∼ψ ⋏ ∼(ψ ➝ ⊥) := demorgan₃'! $ FiniteContext.id!;
        exact (neg_equiv'!.mp $ and₂'! this) ⨀ (neg_equiv'!.mp $ and₁'! this);
    | mdp ihφψ ihφ => exact dn_distribute_imply'! ihφψ ⨀ ihφ;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq : (Hilbert.Int) ⊢! ∼φ ↔ (Hilbert.Cl) ⊢! ∼φ := by
  constructor;
  . intro d;
    exact glivenko.mp $ dni'! d;
  . intro d;
    exact tne'! $ glivenko.mpr d;

end Hilbert

end LO.IntProp
