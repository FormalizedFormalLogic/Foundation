import Foundation.Propositional.Hilbert.WellKnown

namespace LO.Propositional

namespace Hilbert

open Entailment

variable [DecidableEq α]

theorem iff_provable_dn_efq_dne_provable : (Hilbert.Int) ⊢! ∼∼φ ↔ (Hilbert.Cl) ⊢! φ := by
  constructor;
  . intro d; exact of_nn! $ Int_weakerThan_Cl.subset d;
  . intro d;
    induction d using Deduction.rec! with
    | maxm hp =>
      rcases (by simpa using hp) with (⟨_, rfl⟩ | ⟨s, rfl⟩);
      . apply dni'!;
        exact efq!;
      . generalize (s 0) = ψ;
        apply n!_iff_cO!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ (ψ ➝ ⊥))] ⊢[Hilbert.Int]! ∼ψ ⋏ ∼(ψ ➝ ⊥) := demorgan₃'! $ FiniteContext.id!;
        exact (n!_iff_cO!.mp $ of_k_right this) ⨀ (n!_iff_cO!.mp $ of_k!_left this);
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

end LO.Propositional
