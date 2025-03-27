import Foundation.Propositional.Hilbert.WellKnown

namespace LO.Propositional

namespace Hilbert

open Entailment

variable [DecidableEq α]

theorem iff_provable_dn_efq_dne_provable : (Hilbert.Int) ⊢! ∼∼φ ↔ (Hilbert.Cl) ⊢! φ := by
  constructor;
  . intro d; exact φ!_of_nnφ! $ Int_weakerThan_Cl.subset d;
  . intro d;
    induction d using Deduction.rec! with
    | maxm hp =>
      rcases (by simpa using hp) with (⟨_, rfl⟩ | ⟨s, rfl⟩);
      . apply dni'!;
        exact efq!;
      . generalize (s 0) = ψ;
        apply nφ!_iff_cφo!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ (ψ ➝ ⊥))] ⊢[Hilbert.Int]! ∼ψ ⋏ ∼(ψ ➝ ⊥) := demorgan₃'! $ FiniteContext.id!;
        exact (nφ!_iff_cφo!.mp $ ψ!_of_kφψ! this) ⨀ (nφ!_iff_cφo!.mp $ φ!_of_kφψ! this);
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
