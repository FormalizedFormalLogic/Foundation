import Foundation.Propositional.Hilbert.WellKnown

namespace LO.Propositional

namespace Hilbert

open Entailment

variable [DecidableEq α]

theorem iff_provable_dn_efq_dne_provable : (Hilbert.Int) ⊢! ∼∼φ ↔ (Hilbert.Cl) ⊢! φ := by
  constructor;
  . intro d; exact of_NN! $ Int_weakerThan_Cl.subset d;
  . intro d;
    induction d using Deduction.rec! with
    | maxm hp =>
      rcases (by simpa using hp) with (⟨_, rfl⟩ | ⟨s, rfl⟩);
      . apply dni'!;
        exact efq!;
      . generalize (s 0) = ψ;
        apply N!_iff_CO!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ (ψ ➝ ⊥))] ⊢[Hilbert.Int]! ∼ψ ⋏ ∼(ψ ➝ ⊥) := KNN!_of_NA! $ FiniteContext.id!;
        exact (N!_iff_CO!.mp $ K!_right this) ⨀ (N!_iff_CO!.mp $ K!_left this);
    | mdp ihφψ ihφ => exact CNNNN!_of_NNC! ihφψ ⨀ ihφ;
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
