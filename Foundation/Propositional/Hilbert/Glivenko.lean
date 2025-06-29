import Foundation.Propositional.Hilbert.WellKnown

namespace LO.Propositional

namespace Hilbert

open Entailment
open Formula (atom)

variable [DecidableEq α]

theorem iff_provable_dn_efq_dne_provable : Hilbert.Int ⊢! ∼∼φ ↔ Hilbert.Cl ⊢! φ := by
  constructor;
  . intro d; exact of_NN! $ Int_weakerThan_Cl.subset d;
  . intro d;
    induction d with
    | axm s hp =>
      rcases hp with (rfl | rfl);
      . apply dni'!;
        exact efq!;
      . simp only [Formula.subst.subst_or, Formula.subst.subst_atom, Formula.subst.subst_neg];
        generalize (s 0) = ψ;
        apply N!_iff_CO!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ ∼ψ)] ⊢[Hilbert.Int]! ∼ψ ⋏ ∼(ψ ➝ ⊥) := KNN!_of_NA! $ FiniteContext.id!;
        exact (N!_iff_CO!.mp $ K!_right this) ⨀ (N!_iff_CO!.mp $ K!_left this);
    | mdp ihφψ ihφ => exact CNNNN!_of_NNC! ihφψ ⨀ ihφ;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq : Hilbert.Int ⊢! ∼φ ↔ Hilbert.Cl ⊢! ∼φ := by
  constructor;
  . intro d;
    exact glivenko.mp $ dni'! d;
  . intro d;
    exact tne'! $ glivenko.mpr d;

end Hilbert

lemma iff_negneg_Int_Cl : Logic.Int ⊢! ∼∼φ ↔ Logic.Cl ⊢! φ := by
  simpa [Entailment.theory] using Hilbert.iff_provable_dn_efq_dne_provable;

lemma iff_neg_Int_neg_Cl : Logic.Int ⊢! ∼φ ↔ Logic.Cl ⊢! ∼φ := by
  simpa [Entailment.theory] using Hilbert.iff_provable_neg_efq_provable_neg_efq;

end LO.Propositional
