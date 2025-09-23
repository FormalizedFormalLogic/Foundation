import Foundation.Propositional.Hilbert.Basic2

namespace LO.Propositional

open Entailment
open Formula (atom)

variable [DecidableEq α]

instance : 𝐈𝐧𝐭 ⪯ 𝐂𝐥 := Hilbert.weakerThan_of_subset_axioms $ by simp

theorem iff_provable_dn_Int_Cl : 𝐈𝐧𝐭 ⊢! ∼∼φ ↔ 𝐂𝐥 ⊢! φ := by
  constructor;
  . intro d;
    exact of_NN! $ WeakerThan.pbl d;
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
        have : [∼(ψ ⋎ ∼ψ)] ⊢[𝐈𝐧𝐭]! ∼ψ ⋏ ∼(ψ ➝ ⊥) := KNN!_of_NA! $ FiniteContext.id!;
        exact (N!_iff_CO!.mp $ K!_right this) ⨀ (N!_iff_CO!.mp $ K!_left this);
    | mdp ihφψ ihφ => exact CNNNN!_of_NNC! ihφψ ⨀ ihφ;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_Int_Cl

theorem iff_provable_not_Int_not_Cl : 𝐈𝐧𝐭 ⊢! ∼φ ↔ 𝐂𝐥 ⊢! ∼φ := by
  constructor;
  . intro d;
    exact glivenko.mp $ dni'! d;
  . intro d;
    exact tne'! $ glivenko.mpr d;

end LO.Propositional
