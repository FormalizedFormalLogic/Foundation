module
import Foundation.Propositional.Hilbert.Standard.Basic
import Foundation.Meta.IntProver
import Foundation.Meta.ClProver

namespace LO.Propositional

open LO.Entailment
open Formula (atom)

variable [DecidableEq α]

instance : Propositional.Int ⪯ Propositional.Cl := Hilbert.Standard.weakerThan_of_subset_axioms $ by simp

theorem iff_provable_dn_Int_Cl : Propositional.Int ⊢ ∼∼φ ↔ Propositional.Cl ⊢ φ := by
  constructor;
  . intro d;
    exact of_NN! $ WeakerThan.pbl d;
  . intro d;
    induction d with
    | axm s hp =>
      rcases hp with (rfl | rfl);
      . suffices Propositional.Int ⊢ ∼∼(⊥ ➝ s 0) by simpa;
        int_prover;
      . suffices Propositional.Int ⊢ ∼∼(s 0 ⋎ ∼s 0) by simpa;
        int_prover;
    | mdp ihφψ ihφ => exact CNNNN!_of_NNC! ihφψ ⨀ ihφ;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_Int_Cl

theorem iff_provable_not_Int_not_Cl : Propositional.Int ⊢ ∼φ ↔ Propositional.Cl ⊢ ∼φ := by
  constructor;
  . intro d;
    exact glivenko.mp $ dni'! d;
  . intro d;
    exact tne'! $ glivenko.mpr d;

end LO.Propositional
