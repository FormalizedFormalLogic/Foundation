module

public import Foundation.Propositional.Hilbert.Minimal.Basic
public import Foundation.Meta.IntProver
public import Foundation.Meta.ClProver

@[expose] public section

namespace LO.Propositional

open LO.Entailment
open Formula (atom)

variable [DecidableEq α] {φ : Formula α}

namespace Hilbert

instance : (Hilbert.Int : Hilbert α) ⪯ Hilbert.Cl := Hilbert.weakerThan_of_le $ by simp

theorem iff_provable_dn_Int_Cl : Hilbert.Int ⊢ ∼∼φ ↔ Hilbert.Cl ⊢ φ := by
  constructor;
  . intro d;
    exact of_NN! $ WeakerThan.pbl d;
  . intro ⟨d⟩;
    induction d with
    | mdp _ _ ihφψ ihφ => exact (CNNNN!_of_NNC! ihφψ) ⨀ ihφ;
    | axm h => rcases h with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> int_prover;
    | _ => apply dni'! (by simp);

alias glivenko := iff_provable_dn_Int_Cl

theorem iff_provable_neg_Int_neg_Cl : Hilbert.Int ⊢ ∼φ ↔ Hilbert.Cl ⊢ ∼φ := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end Hilbert

end LO.Propositional

end
