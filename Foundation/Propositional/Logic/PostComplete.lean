module

public import Foundation.Propositional.Boolean.Hilbert
public import Foundation.Propositional.Boolean.ZeroSubst

@[expose] public section

namespace LO.Propositional

-- abbrev Ext (L : Logic ℕ) := { L' : Logic ℕ // L'.Superintuitionistic }

variable {α} [DecidableEq α] [Encodable α]

open Formula (atom)
open Formula.Boolean
open Cl
open Boolean

theorem Cl.post_complete : ¬∃ L : SuperintuitionisticLogic α, L.Consistent ∧ Propositional.Cl.logic ⊂ L.logic := by
  by_contra! hC;
  obtain ⟨L, L_consis, L_Cl⟩ := hC;
  apply L.not_mem_bot;
  obtain ⟨hL, φ, hφ₁, hφ₂⟩ := Set.ssubset_iff_exists.mp L_Cl;
  have ⟨v, hv⟩ := Hilbert.Cl.exists_valuation_of_not_provable hφ₂;
  have h₁ : ∼(φ⟦(vfSubst v).1⟧) ∈ L.logic := hL $ by
    apply Hilbert.Cl.iff_provable_tautology.mpr;
    apply Formula.neg_isTautology_of_letterless_of_isTautology;
    . grind;
    . apply vfSubst_tautology.not.mp hv;
  have h₂ : (φ⟦(vfSubst v).1⟧) ∈ L.logic := L.subst _ _ hφ₁;
  exact L.mdp h₁ h₂;

end LO.Propositional
end
