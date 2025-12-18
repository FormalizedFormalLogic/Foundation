import Foundation.Propositional.ClassicalSemantics.Hilbert
import Foundation.Propositional.ClassicalSemantics.ZeroSubst

namespace LO.Propositional

-- abbrev Ext (L : Logic ℕ) := { L' : Logic ℕ // L'.Superintuitionistic }

open Formula (atom)
open Formula.ClassicalSemantics
open Cl
open ClassicalSemantics

theorem Cl.post_complete : ¬∃ L : Logic _, Entailment.Consistent L ∧ Nonempty (L.Superintuitionistic) ∧ Propositional.Cl ⪱ L := by
  by_contra! hC;
  obtain ⟨L, L_consis, ⟨L_ne⟩, L_Cl⟩ := hC;
  apply Logic.no_bot (L := L);
  obtain ⟨hL, φ, hφ₁, hφ₂⟩ := Entailment.strictlyWeakerThan_iff.mp L_Cl;
  have ⟨v, hv⟩ := exists_valuation_of_not_provable hφ₁;
  have h₁ : L ⊢ ∼(φ⟦(vfSubst v).1⟧) := hL $ by
    apply iff_provable_tautology.mpr;
    apply neg_tautology_of_letterless_of_tautology;
    . grind;
    . apply vfSubst_tautology.not.mp hv;
  have h₂ : L ⊢ φ⟦(vfSubst v).1⟧ := L.subst _ hφ₂;
  exact h₁ ⨀ h₂;

end LO.Propositional
