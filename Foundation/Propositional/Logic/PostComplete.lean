import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Logic.Cl
import Foundation.Propositional.ClassicalSemantics.Hilbert
import Foundation.Propositional.ClassicalSemantics.ZeroSubst

lemma Set.ssubset_of_subset_ne {α : Type*} {s t : Set α} (h : s ⊆ t) (hne : s ≠ t) : s ⊂ t := by
  constructor;
  . assumption;
  . revert hne;
    contrapose!;
    intro _;
    apply Set.eq_of_subset_of_subset <;> assumption;

namespace LO.Propositional

namespace Logic

-- abbrev Ext (L : Logic ℕ) := { L' : Logic ℕ // L'.Superintuitionistic }

open Formula (atom)
open Formula.ClassicalSemantics
open Propositional.Hilbert.Cl
open ClassicalSemantics

theorem Cl.post_complete : ¬∃ L : Logic _, Entailment.Consistent L ∧ Nonempty (L.IsSuperintuitionistic) ∧ Logic.Cl ⪱ L := by
  by_contra! hC;
  obtain ⟨L, L_consis, ⟨L_ne⟩, L_Cl⟩ := hC;
  apply Logic.no_bot (L := L);
  obtain ⟨hL, φ, hφ₁, hφ₂⟩ := Entailment.strictlyWeakerThan_iff.mp L_Cl;
  have ⟨v, hv⟩ := exists_valuation_of_not hφ₁;
  have h₁ : L ⊢! ∼(φ⟦(vfSubst v).1⟧) := hL $ by
    apply iff_isTautology.mpr;
    apply neg_isTautology_of_not_isTautology_of_letterless;
    . apply Formula.letterless_zeroSubst;
    . apply isTautology_vfSubst.not.mp hv;
  have h₂ : L ⊢! φ⟦(vfSubst v).1⟧ := L.subst! _ hφ₂;
  exact h₁ ⨀ h₂;

end Logic

end LO.Propositional
