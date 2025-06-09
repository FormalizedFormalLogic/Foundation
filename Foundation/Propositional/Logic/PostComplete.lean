import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Logic.Cl
import Foundation.Propositional.Logic.Extension
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

abbrev Ext (L : Logic) := { L' : Logic // L'.Superintuitionistic ∧ L ⊆ L' }

open Formula (atom)
open Formula.ClassicalSemantics
open Propositional.Hilbert.Cl
open Superintuitionistic
open ClassicalSemantics

theorem Cl.post_complete : ∀ L : Ext (Logic.Cl), L.1.Consistent → L.1 = Logic.Cl := by
  by_contra! hC;
  obtain ⟨⟨L, L_si, L_subset⟩, L_consis, L_ne⟩ := hC;
  apply Logic.no_bot (L := L);
  replace ⟨hL, ⟨φ, hφ₁, hφ₂⟩⟩ := Set.ssubset_iff_exists.mp $ Set.ssubset_of_subset_ne L_subset (by tauto);
  have ⟨v, hv⟩ := exists_valuation_of_not_provable hφ₂;
  have h₁ : ∼(φ⟦(vfSubst v).1⟧) ∈ L := hL $ by
    simp only [tautologies, Formula.subst.subst_atom, Set.mem_setOf_eq];
    suffices ¬(φ⟦(vfSubst v).1⟧).isTautology by
      apply neg_isTautology_of_not_isTautology_of_letterless ?_ this;
      apply Formula.letterless_zeroSubst (s := vfSubst v);
    apply isTautology_vfSubst.not.mp hv;
  have h₂ : φ⟦(vfSubst v).1⟧ ∈ L := subst_closed hφ₁ _;
  exact mdp_closed h₁ h₂;

end Logic

end LO.Propositional
