import Foundation.Propositional.ClassicalSemantics.Basic

namespace LO.Propositional.ClassicalSemantics

variable {v : ClassicalSemantics.Valuation α} {φ ψ : Formula α}

open Classical
open Semantics (Valid)
open Formula.ClassicalSemantics

lemma tautology_neg_zero_subst_instance_of_not_tautology (h : ¬Valid (ClassicalSemantics.Valuation _) φ)
  : ∃ s : ZeroSubstitution α, Valid (ClassicalSemantics.Valuation _) (∼(φ⟦s.1⟧)) := by
  unfold Valid at h;
  push_neg at h;
  obtain ⟨v, hv⟩ := h;
  let s : ZeroSubstitution α := ⟨
    (λ a => if (v a) then ⊤ else ⊥),
    by intro a; simp only [Formula.subst.subst_atom]; split <;> tauto;
  ⟩;
  use s;
  intro u;
  apply iff_subst_self s.1 |>.not.mp;
  apply eq_fml_of_eq_atom (v := v) ?_ |>.not.mp
  . exact hv;
  . intro a;
    simp [s, val];
    split <;> tauto;

end LO.Propositional.ClassicalSemantics
