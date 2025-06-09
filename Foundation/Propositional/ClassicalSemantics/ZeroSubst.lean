import Foundation.Propositional.ClassicalSemantics.Basic

namespace LO.Propositional.ClassicalSemantics

variable {v : ClassicalSemantics.Valuation α} {φ ψ : Formula α}

open Classical
open Semantics (Valid)
open Formula.ClassicalSemantics

open Classical in
noncomputable abbrev vfSubst (v : Valuation α) : ZeroSubstitution α := ⟨
    λ a => if v a then ⊤ else ⊥,
    by intro a; simp [Formula.subst.subst_atom]; split <;> tauto;
⟩

theorem exists_neg_zeroSubst_of_not_isTautology (h : ¬φ.isTautology)
  : ∃ s : ZeroSubstitution α, Formula.isTautology (∼(φ⟦s.1⟧)) := by
  unfold Formula.isTautology Valid at h;
  push_neg at h;
  obtain ⟨v, hv⟩ := h;
  use vfSubst v;
  intro u;
  apply iff_subst_self _ |>.not.mp;
  apply eq_fml_of_eq_atom (v := v) ?_ |>.not.mp
  . exact hv;
  . intro a;
    simp [val];
    split <;> tauto;

lemma isTautology_of_forall_zeroSubst : (∀ s : ZeroSubstitution α, ¬(∼(φ⟦s.1⟧)).isTautology) → φ.isTautology := by
  contrapose!;
  apply exists_neg_zeroSubst_of_not_isTautology;

end LO.Propositional.ClassicalSemantics
