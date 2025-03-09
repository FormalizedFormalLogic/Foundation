import Foundation.Propositional.Classical.Basic

namespace LO.Propositional

namespace Classical

variable {v : Classical.Valuation α} {φ ψ : Formula α}

open Semantics (Valid)

open _root_.Classical in
lemma tautology_neg_zero_subst_instance_of_not_tautology (h : ¬Valid (Valuation _) φ)
  : ∃ s : ZeroSubstitution α, Valid (Valuation _) (∼(φ⟦s.1⟧)) := by
  unfold Valid at h;
  push_neg at h;
  obtain ⟨v, hv⟩ := h;
  let s : ZeroSubstitution α := ⟨
    (λ a => if (v a) then ⊤ else ⊥),
    by intro a; simp only [Formula.subst.subst_atom]; split <;> tauto;
  ⟩;
  use s;
  intro u;
  apply Formula.Classical.iff_subst_self s.1 |>.not.mp;
  apply Formula.Classical.eq_fml_of_eq_atom (v := v) ?_ |>.not.mp
  . exact hv;
  . intro a;
    simp [s, Formula.Classical.val];
    split <;> tauto;

end Classical

end LO.Propositional
