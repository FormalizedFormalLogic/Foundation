import Foundation.Propositional.ClassicalSemantics.Basic

namespace LO.Propositional.ClassicalSemantics

variable {v : ClassicalSemantics.Valuation α} {φ ψ : Formula α}

open Classical
open Semantics (Valid)
open Formula (atom)
open Formula.ClassicalSemantics

open Classical in
noncomputable def vfSubst (v : Valuation α) : ZeroSubstitution α := ⟨
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
    simp [val, vfSubst];
    split <;> tauto;

lemma isTautology_of_forall_zeroSubst : (∀ s : ZeroSubstitution α, ¬(∼(φ⟦s.1⟧)).isTautology) → φ.isTautology := by
  contrapose!;
  apply exists_neg_zeroSubst_of_not_isTautology;

set_option push_neg.use_distrib true in
lemma isTautology_vfSubst : v ⊧ φ ↔ (φ⟦(vfSubst v).1⟧.isTautology) := by
  simp only [Formula.isTautology, Valid, Formula.subst.subst_atom, not_forall];
  induction φ with
  | hatom a =>
    dsimp [vfSubst];
    constructor;
    . intro h w;
      split;
      . tauto;
      . contradiction;
    . intro h;
      have := h v;
      split at this;
      . assumption;
      . tauto;
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro h w hφ;
      apply ihψ.mp;
      apply h;
      apply ihφ.mpr;
      intro u;
      apply equiv_of_letterless ?_ u w |>.mpr hφ;
      exact φ.letterless_zeroSubst;
    . intro h hφ;
      apply ihψ.mpr;
      intro w;
      apply equiv_of_letterless ?_ v w |>.mp;
      . apply h;
        apply ihφ.mp hφ;
      exact ψ.letterless_zeroSubst;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (h | h) w;
      . left; apply ihφ.mp; assumption;
      . right; apply ihψ.mp; assumption;
    . intro h;
      rcases h v with hφ | hψ;
      . left;
        apply ihφ.mpr;
        intro w;
        apply equiv_of_letterless ?_ v w |>.mp hφ;
        exact φ.letterless_zeroSubst;
      . right;
        apply ihψ.mpr;
        intro w;
        apply equiv_of_letterless ?_ v w |>.mp hψ;
        exact ψ.letterless_zeroSubst;
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩ w;
      constructor;
      . apply ihφ.mp hφ;
      . apply ihψ.mp hψ;
    . intro h;
      have := h v;
      constructor;
      . apply ihφ.mpr;
        intro w;
        apply equiv_of_letterless ?_ v w |>.mp $ h v |>.1;
        exact φ.letterless_zeroSubst;
      . apply ihψ.mpr;
        intro w;
        apply equiv_of_letterless ?_ v w |>.mp $ h v |>.2;
        exact ψ.letterless_zeroSubst;

end LO.Propositional.ClassicalSemantics
