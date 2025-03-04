import Foundation.Propositional.Classical.Basic


namespace LO.Propositional

def Formula.letterless : Formula α → Prop
  | .atom _ => False
  | ⊥ => True
  | φ ➝ ψ => (φ.letterless) ∧ (ψ.letterless)
  | φ ⋏ ψ => (φ.letterless) ∧ (ψ.letterless)
  | φ ⋎ ψ => (φ.letterless) ∧ (ψ.letterless)

namespace Formula.letterless

variable {φ ψ : Formula α}

@[simp] lemma not_atom : ¬(letterless (atom p)) := by simp [letterless]

@[simp] lemma def_bot : (⊥ : Formula α).letterless := by simp [letterless]

@[simp] lemma def_top : (⊤ : Formula α).letterless := by simp [letterless]


lemma def_imp : (φ ➝ ψ).letterless → φ.letterless ∧ ψ.letterless := by simp [letterless]
lemma def_imp₁ : (φ ➝ ψ).letterless → φ.letterless := λ h => def_imp h |>.1
lemma def_imp₂ : (φ ➝ ψ).letterless → ψ.letterless := λ h => def_imp h |>.2

lemma def_and : (φ ⋏ ψ).letterless → φ.letterless ∧ ψ.letterless := by simp [letterless]
lemma def_and₁ : (φ ⋏ ψ).letterless → φ.letterless := λ h => def_and h |>.1
lemma def_and₂ : (φ ⋏ ψ).letterless → ψ.letterless := λ h => def_and h |>.2

lemma def_or : (φ ⋎ ψ).letterless → φ.letterless ∧ ψ.letterless := by simp [letterless]
lemma def_or₁ : (φ ⋎ ψ).letterless → φ.letterless := λ h => def_or h |>.1
lemma def_or₂ : (φ ⋎ ψ).letterless → ψ.letterless := λ h => def_or h |>.2

end Formula.letterless

def ZeroSubstitution (α) := {s : Substitution α // ∀ {a : α}, ((.atom a)⟦s⟧).letterless }

lemma Formula.letterless_zeroSubst {φ : Formula α} {s : ZeroSubstitution α} : (φ⟦s.1⟧).letterless := by
  induction φ using Formula.rec' <;> simp [Formula.letterless, *];
  case hatom => exact s.2;

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
    by intro a; simp only [Formula.subst_atom]; split <;> tauto;
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
