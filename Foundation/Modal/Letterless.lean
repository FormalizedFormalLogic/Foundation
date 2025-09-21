import Foundation.Modal.Formula

namespace LO.Modal

variable {α : Type*}

namespace Formula

def letterless : Formula α → Prop
  | atom _ => False
  | ⊥ => True
  | □φ => φ.letterless
  | φ ➝ ψ => (φ.letterless) ∧ (ψ.letterless)

namespace letterless

variable {φ ψ : Formula α}

@[simp, grind] lemma not_atom : ¬(letterless (atom p)) := by simp [letterless]

@[simp, grind] lemma def_bot : (⊥ : Formula α).letterless := by simp [letterless]
@[simp, grind] lemma def_top : (⊤ : Formula α).letterless := by simp [letterless]

lemma def_imp : (φ ➝ ψ).letterless → φ.letterless ∧ ψ.letterless := by simp [letterless]
@[grind] lemma def_imp₁ : (φ ➝ ψ).letterless → φ.letterless := λ h => def_imp h |>.1
@[grind] lemma def_imp₂ : (φ ➝ ψ).letterless → ψ.letterless := λ h => def_imp h |>.2

@[grind] lemma def_box : (□φ).letterless → φ.letterless := by simp [letterless]

@[grind] lemma of_imp (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ➝ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_neg (hφ : φ.letterless) : (∼φ).letterless := by simp_all [letterless]
@[grind] lemma of_or (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⋎ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_and (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⋏ ψ).letterless := by simp_all [letterless]
@[grind] lemma of_box (hφ : φ.letterless) : (□φ).letterless := by simp_all [letterless]
@[grind] lemma of_multibox (hφ : φ.letterless) : (□^[n]φ).letterless := by
  induction n with
  | zero => simpa [letterless]
  | succ n ih => simp [letterless, ih]
@[grind] lemma of_iff (hφ : φ.letterless) (hψ : ψ.letterless) : (φ ⭤ ψ).letterless := by simp_all [letterless]

@[grind]
lemma of_lconj₂ {l : List (Formula α)} (h : ∀ φ ∈ l, φ.letterless) : (l.conj₂).letterless := by
  induction l using List.induction_with_singleton <;> simp_all [letterless];

@[grind]
lemma of_lconj' {l : List β} {Φ : β → Formula α} (h : ∀ i ∈ l, (Φ i).letterless) : (l.conj' Φ).letterless := by
  induction l using List.induction_with_singleton with
  | hcons _ _ _ ih => apply of_lconj₂; grind;
  | _  => simp_all [List.conj']

@[grind]
lemma of_fconj {s : Finset (Formula α)} (h : ∀ φ ∈ s, φ.letterless) : (s.conj).letterless := by
  apply of_lconj₂;
  simpa;

lemma of_fconj' {s : Finset β} {Φ : β → Formula α} (h : ∀ i, (Φ i).letterless) : (⩕ i ∈ s, Φ i).letterless := by
  apply of_lconj';
  grind;

end letterless

@[simp, grind]
lemma subst.subst_letterless {φ : Formula α} (hφ : φ.letterless) {s : Substitution α} : φ⟦s⟧ = φ := by
  induction φ <;> simp_all [letterless];

end Formula



namespace FormulaSet

variable {α : Type*} {Γ : FormulaSet α} {φ : Formula α}

def letterless (Γ : FormulaSet α) : Prop := ∀ φ ∈ Γ, φ.letterless

@[simp, grind]
lemma letterless_singleton {φ : Formula α} : ({φ} : FormulaSet α).letterless ↔ φ.letterless := by
  simp [FormulaSet.letterless];

@[grind] lemma letterless_of_mem (hΓ : Γ.letterless) (hφ : φ ∈ Γ) : φ.letterless := hΓ φ hφ

end FormulaSet

end LO.Modal
