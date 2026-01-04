import Foundation.Modal.Formula

namespace LO.Modal

variable {α : Type*}

namespace Formula

def Letterless : Formula α → Prop
  | atom _ => False
  | ⊥ => True
  | □φ => φ.Letterless
  | φ ➝ ψ => (φ.Letterless) ∧ (ψ.Letterless)

namespace Letterless

variable {φ ψ : Formula α}

@[simp, grind] lemma not_atom : ¬(Letterless (atom p)) := by simp [Letterless]

@[simp, grind] lemma def_bot : (⊥ : Formula α).Letterless := by simp [Letterless]
@[simp, grind] lemma def_top : (⊤ : Formula α).Letterless := by simp [Letterless]

lemma def_imp : (φ ➝ ψ).Letterless → φ.Letterless ∧ ψ.Letterless := by simp [Letterless]
@[grind] lemma def_imp₁ : (φ ➝ ψ).Letterless → φ.Letterless := λ h => def_imp h |>.1
@[grind] lemma def_imp₂ : (φ ➝ ψ).Letterless → ψ.Letterless := λ h => def_imp h |>.2

@[grind] lemma def_box : (□φ).Letterless → φ.Letterless := by simp [Letterless]

@[grind] lemma of_imp (hφ : φ.Letterless) (hψ : ψ.Letterless) : (φ ➝ ψ).Letterless := by simp_all [Letterless]
@[grind] lemma of_neg (hφ : φ.Letterless) : (∼φ).Letterless := by simp_all [Letterless]
@[grind] lemma of_or (hφ : φ.Letterless) (hψ : ψ.Letterless) : (φ ⋎ ψ).Letterless := by simp_all [Letterless]
@[grind] lemma of_and (hφ : φ.Letterless) (hψ : ψ.Letterless) : (φ ⋏ ψ).Letterless := by simp_all [Letterless]
@[grind] lemma of_box (hφ : φ.Letterless) : (□φ).Letterless := by simp_all [Letterless]
@[grind] lemma of_boxItr (hφ : φ.Letterless) : (□^[n]φ).Letterless := by
  induction n with
  | zero => simpa [Letterless]
  | succ n ih => simp [Letterless, ih]
@[grind] lemma of_iff (hφ : φ.Letterless) (hψ : ψ.Letterless) : (φ ⭤ ψ).Letterless := by simp_all [Letterless]

@[grind]
lemma of_lconj₂ {l : List (Formula α)} (h : ∀ φ ∈ l, φ.Letterless) : (l.conj₂).Letterless := by
  induction l using List.induction_with_singleton <;> simp_all [Letterless];

@[grind]
lemma of_lconj' {l : List β} {Φ : β → Formula α} (h : ∀ i ∈ l, (Φ i).Letterless) : (l.conj' Φ).Letterless := by
  induction l using List.induction_with_singleton with
  | hcons _ _ _ ih => apply of_lconj₂; grind;
  | _  => simp_all [List.conj']

@[grind]
lemma of_fconj {s : Finset (Formula α)} (h : ∀ φ ∈ s, φ.Letterless) : (s.conj).Letterless := by
  apply of_lconj₂;
  simpa;

lemma of_fconj' {s : Finset β} {Φ : β → Formula α} (h : ∀ i, (Φ i).Letterless) : (⩕ i ∈ s, Φ i).Letterless := by
  apply of_lconj';
  grind;

end Letterless

@[simp, grind]
lemma subst.subst_letterless {φ : Formula α} (hφ : φ.Letterless) {s : Substitution α} : φ⟦s⟧ = φ := by
  induction φ <;> simp_all [Letterless];

end Formula



namespace FormulaSet

variable {α : Type*} {Γ : FormulaSet α} {φ : Formula α}

def Letterless (Γ : FormulaSet α) : Prop := ∀ φ ∈ Γ, φ.Letterless

@[simp, grind]
lemma letterless_singleton {φ : Formula α} : ({φ} : FormulaSet α).Letterless ↔ φ.Letterless := by
  simp [Letterless];

@[grind] lemma letterless_of_mem (hΓ : Γ.Letterless) (hφ : φ ∈ Γ) : φ.Letterless := hΓ φ hφ

end FormulaSet

end LO.Modal
