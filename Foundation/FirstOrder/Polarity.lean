module

public import Foundation.FirstOrder.Basic

/-!
# Polarity of formulas
-/

@[expose] public section

namespace LO.FirstOrder.Semiformula

variable {L : Language} {ξ : Type*}

/-- A polarity of a formula -/
def polarity {n} : Semiformula L ξ n → Bool
  |  rel _ _ => true
  | nrel _ _ => false
  |        ⊤ => true
  |        ⊥ => false
  |    φ ⋏ ψ => polarity φ || polarity ψ
  |    φ ⋎ ψ => polarity φ && polarity ψ
  |     ∀⁰ _ => false
  |     ∃⁰ _ => true

@[simp] lemma polarity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).polarity = true := rfl

@[simp] lemma polarity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).polarity = false := rfl

@[simp] lemma polarity_verum : (⊤ : Semiformula L ξ n).polarity = true := rfl

@[simp] lemma polarity_falsum : (⊥ : Semiformula L ξ n).polarity = false := rfl

@[simp] lemma polarity_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).polarity = (φ.polarity || ψ.polarity) := rfl

@[simp] lemma polarity_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).polarity = (φ.polarity && ψ.polarity) := rfl

@[simp] lemma polarity_all (φ : Semiformula L ξ (n + 1)) : (∀⁰ φ).polarity = false := rfl

@[simp] lemma polarity_ex (φ : Semiformula L ξ (n + 1)) : (∃⁰ φ).polarity = true := rfl

@[simp] lemma polarity_neg {n} (φ : Semiformula L ξ n) : (∼φ).polarity = !φ.polarity := by
  induction φ using rec' <;> simp [polarity, *]

@[simp] lemma polarity_imply {n} (φ ψ : Semiformula L ξ n) : (φ ➝ ψ).polarity = (!φ.polarity && ψ.polarity) := by
  simp [imp_eq]

abbrev Positive (φ : Semiformula L ξ n) : Prop := φ.polarity = true

abbrev Negative (φ : Semiformula L ξ n) : Prop := φ.polarity = false

@[simp] lemma rel_positive {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Positive (rel r v) := rfl

@[simp] lemma rel_negative {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ¬Negative (rel r v) := by simp [Negative]

@[simp] lemma nrel_positive {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ¬Positive (nrel r v) := by simp [Positive]

@[simp] lemma nrel_negative {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : Negative (nrel r v) := rfl

@[simp] lemma verum_positive : Positive (⊤ : Semiformula L ξ n) := rfl

@[simp] lemma verum_negative : ¬Negative (⊤ : Semiformula L ξ n) := by simp [Negative]

@[simp] lemma falsum_positive : ¬Positive (⊥ : Semiformula L ξ n) := by simp [Positive]

@[simp] lemma falsum_negative : Negative (⊥ : Semiformula L ξ n) := rfl

@[simp] lemma and_positive_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋏ ψ).Positive ↔ φ.Positive ∨ ψ.Positive := by
  simp [Positive]

@[simp] lemma and_negative_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋏ ψ).Negative ↔ φ.Negative ∧ ψ.Negative := by
  simp [Negative]

@[simp] lemma or_positive_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋎ ψ).Positive ↔ φ.Positive ∧ ψ.Positive := by
  simp [Positive]

@[simp] lemma or_negative_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋎ ψ).Negative ↔ φ.Negative ∨ ψ.Negative := by
  simp [Negative]; grind

@[simp] lemma ex_positive_iff {n} (φ : Semiformula L ξ (n + 1)) :
    (∃⁰ φ).Positive := by simp [Positive]

@[simp] lemma ex_negative_iff {n} (φ : Semiformula L ξ (n + 1)) :
    ¬(∃⁰ φ).Negative := by simp [Negative]

@[simp] lemma all_positive_iff {n} (φ : Semiformula L ξ (n + 1)) :
    ¬(∀⁰ φ).Positive := by simp [Positive]

@[simp] lemma all_negative_iff {n} (φ : Semiformula L ξ (n + 1)) :
    (∀⁰ φ).Negative := by simp [Negative]

@[simp] lemma neg_positive_iff {n} (φ : Semiformula L ξ n) : (∼φ).Positive ↔ φ.Negative := by simp [Positive, Negative]

@[simp] lemma neg_negative_iff {n} (φ : Semiformula L ξ n) : (∼φ).Negative ↔ φ.Positive := by simp [Positive, Negative]

lemma Positive.eq_true {n} {φ : Semiformula L ξ n} (h : φ.Positive) : φ.polarity = true := h

lemma Negative.eq_false {n} {φ : Semiformula L ξ n} (h : φ.Negative) : φ.polarity = false := h

@[simp] lemma polarity_rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : (ω ▹ φ).polarity = φ.polarity := by
  induction φ using rec' <;> simp [polarity, *, Semiformula.rew_rel, Semiformula.rew_nrel]

end LO.FirstOrder.Semiformula
