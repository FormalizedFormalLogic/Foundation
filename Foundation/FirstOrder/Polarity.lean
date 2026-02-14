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

def IsPositive (φ : Semiformula L ξ n) : Prop := φ.polarity = true

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

@[simp] lemma neg_isPositive_iff {n} (φ : Semiformula L ξ n) : (∼φ).IsPositive ↔ ¬φ.IsPositive := by simp [IsPositive]

@[simp] lemma and_isPositive_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋏ ψ).IsPositive ↔ φ.IsPositive ∨ ψ.IsPositive := by
  simp [IsPositive]

@[simp] lemma or_isPositive_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋎ ψ).IsPositive ↔ φ.IsPositive ∧ ψ.IsPositive := by
  simp [IsPositive]

@[simp] lemma ex_isPositive_iff {n} (φ : Semiformula L ξ (n + 1)) :
    (∃⁰ φ).IsPositive := by simp [IsPositive]

@[simp] lemma all_isPositive_iff {n} (φ : Semiformula L ξ (n + 1)) :
    ¬(∀⁰ φ).IsPositive := by simp [IsPositive]

lemma IsPositive.eq_true {n} {φ : Semiformula L ξ n} (h : φ.IsPositive) : φ.polarity = true := h

end LO.FirstOrder.Semiformula
