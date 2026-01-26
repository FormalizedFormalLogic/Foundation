import Foundation.FirstOrder.Intuitionistic.Deduction

/-!
# Girard's Negation Translation

cf. Girard. "A new constructive logic: classic logic"
-/

namespace LO.FirstOrder.Semiformula

variable {L : Language} {ξ : Type*}

def polarity {n} : Semiformula L ξ n → Bool
  |  rel _ _ => true
  | nrel _ _ => false
  |        ⊤ => true
  |        ⊥ => false
  |    φ ⋏ ψ => polarity φ || polarity ψ
  |    φ ⋎ ψ => polarity φ && polarity ψ
  |     ∀' _ => false
  |     ∃' _ => true

abbrev IsPositive (φ : Semiformula L ξ n) : Prop := φ.polarity = true

abbrev IsNegative (φ : Semiformula L ξ n) : Prop := φ.polarity = false

@[simp] lemma polarity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).polarity = true := rfl

@[simp] lemma polarity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).polarity = false := rfl

@[simp] lemma polarity_verum : (⊤ : Semiformula L ξ n).polarity = true := rfl

@[simp] lemma polarity_falsum : (⊥ : Semiformula L ξ n).polarity = false := rfl

@[simp] lemma polarity_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).polarity = (φ.polarity || ψ.polarity) := rfl

@[simp] lemma polarity_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).polarity = (φ.polarity && ψ.polarity) := rfl

@[simp] lemma polarity_all (φ : Semiformula L ξ (n + 1)) : (∀' φ).polarity = false := rfl

@[simp] lemma polarity_ex (φ : Semiformula L ξ (n + 1)) : (∃' φ).polarity = true := rfl

@[simp] lemma polarity_neg {n} (φ : Semiformula L ξ n) : (∼φ).polarity = !φ.polarity := by
  induction φ using rec' <;> simp [polarity, *]

@[simp] lemma polarity_imply {n} (φ ψ : Semiformula L ξ n) : (φ ➝ ψ).polarity = (!φ.polarity && ψ.polarity) := by
  simp [imp_eq]

@[simp] lemma neg_isPositive {n} (φ : Semiformula L ξ n) : (∼φ).IsPositive ↔ φ.IsNegative := by
  simp []

def girardAux {n} : (φ : Semiformula L ξ n) → (H : φ.IsPositive) → Semiformulaᵢ L ξ n
  | rel r v, _ => .rel r v
  |       ⊤, _ => ⊤
  |   φ ⋏ ψ, H =>
    match hφ : φ.polarity, hψ : ψ.polarity with
    |  true,  true => girardAux φ hφ ⋏ girardAux ψ hψ
    |  true, false => girardAux φ hφ ⋏ ∼(girardAux (∼ψ) (by simpa using hψ))
    | false,  true => ∼(girardAux (∼φ) (by simpa using hφ)) ⋏ girardAux ψ hψ
    | false, false => by simp [IsPositive] at H; tauto
  |   φ ⋎ ψ, H =>
    have : φ.polarity = true ∧ ψ.polarity = true := by simpa [IsPositive] using H
    girardAux φ this.1 ⋎ girardAux ψ this.2
  |    ∃' φ, _ =>
    match hφ : φ.polarity with
    | true  => ∃' girardAux φ hφ
    | false => ∼(∀' girardAux (∼φ) (by simpa using hφ))
  |    ∀' φ, H => by simp [IsPositive] at H
termination_by φ _ => φ.complexity

end LO.FirstOrder.Semiformula
