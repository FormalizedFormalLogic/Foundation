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

def IsPositive (φ : Semiformula L ξ n) : Prop := φ.polarity = true

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

@[simp] lemma neg_isPositive_iff {n} (φ : Semiformula L ξ n) : (∼φ).IsPositive ↔ ¬φ.IsPositive := by simp [IsPositive]

@[simp] lemma and_isPositive_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋏ ψ).IsPositive ↔ φ.IsPositive ∨ ψ.IsPositive := by
  simp [IsPositive]

@[simp] lemma or_isPositive_iff {n} (φ ψ : Semiformula L ξ n) :
    (φ ⋎ ψ).IsPositive ↔ φ.IsPositive ∧ ψ.IsPositive := by
  simp [IsPositive]

@[simp] lemma ex_isPositive_iff {n} (φ : Semiformula L ξ (n + 1)) :
    (∃' φ).IsPositive := by simp [IsPositive]

@[simp] lemma all_isPositive_iff {n} (φ : Semiformula L ξ (n + 1)) :
    ¬(∀' φ).IsPositive := by simp [IsPositive]

lemma IsPositive.eq_true {n} {φ : Semiformula L ξ n} (h : φ.IsPositive) : φ.polarity = true := h

def girard {n} : (φ : Semiformula L ξ n) → Semiformulaᵢ L ξ n
  |  rel r v => Semiformulaᵢ.rel r v
  | nrel r v => ∼Semiformulaᵢ.rel r v
  |        ⊤ => ⊤
  |        ⊥ => ∼⊤
  |    φ ⋏ ψ =>
    match (φ ⋏ ψ).polarity with
    |  true => φ.girard ⋏ ψ.girard
    | false => ∼((∼φ).girard ⋎ (∼ψ).girard)
  |    φ ⋎ ψ =>
    match (φ ⋎ ψ).polarity with
    |  true => φ.girard ⋎ ψ.girard
    | false => ∼((∼φ).girard ⋏ (∼ψ).girard)
  |     ∃' φ => ∃' φ.girard
  |     ∀' φ => ∼(∃' (∼φ).girard)
termination_by φ => φ.complexity

@[simp] lemma girard_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).girard = Semiformulaᵢ.rel r v := by simp [girard]

@[simp] lemma girard_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).girard = ∼Semiformulaᵢ.rel r v := by simp [girard]

@[simp] lemma girard_verum : (⊤ : Semiformula L ξ n).girard = ⊤ := by grind only [= girard.eq_def]

@[simp] lemma girard_falsum : (⊥ : Semiformula L ξ n).girard = ∼⊤ := by grind only [= girard.eq_def]

lemma girard_and_pos (φ ψ : Semiformula L ξ n) (h : (φ ⋏ ψ).IsPositive) :
    (φ ⋏ ψ).girard = φ.girard ⋏ ψ.girard := by grind only [IsPositive, = girard.eq_def]

lemma girard_and_neg (φ ψ : Semiformula L ξ n) (h : ¬(φ ⋏ ψ).IsPositive) :
    (φ ⋏ ψ).girard = ∼((∼φ).girard ⋎ (∼ψ).girard) := by grind only [IsPositive, = girard.eq_def]

lemma girard_or_pos (φ ψ : Semiformula L ξ n) (h : (φ ⋎ ψ).IsPositive) :
    (φ ⋎ ψ).girard = φ.girard ⋎ ψ.girard := by grind only [IsPositive, = girard.eq_def]

lemma girard_or_neg (φ ψ : Semiformula L ξ n) (h : ¬(φ ⋎ ψ).IsPositive) :
    (φ ⋎ ψ).girard = ∼((∼φ).girard ⋏ (∼ψ).girard) := by grind only [IsPositive, = girard.eq_def]

lemma girard_ex (φ : Semiformula L ξ (n + 1)) : (∃' φ).girard = ∃' φ.girard := by grind only [IsPositive, = girard.eq_def]

lemma girard_all (φ : Semiformula L ξ (n + 1)) : (∀' φ).girard = ∼(∃' (∼φ).girard) := by grind only [= girard.eq_def]

lemma girard_neg_of_pos (φ : Semiformula L ξ n) (h : φ.IsPositive) : (∼φ).girard = ∼(φ.girard) := by
  match φ with
  | rel r v => simp
  | ⊤ => simp
  | φ ⋏ ψ =>
    rw [DeMorgan.and, girard_and_pos, girard_or_neg]
    <;> { simp_all; try tauto }
  | φ ⋎ ψ =>
    rw [DeMorgan.or, girard_or_pos, girard_and_neg]
    <;> { simp_all; try tauto }
  | ∃' φ =>
    simp [neg_ex, girard_ex, girard_all]

end LO.FirstOrder.Semiformula
