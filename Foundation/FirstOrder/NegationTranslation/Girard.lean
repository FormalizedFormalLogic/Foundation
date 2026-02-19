module

public import Foundation.FirstOrder.Polarity
public import Foundation.FirstOrder.Intuitionistic.Deduction

/-!
# Girard's negation translation

reference: Girard. "A new constructive logic: classic logic" [Gir91]
-/

@[expose] public section

namespace LO.FirstOrder.Semiformula

variable {L : Language} {ξ : Type*}

/-- Girard's negation translation -/
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
  |     ∃⁰ φ => ∃⁰ φ.girard
  |     ∀⁰ φ => ∼(∃⁰ (∼φ).girard)
termination_by φ => φ.complexity

@[simp] lemma girard_rel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).girard = Semiformulaᵢ.rel r v := by simp [girard]

@[simp] lemma girard_nrel (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).girard = ∼Semiformulaᵢ.rel r v := by simp [girard]

@[simp] lemma girard_verum : (⊤ : Semiformula L ξ n).girard = ⊤ := by grind only [= girard.eq_def]

@[simp] lemma girard_falsum : (⊥ : Semiformula L ξ n).girard = ∼⊤ := by grind only [= girard.eq_def]

lemma girard_and_pos (φ ψ : Semiformula L ξ n) (h : (φ ⋏ ψ).Positive) :
    (φ ⋏ ψ).girard = φ.girard ⋏ ψ.girard := by grind [= girard.eq_def]

lemma girard_and_neg (φ ψ : Semiformula L ξ n) (h : ¬(φ ⋏ ψ).Positive) :
    (φ ⋏ ψ).girard = ∼((∼φ).girard ⋎ (∼ψ).girard) := by grind only [= girard.eq_def]

lemma girard_or_pos (φ ψ : Semiformula L ξ n) (h : (φ ⋎ ψ).Positive) :
    (φ ⋎ ψ).girard = φ.girard ⋎ ψ.girard := by grind only [= girard.eq_def]

lemma girard_or_neg (φ ψ : Semiformula L ξ n) (h : ¬(φ ⋎ ψ).Positive) :
    (φ ⋎ ψ).girard = ∼((∼φ).girard ⋏ (∼ψ).girard) := by grind only [= girard.eq_def]

lemma girard_ex (φ : Semiformula L ξ (n + 1)) : (∃⁰ φ).girard = ∃⁰ φ.girard := by grind only [= girard.eq_def]

lemma girard_all (φ : Semiformula L ξ (n + 1)) : (∀⁰ φ).girard = ∼(∃⁰ (∼φ).girard) := by grind only [= girard.eq_def]

end LO.FirstOrder.Semiformula
