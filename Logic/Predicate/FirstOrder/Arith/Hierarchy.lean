import Logic.Predicate.FirstOrder.Eq

variable {L : Language.{u}} [L.ORing] {μ : Type v}

namespace SubTerm

@[simp]
def bZeroFree : SubTerm L μ (n + 1) → Bool
  | #x       => x ≠ 0
  | &_       => true
  | func _ v => ∀ i, (v i).bZeroFree 

lemma bShift_of_bZeroFree : ∀ {t : SubTerm L μ (n + 1)}, t.bZeroFree → ∃ u : SubTerm L μ n , t = u.bShift
  | #x,       h => by
    cases' x using Fin.cases with x
    · simp at h
    · exact ⟨#x, by simp⟩
  | &x,       _ => ⟨&x, by simp⟩
  | func f v, h => by
    simp[bZeroFree] at h
    choose w hw using fun i => bShift_of_bZeroFree (h i)
    exact ⟨func f w, by simp[bShift_func]; funext; simp[hw]⟩

end SubTerm

namespace FirstOrder

namespace Arith

namespace Hierarchy

inductive DeltaZero : ∀ {n}, SubFormula L μ n → Prop
  | qfree {n} : ∀ {p : SubFormula L μ n}, p.qfree → DeltaZero p
  | ballFvar {n} {p : SubFormula L μ (n + 1)} {x : Fin (n + 1)} (h : x ≠ 0) :
    DeltaZero p → DeltaZero “∀[#0 < #x] !p”
  | bexFvar {n} {p : SubFormula L μ (n + 1)} {x : Fin (n + 1)} (h : x ≠ 0) :
    DeltaZero p → DeltaZero “∃[#0 < #x] !p”

mutual

inductive Sigma : ℕ → ∀ {n}, SubFormula L μ n → Prop
  | zero {n} {p : SubFormula L μ n} : DeltaZero p → Sigma 0 p
  | succ {n k} {p : SubFormula L μ (n + 1)} : Pi k p → Sigma (k + 1) (∃' p)

inductive Pi : ℕ → ∀ {n}, SubFormula L μ n → Prop
  | zero {n} {p : SubFormula L μ n} : DeltaZero p → Pi 0 p
  | succ {n k} {p : SubFormula L μ (n + 1)} : Sigma k p → Pi (k + 1) (∀' p)

end

end Hierarchy

end Arith

end FirstOrder