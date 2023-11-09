import Logic.Predicate.FirstOrder.Arith.Basic

namespace LO

namespace FirstOrder

variable {L : Language.{u}} [FirstOrder.ORing L] {μ : Type v}

namespace Subterm

@[simp]
def bZeroFree : Subterm L μ (n + 1) → Bool
  | #x       => x ≠ 0
  | &_       => true
  | func _ v => ∀ i, (v i).bZeroFree

lemma bShift_of_bZeroFree : ∀ {t : Subterm L μ (n + 1)}, t.bZeroFree → ∃ u : Subterm L μ n , t = Rew.bShift u
  | #x,       h => by
    cases' x using Fin.cases with x
    · simp at h
    · exact ⟨#x, by simp⟩
  | &x,       _ => ⟨&x, by simp⟩
  | func f v, h => by
    simp[bZeroFree] at h
    choose w hw using fun i => bShift_of_bZeroFree (h i)
    exact ⟨func f w, by simp[Rew.func]; funext; simp[hw]⟩

end Subterm

namespace Arith

namespace Hierarchy

inductive DeltaZeroForm : ∀ {n}, Subformula L μ n → Prop
  | qfree {n} : ∀ {p : Subformula L μ n}, p.qfree → DeltaZeroForm p
  | and {n} {p q : Subformula L μ n} (hp : DeltaZeroForm p) (hp : DeltaZeroForm q) : DeltaZeroForm (p ⋏ q)
  | ball {n} {p : Subformula L μ (n + 1)} (t : Subterm L μ n) :
    DeltaZeroForm p → DeltaZeroForm “∀[#0 < ᵀ!(Rew.bShift t)] !p”
  | bex {n} {p : Subformula L μ (n + 1)} (t : Subterm L μ n) :
    DeltaZeroForm p → DeltaZeroForm “∃[#0 < ᵀ!(Rew.bShift t)] !p”

mutual

inductive Sigma : ℕ → ∀ {n}, Subformula L μ n → Prop
  | zero {n} {p : Subformula L μ n} : DeltaZeroForm p → Sigma 0 p
  | succ {n k} {p : Subformula L μ (n + 1)} : Pi k p → Sigma (k + 1) (∃' p)

inductive Pi : ℕ → ∀ {n}, Subformula L μ n → Prop
  | zero {n} {p : Subformula L μ n} : DeltaZeroForm p → Pi 0 p
  | succ {n k} {p : Subformula L μ (n + 1)} : Sigma k p → Pi (k + 1) (∀' p)

end

end Hierarchy

end Arith

end FirstOrder

end LO
