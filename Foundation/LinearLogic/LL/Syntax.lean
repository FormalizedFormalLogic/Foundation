module

public import Foundation.Logic.Predicate.Term
public import Foundation.Logic.Predicate.Quantifier
public import Foundation.Logic.Entailment
public import Foundation.LinearLogic.LogicSymbol

/-!
# First-order linear logic
-/

@[expose] public section

namespace LO.LinearLogic.FOLL

open FirstOrder

inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  /-- Multiplicative connectives -/
  |    one : Semiformula L ξ n
  | falsum : Semiformula L ξ n
  | tensor : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |    par : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  /-- Additive connectives -/
  |  verum : Semiformula L ξ n
  |   zero : Semiformula L ξ n
  |   with : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  |   plus : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  /-- Exponentials -/
  |   bang : Semiformula L ξ n → Semiformula L ξ n
  |  quest : Semiformula L ξ n → Semiformula L ξ n
  /-- Quantifiers -/
  |    all : Semiformula L ξ (n + 1) → Semiformula L ξ n
  |     ex : Semiformula L ξ (n + 1) → Semiformula L ξ n

abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0

abbrev Sentence (L : Language) := Semiformula L Empty 0

abbrev Statement (L : Language) := Formula L ℕ

namespace Semiformula

variable {L : Language} {ξ : Type*}

instance : MultiplicativeConnective (Semiformula L ξ n) where
  one := one
  bot := falsum
  tensor := tensor
  par := par

instance : AdditiveConnective (Semiformula L ξ n) where
  top := verum
  zero := zero
  with_ := .with
  plus := plus

instance : ExponentialConnective (Semiformula L ξ n) where
  bang := bang
  quest := quest

instance : Quantifier (Semiformula L ξ) where
  univ := all
  ex := ex

def neg : Semiformula L ξ n → Semiformula L ξ n
  |  rel R v => nrel R v
  | nrel R v => rel R v
  |        1 => ⊥
  |        ⊥ => 1
  |    φ ⨂ ψ => φ.neg ⅋ ψ.neg
  |    φ ⅋ ψ => φ.neg ⨂ ψ.neg
  |        ⊤ => 0
  |        0 => ⊤
  |    φ 🙲 ψ => φ.neg ⨁ ψ.neg
  |    φ ⨁ ψ => φ.neg 🙲 ψ.neg
  |       ！φ => ？φ.neg
  |       ？φ => ！φ.neg
  |     ∀' φ => ∃' φ.neg
  |     ∃' φ => ∀' φ.neg

instance : Tilde (Semiformula L ξ n) := ⟨neg⟩

instance : MultiplicativeConnective.DeMorgan (Semiformula L ξ n) where
  one := rfl
  falsum := rfl
  tensor _ _ := rfl
  par _ _ := rfl

instance : AdditiveConnective.DeMorgan (Semiformula L ξ n) where
  verum := rfl
  zero := rfl
  with_ _ _ := rfl
  plus _ _ := rfl

instance : ExponentialConnective.DeMorgan (Semiformula L ξ n) where
  bang _ := rfl
  quest _ := rfl

@[simp] lemma neg_rel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
  ∼rel R v = nrel R v := rfl

@[simp] lemma neg_nrel (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
  ∼nrel R v = rel R v := rfl

@[simp] lemma neg_all (φ : Semiformula L ξ (n + 1)) :
  ∼(∀' φ) = ∃' ∼φ := rfl

@[simp] lemma neg_ex (φ : Semiformula L ξ (n + 1)) :
  ∼(∃' φ) = ∀' ∼φ := rfl

lemma neg_neg {n} (φ : Semiformula L ξ n) : ∼∼φ = φ := by
  match φ with
  |  rel R v => rfl
  | nrel R v => rfl
  |        1 => rfl
  |        ⊥ => rfl
  |    φ ⨂ ψ => simp [neg_neg φ, neg_neg ψ]
  |    φ ⅋ ψ => simp [neg_neg φ, neg_neg ψ]
  |        ⊤ => rfl
  |        0 => rfl
  |    φ 🙲 ψ => simp [neg_neg φ, neg_neg ψ]
  |    φ ⨁ ψ => simp [neg_neg φ, neg_neg ψ]
  |       ！φ => simp [neg_neg φ]
  |       ？φ => simp [neg_neg φ]
  |     ∀' φ => simp [neg_neg φ]
  |     ∃' φ => simp [neg_neg φ]

instance : NegInvolutive (Semiformula L ξ n) := ⟨neg_neg⟩

end Semiformula

end LO.LinearLogic.FOLL

end
