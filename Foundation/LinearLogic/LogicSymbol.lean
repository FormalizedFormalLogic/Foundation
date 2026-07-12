module

public import Foundation.Logic.LogicSymbol

/-! # Linear connectives -/

@[expose] public section

namespace LO

class MultiplicativeConnective (α : Type*) extends Tensor α, Par α

class MultiplicativeNeutral (α : Type*) extends One α, Bot α

class AdditiveConnective (α : Type*) extends With α, Plus α

class AdditiveNeutral (α : Type*) extends Top α, Zero α

class ExponentialConnective (α : Type*) extends Bang α, Quest α

namespace MultiplicativeConnective

class DeMorgan (F : Type*) [MultiplicativeConnective F] [Tilde F] where
  tensor (φ ψ : F) : ∼(φ ⨂ ψ) = ∼φ ⅋ ∼ψ
  par (φ ψ : F) : ∼(φ ⅋ ψ) = ∼φ ⨂ ∼ψ

attribute [simp] DeMorgan.tensor DeMorgan.par

variable {F : Type*} [MultiplicativeConnective F] [Tilde F]

instance : Lolli F where
  lolli φ ψ := ∼φ ⅋ ψ

end MultiplicativeConnective

namespace MultiplicativeNeutral

class DeMorgan (F : Type*) [MultiplicativeNeutral F] [Tilde F] where
  one : ∼(1 : F) = ⊥
  bot : ∼(⊥ : F) = 1

attribute [simp] DeMorgan.one DeMorgan.bot

end MultiplicativeNeutral

namespace AdditiveConnective

class DeMorgan (F : Type*) [AdditiveConnective F] [Tilde F] where
  with_ (φ ψ : F) : ∼(φ ＆ ψ) = ∼φ ⨁ ∼ψ
  plus (φ ψ : F) : ∼(φ ⨁ ψ) = ∼φ ＆ ∼ψ

attribute [simp] DeMorgan.with_ DeMorgan.plus

end AdditiveConnective

namespace AdditiveNeutral

class DeMorgan (F : Type*) [AdditiveNeutral F] [Tilde F] where
  top : ∼(⊤ : F) = 0
  zero : ∼(0 : F) = ⊤

attribute [simp] DeMorgan.top DeMorgan.zero

end AdditiveNeutral

namespace ExponentialConnective

class DeMorgan (F : Type*) [ExponentialConnective F] [Tilde F] where
  bang (φ : F) : ∼！φ = ？∼φ
  quest (φ : F) : ∼？φ = ！∼φ

attribute [simp] DeMorgan.bang DeMorgan.quest

end ExponentialConnective

end LO

end
