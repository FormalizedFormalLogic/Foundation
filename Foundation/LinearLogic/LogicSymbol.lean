module

public import Foundation.Logic.LogicSymbol

/-! # Linear connectives -/

@[expose] public section

namespace LO

class MultiplicativeConnective (α : Type*) extends One α, Bot α, Tensor α, Par α

class AdditiveConnective (α : Type*) extends Top α, Zero α, With α, Plus α

class ExponentialConnective (α : Type*) extends Bang α, Quest α

namespace MultiplicativeConnective

class DeMorgan (F : Type*) [MultiplicativeConnective F] [Tilde F] where
  one : ∼(1 : F) = ⊥
  falsum : ∼(⊥ : F) = 1
  tensor (φ ψ : F) : ∼(φ ⨂ ψ) = ∼φ ⅋ ∼ψ
  par (φ ψ : F) : ∼(φ ⅋ ψ) = ∼φ ⨂ ∼ψ

attribute [simp] DeMorgan.one DeMorgan.falsum DeMorgan.tensor DeMorgan.par DeMorgan.neg

variable {F : Type*} [MultiplicativeConnective F] [Tilde F]

instance : Lolli F where
  lolli φ ψ := ∼φ ⅋ ψ

end MultiplicativeConnective

namespace AdditiveConnective

class DeMorgan (F : Type*) [AdditiveConnective F] [Tilde F] where
  verum : ∼(⊤ : F) = 0
  zero : ∼(0 : F) = ⊤
  with_ (φ ψ : F) : ∼(φ 🙲 ψ) = ∼φ ⨁ ∼ψ
  plus (φ ψ : F) : ∼(φ ⨁ ψ) = ∼φ 🙲 ∼ψ

attribute [simp] DeMorgan.verum DeMorgan.zero DeMorgan.with_ DeMorgan.plus DeMorgan.neg

end AdditiveConnective

namespace ExponentialConnective

class DeMorgan (F : Type*) [ExponentialConnective F] [Tilde F] where
  bang (φ : F) : ∼！φ = ？∼φ
  quest (φ : F) : ∼？φ = ！∼φ

attribute [simp] DeMorgan.bang DeMorgan.quest

end ExponentialConnective

end LO

end
