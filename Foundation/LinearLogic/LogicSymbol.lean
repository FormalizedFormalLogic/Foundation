module

public import Foundation.Logic.LogicSymbol

/-! # Linear connectives -/

@[expose] public section

namespace LO

class MultiplicativeConnective (α : Type*) extends Tensor α, Par α where
  tensor_injective : Function.Injective2 tensor
  par_injective : Function.Injective2 par

class MultiplicativeNeutral (α : Type*) extends One α, Bot α

class AdditiveConnective (α : Type*) extends With α, Plus α where
  with_injective : Function.Injective2 with'
  plus_injective : Function.Injective2 plus

class AdditiveNeutral (α : Type*) extends Top α, Zero α

class ExponentialConnective (α : Type*) extends Bang α, Quest α where
  bang_injective : Function.Injective bang
  quest_injective : Function.Injective quest

namespace MultiplicativeConnective

class DeMorgan (F : Type*) [MultiplicativeConnective F] [Tilde F] where
  tensor (φ ψ : F) : ∼(φ ⨂ ψ) = ∼φ ⅋ ∼ψ
  par (φ ψ : F) : ∼(φ ⅋ ψ) = ∼φ ⨂ ∼ψ

attribute [simp] DeMorgan.tensor DeMorgan.par

variable {F : Type*} [MultiplicativeConnective F]

instance [Tilde F] : Lolli F where
  lolli φ ψ := ∼φ ⅋ ψ

@[simp] lemma tensor_eq_tensor_iff_eq {φ₁ ψ₁ φ₂ ψ₂ : F} :
    φ₁ ⨂ ψ₁ = φ₂ ⨂ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := Function.Injective2.eq_iff tensor_injective

@[simp] lemma par_eq_par_iff_eq {φ₁ ψ₁ φ₂ ψ₂ : F} :
    φ₁ ⅋ ψ₁ = φ₂ ⅋ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := Function.Injective2.eq_iff par_injective

@[simp] lemma lolli_eq_lolli_iff_eq [Tilde F] [TildeInvolutive F] {φ₁ ψ₁ φ₂ ψ₂ : F} :
    φ₁ ⊸ ψ₁ = φ₂ ⊸ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := by
  simp [Lolli.lolli]

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

variable {F : Type*} [AdditiveConnective F]

@[simp] lemma with_eq_with_iff_eq {φ₁ ψ₁ φ₂ ψ₂ : F} :
    φ₁ ＆ ψ₁ = φ₂ ＆ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := Function.Injective2.eq_iff with_injective

@[simp] lemma plus_eq_plus_iff_eq {φ₁ ψ₁ φ₂ ψ₂ : F} :
    φ₁ ⨁ ψ₁ = φ₂ ⨁ ψ₂ ↔ φ₁ = φ₂ ∧ ψ₁ = ψ₂ := Function.Injective2.eq_iff plus_injective

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

variable {F : Type*} [ExponentialConnective F]

@[simp] lemma bang_eq_bang_iff_eq {φ₁ φ₂ : F} :
    ！φ₁ = ！φ₂ ↔ φ₁ = φ₂ := Function.Injective.eq_iff bang_injective

@[simp] lemma quest_eq_quest_iff_eq {φ₁ φ₂ : F} :
    ？φ₁ = ？φ₂ ↔ φ₁ = φ₂ := Function.Injective.eq_iff quest_injective

def listQuest (Γ : List F) : List F := Γ.map (？·)

instance : Quest (List F) := ⟨listQuest⟩

lemma listQuest_def (Γ : List F) : ？Γ = Γ.map (？·) := rfl

@[simp] lemma listQuest_nil : ？([] : List F) = [] := rfl

@[simp] lemma listQuest_cons (φ : F) (Γ : List F) :
    ？(φ :: Γ) = ？φ :: ？Γ := rfl

@[simp] lemma listQuest_append (Γ Δ : List F) :
    ？(Γ ++ Δ) = ？Γ ++ ？Δ := by simp [listQuest_def]

end ExponentialConnective

end LO

end
