import Foundation.Logic.Predicate.Term
import Foundation.Logic.Predicate.Quantifier

namespace LO

namespace Quantifier

variable {F : ℕ → Type*} [(n : ℕ) → LogicalConnective (F n)] [Quantifier F]

inductive IsSubformula :
    {n m : ℕ} → F n → F m → Prop
  | neg (φ : F n) : IsSubformula φ (∼φ)
  | and_left (φ ψ : F n) : IsSubformula φ (φ ⋏ ψ)
  | and_right (φ ψ : F n) : IsSubformula ψ (φ ⋏ ψ)
  | or_left (φ ψ : F n) : IsSubformula φ (φ ⋎ ψ)
  | or_right (φ ψ : F n) : IsSubformula ψ (φ ⋎ ψ)
  | imp_left (φ ψ : F n) : IsSubformula φ (φ ➝ ψ)
  | imp_right (φ ψ : F n) : IsSubformula ψ (φ ➝ ψ)
  | all (φ : F (n + 1)) : IsSubformula φ (∀' φ)
  | ex (φ : F (n + 1)) : IsSubformula φ (∃' φ)

scoped infix:40 " <: " => IsSubformula

attribute [simp]
  IsSubformula.neg
  IsSubformula.and_left
  IsSubformula.and_right
  IsSubformula.or_left
  IsSubformula.or_right
  IsSubformula.imp_left
  IsSubformula.imp_right
  IsSubformula.all
  IsSubformula.ex

def IsAtomic {n} (φ : F n) : Prop := ∀ {m} (ψ : F m), ¬ψ <: φ

lemma casesss {n} (φ : F n) :
    IsAtomic φ ∨ (∃ ψ, φ = ∼ψ) ∨ (∃ ψ χ, φ = ψ ⋏ χ) ∨ (∃ ψ χ, φ = ψ ⋎ χ) ∨ (∃ ψ χ, φ = ψ ➝ χ) ∨ (∃ ψ, φ = ∀' ψ) ∨ (∃ ψ, φ = ∃' ψ) := by
  by_cases h : IsAtomic φ
  · left; exact h
  · right
    have : ∃ (m : ℕ) (ψ : F m), ψ <: φ := by simpa [IsAtomic] using h
    rcases this with ⟨m, ψ, hψ⟩
    cases hψ
    · exact .inl ⟨_, rfl⟩
    · exact .inr <| .inl ⟨_, _, rfl⟩
    · exact .inr <| .inl ⟨_, _, rfl⟩
    · exact .inr <| .inr <| .inl ⟨_, _, rfl⟩
    · exact .inr <| .inr <| .inl ⟨_, _, rfl⟩
    · exact .inr <| .inr <| .inr <| .inl ⟨_, _, rfl⟩
    · exact .inr <| .inr <| .inr <| .inl ⟨_, _, rfl⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inl ⟨_, rfl⟩
    · exact .inr <| .inr <| .inr <| .inr <| .inr ⟨_, rfl⟩

@[elab_as_elim]
lemma cases {P : {n : ℕ} → F n → Prop} {n : ℕ} (φ : F n)
    (atomic : ∀ {n} (φ : F n), IsAtomic φ → P φ)
    (neg : ∀ {n} (φ : F n), P (∼φ))
    (and : ∀ {n} (φ ψ : F n), P (φ ⋏ ψ))
    (or : ∀ {n} (φ ψ : F n), P (φ ⋎ ψ))
    (imp : ∀ {n} (φ ψ : F n), P (φ ➝ ψ))
    (all : ∀ {n} (φ : F (n + 1)), P (∀' φ))
    (ex : ∀ {n} (φ : F (n + 1)), P (∃' φ)) : P φ := by
  by_cases h : IsAtomic φ
  · exact atomic φ h
  have : ∃ (m : ℕ) (ψ : F m), ψ <: φ := by simpa [IsAtomic] using h
  rcases this with ⟨m, ψ, hψ⟩
  cases hψ
  · exact neg _
  · exact and _ _
  · exact and _ _
  · exact or _ _
  · exact or _ _
  · exact imp _ _
  · exact imp _ _
  · exact all _
  · exact ex _

inductive Acc : {n : ℕ} → F n → Prop
  | intro {n : ℕ} (φ : F n) : (∀ {m : ℕ} (ψ : F m), ψ <: φ → Acc ψ) → Acc φ

variable (F)

class WellFounded where
  wf : ∀ {n} (φ : F n), Acc φ

variable {F}

@[elab_as_elim]
lemma induction [WellFounded F] {P : {n : ℕ} → F n → Prop} {n : ℕ} (φ : F n)
    (atomic : ∀ {n} (φ : F n), IsAtomic φ → P φ)
    (neg : ∀ {n} {φ : F n}, P φ → P (∼φ))
    (and : ∀ {n} {φ ψ : F n}, P φ → P ψ → P (φ ⋏ ψ))
    (or : ∀ {n} {φ ψ : F n}, P φ → P ψ → P (φ ⋎ ψ))
    (imp : ∀ {n} {φ ψ : F n}, P φ → P ψ → P (φ ➝ ψ))
    (all : ∀ {n} {φ : F (n + 1)}, P φ → P (∀' φ))
    (ex : ∀ {n} {φ : F (n + 1)}, P φ → P (∃' φ)) : P φ := by
  revert n φ
  suffices ∀ {n : ℕ} (φ : F n), Acc φ → P φ from fun n φ ↦ this φ (WellFounded.wf φ)
  intro n φ H
  induction H
  case intro n m φ _ ih =>
    cases φ using cases
    case atomic hφ => exact atomic φ hφ
    case neg φ _ => exact neg (ih φ (by simp))
    case and φ ψ _ => exact and (ih φ (by simp)) (ih ψ (by simp))
    case or φ ψ _ => exact or (ih φ (by simp)) (ih ψ (by simp))
    case imp φ ψ _ => exact imp (ih φ (by simp)) (ih ψ (by simp))
    case all φ _ => exact all (ih φ (by simp))
    case ex φ _ => exact ex (ih φ (by simp))

end Quantifier

namespace WellFoundedFormula

end WellFoundedFormula

end LO
