import Logic.Logic.HilbertStyle.Context
import Logic.Logic.Calculus

namespace LO

namespace Gentzen

open System

variable {F : Type*} [LogicalConnective F] [Gentzen F] [Cut F]

variable {S : Type*} [Collection F S]

instance (𝓣 : S) : System.ModusPonens 𝓣 := ⟨
  fun {p q} ↦ by
    rintro ⟨Γ₁, h₁, d₁⟩ ⟨Γ₂, h₂, d₂⟩
    let d₃ : Γ₁ ++ Γ₂ ⊢² [q] := modusPonens (wkLeft d₁ (by simp)) (wkLeft d₂ (by simp))
    exact ⟨Γ₁ ++ Γ₂, by simp; rintro p (hp | hp); { exact h₁ p hp }; { exact h₂ p hp }, d₃⟩⟩

instance (𝓣 : S) : HasEFQ 𝓣 := ⟨fun p ↦ ⟨[], by simp, implyRight (falsum _ _)⟩⟩

instance (𝓣 : S) : Classical 𝓣 where
  verum := of <| verum _ _
  imply₁ := fun p q ↦ of <| implyRight <| implyRight <| closed p (by simp) (by simp)
  imply₂ := fun p q r ↦ of
    <| implyRight <| implyRight <| implyRight <| wkL [p ⟶ q ⟶ r, p ⟶ q, p] (by simp)
    <| implyLeft
      (closed p (by simp) (by simp))
      (implyLeft
        (implyLeft
          (closed p (by simp) (by simp))
          (closed q (by simp) (by simp)))
        (closed r (by simp) (by simp)))
  conj₁ := fun p q ↦ of <| implyRight <| andLeft <| closed p (by simp) (by simp)
  conj₂ := fun p q ↦ of <| implyRight <| andLeft <| closed q (by simp) (by simp)
  conj₃ := fun p q ↦ of <| implyRight <| implyRight <| andRight (closed p (by simp) (by simp)) (closed q (by simp) (by simp))
  disj₁ := fun p q ↦ of <| implyRight <| orRight <| closed p (by simp) (by simp)
  disj₂ := fun p q ↦ of <| implyRight <| orRight <| closed q (by simp) (by simp)
  disj₃ := fun p q r ↦ of <| implyRight <| implyRight <| implyRight
    <| orLeft
      (wkL [p ⟶ r, p] (by simp) <| implyLeft (closed p (by simp) (by simp)) (closed r (by simp) (by simp)))
      (wkL [q ⟶ r, q] (by simp) <| implyLeft (closed q (by simp) (by simp)) (closed r (by simp) (by simp)))
  dne := fun p ↦ of <| implyRight <| negLeft <| negRight <| closed p (by simp) (by simp)

end Gentzen

end LO
