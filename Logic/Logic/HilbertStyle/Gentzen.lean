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

instance (𝓣 : S) : HasAxiomEFQ 𝓣 := ⟨fun p ↦ ⟨[], by simp, implyRight (falsum _ _)⟩⟩

instance (𝓣 : S) : System.Classical 𝓣 where
  verum := of <| verum _ _
  imply₁ := fun p q ↦ of <| implyRight <| implyRight <| closed p (by simp) (by simp)
  imply₂ := fun p q r ↦ of
    <| implyRight <| implyRight <| implyRight <| wkL [p ➝ q ➝ r, p ➝ q, p] (by simp)
    <| implyLeft
      (closed p (by simp) (by simp))
      (implyLeft
        (implyLeft
          (closed p (by simp) (by simp))
          (closed q (by simp) (by simp)))
        (closed r (by simp) (by simp)))
  and₁ := fun p q ↦ of <| implyRight <| andLeft <| closed p (by simp) (by simp)
  and₂ := fun p q ↦ of <| implyRight <| andLeft <| closed q (by simp) (by simp)
  and₃ := fun p q ↦ of <| implyRight <| implyRight <| andRight (closed p (by simp) (by simp)) (closed q (by simp) (by simp))
  or₁  := fun p q ↦ of <| implyRight <| orRight <| closed p (by simp) (by simp)
  or₂  := fun p q ↦ of <| implyRight <| orRight <| closed q (by simp) (by simp)
  or₃  := fun p q r ↦ of <| implyRight <| implyRight <| implyRight
    <| orLeft
      (wkL [p ➝ r, p] (by simp) <| implyLeft (closed p (by simp) (by simp)) (closed r (by simp) (by simp)))
      (wkL [q ➝ r, q] (by simp) <| implyLeft (closed q (by simp) (by simp)) (closed r (by simp) (by simp)))
  dne := fun p ↦ of <| implyRight <| negLeft <| negRight <| closed p (by simp) (by simp)
  neg_equiv := λ {p} => of <| andRight
    (implyRight <| implyRight <| rotateLeft <| negLeft <| closed p (by simp) (by simp))
    (implyRight <| negRight  <| rotateLeft <| implyLeft (closed p (by simp) (by simp)) (falsum _ _))


def notContra {𝓣 : S} {p q : F} (b : 𝓣 ⊢ p ⭤ ∼q) : 𝓣 ⊢ ∼p ⭤ q := by
  have : [p ⭤ ∼q] ⊢² [∼p ⭤ q] :=
    andRight
      (andLeft <| implyRight
        <| negLeft <| implyLeft
          (implyLeft
            (negRight <| closed q (by simp) (by simp))
            (closed p (by simp) (by simp)))
          (negLeft <| implyLeft
            (negRight <| closed q (by simp) (by simp))
            (closed p (by simp) (by simp))))
      (andLeft <| implyRight <| rotateLeft <| implyLeft
        (rotateRight <| negRight <| closed p (by simp) (by simp))
        (negLeft <| closed q (by simp) (by simp)))
  exact toProof this (fun r ↦ by simp; rintro rfl; exact b)

lemma not_contra! {𝓣 : S} {p q : F} (b : 𝓣 ⊢! p ⭤ ∼q) : 𝓣 ⊢! ∼p ⭤ q := ⟨notContra b.get⟩

end Gentzen

namespace System

variable {F : Type*} [LogicalConnective F] {S : Type*} [System F S] {𝓢 : S} [System.Classical 𝓢]

end System

end LO
