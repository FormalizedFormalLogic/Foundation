import Logic.Propositional.Basic.Deduction

namespace LO.Propositional.Basic

open Hilbert Deduction

infix:45 " ⊢ᶜ " => Deduction 𝐃𝐍𝐄
infix:45 " ⊢ᶜ! " => Deducible 𝐃𝐍𝐄
infix:45 " ⊬ᶜ! " => Undeducible 𝐃𝐍𝐄

instance : Hilbert.Classical (· ⊢ᶜ · : Theory α → Formula α → Type _) where
  axm          := axm;
  weakening'   := Deduction.weakening';
  modus_ponens h₁ h₂ := by
    rename_i Γ₁ Γ₂ p q
    replace h₁ : (Γ₁ ∪ Γ₂) ⊢ᶜ p ⟶ q := h₁.weakening' (by simp);
    replace h₂ : (Γ₁ ∪ Γ₂) ⊢ᶜ p := h₂.weakening' (by simp);
    exact modusPonens h₁ h₂;
  verum        := verum;
  imply₁       := imply₁;
  imply₂       := imply₂;
  conj₁        := conj₁;
  conj₂        := conj₂;
  conj₃        := conj₃;
  disj₁        := disj₁;
  disj₂        := disj₂;
  disj₃        := disj₃;
  dne Γ p      := eaxm (by simp);

end LO.Propositional.Basic
