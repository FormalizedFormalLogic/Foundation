import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Classical.Deduction

namespace LO.Propositional.Superintuitionistic

open Hilbert Deduction

variable {α} [DecidableEq α]

infix:45 " ⊢ⁱ " => Deduction 𝐄𝐅𝐐
infix:45 " ⊢ⁱ! " => Deducible 𝐄𝐅𝐐
infix:45 " ⊬ⁱ! " => Undeducible 𝐄𝐅𝐐

instance : Hilbert.Intuitionistic (· ⊢ⁱ · : Theory α → Formula α → Type _) where
  axm          := axm;
  weakening'   := Deduction.weakening';
  modus_ponens h₁ h₂ := by
    rename_i Γ₁ Γ₂ p q
    replace h₁ : (Γ₁ ∪ Γ₂) ⊢ⁱ p ⟶ q := h₁.weakening' (by simp);
    replace h₂ : (Γ₁ ∪ Γ₂) ⊢ⁱ p := h₂.weakening' (by simp);
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
  efq Γ p      := eaxm (by simp);

namespace Deduction

variable {Γ : Theory α} {p : Formula α}

theorem deducible_Classical_of_Int (d : Γ ⊢ⁱ! p) : (Γ ⊢ᶜ! p) := by
  induction d.some with
  | axm => apply axm! (by assumption)
  | eaxm ih =>
    obtain ⟨q, hq⟩ := ih;
    subst hq;
    apply efq!;
  | modusPonens h₁ h₂ ih₁ ih₂ => exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩)
  | _ =>
    try first
    | apply verum!
    | apply imply₁!
    | apply imply₂!
    | apply conj₁!
    | apply conj₂!
    | apply conj₃!
    | apply disj₁!
    | apply disj₂!
    | apply disj₃!

/-- a.k.a. Glivenko's Theorem -/
theorem deducible_dn_iff_Int_Classical : (Γ ⊢ⁱ! ~~p) ↔ (Γ ⊢ᶜ! p) := by
  constructor;
  . intro d;
    exact dne'! $ deducible_Classical_of_Int d;
  . intro d;
    induction d.some with
    | axm h => exact dni'! $ axm! h;
    | @modusPonens p q h₁ h₂ ih₁ ih₂ =>
      have : Γ ⊢ⁱ! ~~p ⟶ ~~q := dn_distribute_imp_left'! $ ih₁ ⟨h₁⟩;
      exact (by assumption) ⨀ ih₂ ⟨h₂⟩;
    | eaxm ih =>
      obtain ⟨q, hq⟩ := ih;
      subst hq;
      exact dn_disctribute_imp_right'! $ contra₀'! $ dni!;
    | _ =>
      apply dni'!;
      try first
      | apply verum!
      | apply imply₁!
      | apply imply₂!
      | apply conj₁!
      | apply conj₂!
      | apply conj₃!
      | apply disj₁!
      | apply disj₂!
      | apply disj₃!

alias glivenko := deducible_dn_iff_Int_Classical

theorem deducible_neg_iff_Int_Classical : (Γ ⊢ⁱ! ~p) ↔ (Γ ⊢ᶜ! ~p) := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end Deduction

end LO.Propositional.Superintuitionistic
