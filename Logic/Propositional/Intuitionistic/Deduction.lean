import Logic.Logic.System
import Logic.Propositional.Intuitionistic.Formula
import Logic.Propositional.Intuitionistic.Axioms

namespace LO.Propositional.Intuitionistic

variable {α : Type u} [DecidableEq α]

inductive Deduction (Λ : AxiomSet α) : Theory α → Formula α → Type _
  | axm {Γ p}        : p ∈ Γ → Deduction Λ Γ p
  | eaxm {Γ p}       : p ∈ Λ → Deduction Λ Γ p
  | modusPonens {Γ p q} : Deduction Λ Γ (p ⟶ q) → Deduction Λ Γ p → Deduction Λ Γ q
  | verum Γ          : Deduction Λ Γ ⊤
  | imply₁ Γ p q     : Deduction Λ Γ (p ⟶ q ⟶ p)
  | imply₂ Γ p q r   : Deduction Λ Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ Γ p q      : Deduction Λ Γ (p ⋏ q ⟶ p)
  | conj₂ Γ p q      : Deduction Λ Γ (p ⋏ q ⟶ q)
  | conj₃ Γ p q      : Deduction Λ Γ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ Γ p q      : Deduction Λ Γ (p ⟶ p ⋎ q)
  | disj₂ Γ p q      : Deduction Λ Γ (q ⟶ p ⋎ q)
  | disj₃ Γ p q r    : Deduction Λ Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  -- | efq Γ p          : Deduction Λ Γ (⊥ ⟶ p)

notation:45 Γ " ⊢ᴾ[" Λ "] " p => Deduction Λ Γ p

variable (Λ : AxiomSet α) (Γ : Theory α) (p : Formula α)

abbrev Deducible := Nonempty (Γ ⊢ᴾ[Λ] p)
notation:45 Γ " ⊢ᴾ[" Λ "]! " p => Deducible Λ Γ p

abbrev Undeducible := ¬(Γ ⊢ᴾ[Λ]! p)
notation:45 Γ " ⊬ᴾ[" Λ "]! " p => Undeducible Λ Γ p

abbrev Theory.Consistent := Γ ⊬ᴾ[Λ]! ⊥

abbrev Theory.Inconsistent := Γ ⊢ᴾ[Λ]! ⊥

/-
infix:45 " ⊢ⁱ! " => Deducible

abbrev Undeducible := Hilbert.Undeducible (@Deduction α)
infix:45 " ⊬ⁱ! " => Undeducible

abbrev Theory.Consistent := Hilbert.Consistent (@Deduction α) Γ
abbrev Theory.Inconsistent := Hilbert.Inconsistent (@Deduction α) Γ
-/

namespace Deduction

open Hilbert

variable {Λ : AxiomSet α} {Γ : Theory α} {p q : Formula α}

def weakening' {Γ Δ} {p : Formula α} (hs : Γ ⊆ Δ) : Deduction Λ Γ p → Deduction Λ Δ p
  | axm h => axm (hs h)
  | eaxm h => eaxm h
  | modusPonens h₁ h₂ => by
      -- simp [Finset.union_subset_iff] at hs;
      simpa using (h₁.weakening' hs).modusPonens (h₂.weakening' hs);
  | verum _ => by apply verum
  | imply₁ _ _ _ => by apply imply₁
  | imply₂ _ _ _ _ => by apply imply₂
  | conj₁ _ _ _ => by apply conj₁
  | conj₂ _ _ _ => by apply conj₂
  | conj₃ _ _ _ => by apply conj₃
  | disj₁ _ _ _ => by apply disj₁
  | disj₂ _ _ _ => by apply disj₂
  | disj₃ _ _ _ _ => by apply disj₃

instance : Hilbert.Minimal (· ⊢ᴾ[Λ] · : Theory α → Formula α → Type _) where
  axm          := axm;
  weakening'   := weakening';
  modus_ponens h₁ h₂ := by
    rename_i Γ₁ Γ₂ p q
    replace h₁ : (Γ₁ ∪ Γ₂) ⊢ᴾ[Λ] p ⟶ q := h₁.weakening' (by simp);
    replace h₂ : (Γ₁ ∪ Γ₂) ⊢ᴾ[Λ] p := h₂.weakening' (by simp);
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

private def dtrAux (Γ : Theory α) (p q : Formula α) : (Γ ⊢ᴾ[Λ] q) → (Γ \ {p} ⊢ᴾ[Λ] p ⟶ q)
  | verum _         => (imply₁ _ _ _) ⨀ (verum _)
  | imply₁ _ _ _    => (imply₁ _ _ _) ⨀ (imply₁ _ _ _)
  | imply₂ _ _ _ _  => (imply₁ _ _ _) ⨀ (imply₂ _ _ _ _)
  | conj₁ _ _ _     => (imply₁ _ _ _) ⨀ (conj₁ _ _ _)
  | conj₂ _ _ _     => (imply₁ _ _ _) ⨀ (conj₂ _ _ _)
  | conj₃ _ _ _     => (imply₁ _ _ _) ⨀ (conj₃ _ _ _)
  | disj₁ _ _ _     => (imply₁ _ _ _) ⨀ (disj₁ _ _ _)
  | disj₂ _ _ _     => (imply₁ _ _ _) ⨀ (disj₂ _ _ _)
  | disj₃ _ _ _ _   => (imply₁ _ _ _) ⨀ (disj₃ _ _ _ _)
  | @eaxm _ _ Γ q ih => (imply₁ _ _ _) ⨀ (eaxm (by assumption))
  | @axm _ _ Γ q ih => by
    by_cases h : p = q
    case pos => deduct
    case neg =>
      have d₁ : (Γ \ {p}) ⊢ᴾ[Λ] (q ⟶ p ⟶ q) := imply₁ _ q p
      have d₂ : (Γ \ {p}) ⊢ᴾ[Λ] q := axm (Set.mem_diff_singleton.mpr ⟨ih, Ne.symm h⟩)
      exact d₁ ⨀ d₂;
  | @modusPonens _ _ Γ a b h₁ h₂ =>
      have ih₁ : Γ \ {p} ⊢ᴾ[Λ] p ⟶ a ⟶ b := dtrAux Γ p (a ⟶ b) h₁
      have ih₂ : Γ \ {p} ⊢ᴾ[Λ] p ⟶ a := dtrAux Γ p a h₂
      have d₁ : Γ \ {p} ⊢ᴾ[Λ] (p ⟶ a) ⟶ p ⟶ b := Hilbert.imply₂ ⨀ ih₁;
      have d₂ : (Γ) \ {p} ⊢ᴾ[Λ] (p ⟶ a) := ih₂.weakening' (by simp)
      d₁ ⨀ d₂

def dtr {Γ : Theory α} {p q} (d : (insert p Γ) ⊢ᴾ[Λ] q) : (Γ ⊢ᴾ[Λ](p ⟶ q)) := by
  exact dtrAux (insert p Γ) p q d |> LO.Deduction.weakening' (by simp)

instance : Hilbert.HasDT (· ⊢ᴾ[Λ] · : Theory α → Formula α → Type _) := ⟨dtr⟩

def compact {Γ : Theory α} {p : Formula α} : (Γ ⊢ᴾ[Λ] p) → (Δ : { Δ : Context α | ↑Δ ⊆ Γ}) × Δ ⊢ᴾ[Λ] p
  | @axm _ _ Γ p h  => ⟨⟨{p}, by simpa⟩, axm (by simp)⟩
  | @eaxm _ _ Γ q ih => ⟨⟨∅, by simp⟩, eaxm (by assumption)⟩
  | @modusPonens _ _ Γ p q h₁ h₂ => by
      have ⟨⟨Δ₁, hs₁⟩, d₁⟩ := compact h₁
      have ⟨⟨Δ₂, hs₂⟩, d₂⟩ := compact h₂
      simp at hs₁ d₁ hs₂ d₂;
      exact ⟨
        ⟨Δ₁ ∪ Δ₂, by simp [hs₁, hs₂, Set.subset_union_of_subset_left, Set.subset_union_of_subset_right];⟩,
        by simpa using modus_ponens₂' (LO.Deduction.weakening' (by simp) d₁) (LO.Deduction.weakening' (by simp) d₂)
      ⟩
  | verum _         => ⟨⟨∅, by simp⟩, verum _⟩
  | imply₁ _ _ _    => ⟨⟨∅, by simp⟩, imply₁ _ _ _⟩
  | imply₂ _ _ _ _  => ⟨⟨∅, by simp⟩, imply₂ _ _ _ _⟩
  | conj₁ _ _ _     => ⟨⟨∅, by simp⟩, conj₁ _ _ _⟩
  | conj₂ _ _ _     => ⟨⟨∅, by simp⟩, conj₂ _ _ _⟩
  | conj₃ _ _ _     => ⟨⟨∅, by simp⟩, conj₃ _ _ _⟩
  | disj₁ _ _ _     => ⟨⟨∅, by simp⟩, disj₁ _ _ _⟩
  | disj₂ _ _ _     => ⟨⟨∅, by simp⟩, disj₂ _ _ _⟩
  | disj₃ _ _ _ _   => ⟨⟨∅, by simp⟩, disj₃ _ _ _ _⟩

infix:45 " ⊢ⁱ " => Deduction 𝐄𝐅𝐐
infix:45 " ⊢ⁱ! " => Deducible 𝐄𝐅𝐐
infix:45 " ⊬ⁱ! " => Undeducible 𝐄𝐅𝐐

instance : Hilbert.Intuitionistic (· ⊢ⁱ · : Theory α → Formula α → Type _) where
  axm          := axm;
  weakening'   := weakening';
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

infix:45 " ⊢ᶜ " => Deduction 𝐃𝐍𝐄
infix:45 " ⊢ᶜ! " => Deducible 𝐃𝐍𝐄
infix:45 " ⊬ᶜ! " => Undeducible 𝐃𝐍𝐄

instance : Hilbert.Classical (· ⊢ᶜ · : Theory α → Formula α → Type _) where
  axm          := axm;
  weakening'   := weakening';
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

instance : HasDT (· ⊢ᶜ · : Theory α → Formula α → Type _) := ⟨dtr⟩

/-- a.k.a. Glivenko's Theorem -/
theorem negnegEquivalence_Int_Classical : (Γ ⊢ⁱ! ~~p) ↔ (Γ ⊢ᶜ! p) := by
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

abbrev glivenko : (Γ ⊢ⁱ! ~~p) ↔ Γ ⊢ᶜ! p := negnegEquivalence_Int_Classical

theorem negEquivalence_int_classical : (Γ ⊢ⁱ! ~p) ↔ (Γ ⊢ᶜ! ~p) := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end Deduction

def AxiomSet.Disjunctive (Λ : AxiomSet α) := ∀ {p q}, (∅ ⊢ᴾ[Λ]! p ⋎ q) → (∅ ⊢ᴾ[Λ]! p) ∨ (∅ ⊢ᴾ[Λ]! q)


end LO.Propositional.Intuitionistic
