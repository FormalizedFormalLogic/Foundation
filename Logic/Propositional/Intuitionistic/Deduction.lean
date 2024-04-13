import Logic.Logic.System
import Logic.Propositional.Intuitionistic.Formula

namespace LO.Propositional.Intuitionistic

variable {α : Type u} [DecidableEq α]

inductive Deduction : Theory α → Formula α → Type _
  | axm {Γ p}                : p ∈ Γ → Deduction Γ p
  /-- **Remark**: This is stronger version. -/
  | modusPonens {Γ p q} : Deduction Γ (p ⟶ q) → Deduction Γ p → Deduction Γ q
  | verum Γ          : Deduction Γ ⊤
  | imply₁ Γ p q     : Deduction Γ (p ⟶ q ⟶ p)
  | imply₂ Γ p q r   : Deduction Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ Γ p q      : Deduction Γ (p ⋏ q ⟶ p)
  | conj₂ Γ p q      : Deduction Γ (p ⋏ q ⟶ q)
  | conj₃ Γ p q      : Deduction Γ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ Γ p q      : Deduction Γ (p ⟶ p ⋎ q)
  | disj₂ Γ p q      : Deduction Γ (q ⟶ p ⋎ q)
  | disj₃ Γ p q r    : Deduction Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | efq Γ p          : Deduction Γ (⊥ ⟶ p)

infix:45 " ⊢ᴵ " => Deduction

variable (Γ : Theory α) (p : Formula α)

/-
abbrev Deducible := Hilbert.Deducible (@Deduction α)
infix:45 " ⊢ᴵ! " => Deducible

abbrev Undeducible := Hilbert.Undeducible (@Deduction α)
infix:45 " ⊬ᴵ! " => Undeducible

abbrev Theory.Consistent := Hilbert.Consistent (@Deduction α) Γ
abbrev Theory.Inconsistent := Hilbert.Inconsistent (@Deduction α) Γ
-/

namespace Deduction

open Hilbert

variable {Γ : Theory α} {p q : Formula α}

def weakening' {Γ Δ} {p : Formula α} (hs : Γ ⊆ Δ) : Deduction Γ p → Deduction Δ p
  | axm h => axm (hs h)
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
  | efq _ _ => by apply efq

instance : System (Formula α) where
  turnstile := Deduction
  axm := axm
  weakening' := weakening'

instance : Hilbert.Intuitionistic (· ⊢ · : Theory α → Formula α → Type _) where
  axm          := axm;
  weakening'   := weakening';
  modus_ponens h₁ h₂ := by
    rename_i Γ₁ Γ₂ p q
    replace h₁ : (Γ₁ ∪ Γ₂) ⊢ p ⟶ q := h₁.weakening' (by simp);
    replace h₂ : (Γ₁ ∪ Γ₂) ⊢ p := h₂.weakening' (by simp);
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
  efq          := efq

private def dtrAux (Γ : Theory α) (p q) : Γ ⊢ q → (Γ \ {p}) ⊢ p ⟶ q
  | verum _         => (imply₁ _ _ _) ⨀ (verum _)
  | imply₁ _ _ _    => (imply₁ _ _ _) ⨀ (imply₁ _ _ _)
  | imply₂ _ _ _ _  => (imply₁ _ _ _) ⨀ (imply₂ _ _ _ _)
  | conj₁ _ _ _     => (imply₁ _ _ _) ⨀ (conj₁ _ _ _)
  | conj₂ _ _ _     => (imply₁ _ _ _) ⨀ (conj₂ _ _ _)
  | conj₃ _ _ _     => (imply₁ _ _ _) ⨀ (conj₃ _ _ _)
  | disj₁ _ _ _     => (imply₁ _ _ _) ⨀ (disj₁ _ _ _)
  | disj₂ _ _ _     => (imply₁ _ _ _) ⨀ (disj₂ _ _ _)
  | disj₃ _ _ _ _   => (imply₁ _ _ _) ⨀ (disj₃ _ _ _ _)
  | efq _ _         => (imply₁ _ _ _) ⨀ (efq _ _)
  | @axm _ Γ q ih => by
    by_cases h : p = q
    case pos => deduct
    case neg =>
      have d₁ : (Γ \ {p}) ⊢ (q ⟶ p ⟶ q) := by deduct
      have d₂ : (Γ \ {p}) ⊢ q := by deduct
      deduct
  | @modusPonens _ Γ a b h₁ h₂ =>
      have ih₁ : Γ \ {p} ⊢ p ⟶ a ⟶ b := dtrAux Γ p (a ⟶ b) h₁;
      have ih₂ : Γ \ {p} ⊢ p ⟶ a := dtrAux Γ p a h₂;
      have d₁ : Γ \ {p} ⊢ (p ⟶ a) ⟶ p ⟶ b := (by deduct) ⨀ ih₁;
      have d₂ : Γ \ {p} ⊢ (p ⟶ a) := ih₂.weakening' (by simp);
      d₁ ⨀ d₂

def dtr' {Γ : Theory α} {p q} (d : (insert p Γ) ⊢ q) : (Γ ⊢ (p ⟶ q)) := by
  exact dtrAux (insert p Γ) p q d |> LO.Deduction.weakening' (by simp)

instance : Hilbert.HasDT (· ⊢ · : Theory α → Formula α → Type _) := ⟨dtr'⟩

def compact {Γ : Theory α} {p} : Γ ⊢ p → (Δ : { Δ : Context α | ↑Δ ⊆ Γ}) × Δ ⊢ p
  | @axm _ Γ p h  => ⟨⟨{p}, by simpa⟩, axm (by simp)⟩
  | @modusPonens _ Γ p q h₁ h₂ => by
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
  | efq _ _         => ⟨⟨∅, by simp⟩, efq _ _⟩

instance : Hilbert.Compact (· ⊢ · : Theory α → Formula α → Type _) := ⟨compact⟩

end Deduction

end LO.Propositional.Intuitionistic
