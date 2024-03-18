import Logic.Logic.HilbertStyle2
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

abbrev Deducible := Hilbert.Deducible (@Deduction α)
infix:45 " ⊢ᴵ! " => Deducible

abbrev Undeducible := Hilbert.Undeducible (@Deduction α)
infix:45 " ⊬ᴵ! " => Undeducible

abbrev Theory.Consistent := Hilbert.Consistent (@Deduction α) Γ
abbrev Theory.Inconsistent := Hilbert.Inconsistent (@Deduction α) Γ

namespace Deduction

open Hilbert

variable {Γ : Theory α} {p q : Formula α}

def weakening' {Γ Δ} {p : Formula α} (hs : Γ ⊆ Δ) : (Γ ⊢ᴵ p) → (Δ ⊢ᴵ p)
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

instance : Hilbert.Intuitionistic (@Deduction α) where
  axm          := axm;
  weakening'   := weakening';
  modus_ponens h₁ h₂ := by
    rename_i Γ₁ Γ₂ p q
    replace h₁ : (Γ₁ ∪ Γ₂) ⊢ᴵ p ⟶ q := h₁.weakening' (by simp);
    replace h₂ : (Γ₁ ∪ Γ₂) ⊢ᴵ p := h₂.weakening' (by simp);
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

private def dtrAux (Γ : Theory α) (p q) : (Γ ⊢ᴵ q) → ((Γ \ {p}) ⊢ᴵ (p ⟶ q))
  | verum _         => modus_ponens' (imply₁ _ _ _) (verum _)
  | imply₁ _ _ _    => modus_ponens' (imply₁ _ _ _) (imply₁ _ _ _)
  | imply₂ _ _ _ _  => modus_ponens' (imply₁ _ _ _) (imply₂ _ _ _ _)
  | conj₁ _ _ _     => modus_ponens' (imply₁ _ _ _) (conj₁ _ _ _)
  | conj₂ _ _ _     => modus_ponens' (imply₁ _ _ _) (conj₂ _ _ _)
  | conj₃ _ _ _     => modus_ponens' (imply₁ _ _ _) (conj₃ _ _ _)
  | disj₁ _ _ _     => modus_ponens' (imply₁ _ _ _) (disj₁ _ _ _)
  | disj₂ _ _ _     => modus_ponens' (imply₁ _ _ _) (disj₂ _ _ _)
  | disj₃ _ _ _ _   => modus_ponens' (imply₁ _ _ _) (disj₃ _ _ _ _)
  | efq _ _         => modus_ponens' (imply₁ _ _ _) (efq _ _)
  | @axm _ Γ q ih => by
    by_cases h : p = q
    case pos =>
      simpa [h] using Hilbert.imp_id (Γ \ {p}) p;
    case neg =>
      have d₁ : (Γ \ {p}) ⊢ᴵ (q ⟶ p ⟶ q) := imply₁ _ q p
      have d₂ : (Γ \ {p}) ⊢ᴵ q := axm (Set.mem_diff_singleton.mpr ⟨ih, Ne.symm h⟩)
      exact modus_ponens' d₁ d₂;
  | @modusPonens _ Γ a b h₁ h₂ =>
      have ih₁ : Γ \ {p} ⊢ᴵ p ⟶ a ⟶ b := dtrAux Γ p (a ⟶ b) h₁
      have ih₂ : Γ \ {p} ⊢ᴵ p ⟶ a := dtrAux Γ p a h₂
      have d₁ : ((Γ) \ {p}) ⊢ᴵ (p ⟶ a) ⟶ p ⟶ b := modus_ponens' (imply₂ _ p a b) ih₁ |>.weakening' (by simp)
      have d₂ : ((Γ) \ {p}) ⊢ᴵ (p ⟶ a) := ih₂.weakening' (by simp)
      modus_ponens' d₁ d₂

def dtr {Γ : Theory α} {p q} (d : (insert p Γ) ⊢ᴵ q) : (Γ ⊢ᴵ (p ⟶ q)) := by
  exact dtrAux (insert p Γ) p q d |>.weakening' (by simp);

instance : Hilbert.HasDT (@Deduction α) := ⟨dtr⟩

def compact {Γ : Theory α} {p} : (Γ ⊢ᴵ p) → (Δ : { Δ : Context α | ↑Δ ⊆ Γ}) × (Δ ⊢ᴵ p)
  | @axm _ Γ p h  => ⟨⟨{p}, by simpa⟩, axm (by simp)⟩
  | @modusPonens _ Γ p q h₁ h₂ => by
      have ⟨⟨Δ₁, hs₁⟩, d₁⟩ := h₁.compact;
      have ⟨⟨Δ₂, hs₂⟩, d₂⟩ := h₂.compact;
      simp at hs₁ d₁ hs₂ d₂;
      exact ⟨
        ⟨Δ₁ ∪ Δ₂, by simp [hs₁, hs₂, Set.subset_union_of_subset_left, Set.subset_union_of_subset_right];⟩,
        by simpa using modus_ponens' (d₁.weakening' (by simp)) (d₂.weakening' (by simp));
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

instance : Hilbert.Compact (@Deduction α) := ⟨compact⟩

end Deduction

end LO.Propositional.Intuitionistic
