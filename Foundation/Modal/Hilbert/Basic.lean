import Foundation.Modal.Formula
import Foundation.Modal.System.K
import Foundation.Logic.HilbertStyle.Lukasiewicz

namespace LO.Modal

open System

variable {α : Type*}

section

/-- instance of inference rule -/
structure Hilbert.InferenceRule (α : Type*) where
  antecedents : List (Formula α)
  consequence : Formula α
  /--
  Empty antecedent rule can be simply regarded as axiom rule.
  However, union of all these rules including to `Hilbert.rules` would be too complex for implementation and induction,
  so more than one antecedent is required.
  -/
  antecedents_nonempty : antecedents ≠ [] := by simp

namespace Hilbert.InferenceRule

abbrev Necessitation (φ : Formula α) : InferenceRule α := ⟨[φ], □φ, by simp⟩
abbrev Necessitation.set : Set (InferenceRule α) := { Necessitation φ | φ }
notation "⟮Nec⟯" => Necessitation.set

abbrev LoebRule (φ : Formula α) : InferenceRule α := ⟨[□φ ➝ φ], φ, by simp⟩
abbrev LoebRule.set : Set (InferenceRule α) := { LoebRule φ | φ }
notation "⟮Loeb⟯" => LoebRule.set

abbrev HenkinRule (φ : Formula α) : InferenceRule α := ⟨[□φ ⭤ φ], φ, by simp⟩
abbrev HenkinRule.set : Set (InferenceRule α) := { HenkinRule φ | φ }
notation "⟮Henkin⟯" => HenkinRule.set

end Hilbert.InferenceRule

end


structure Hilbert (α : Type*) where
  axioms : FormulaSet α
  rules : Set (Hilbert.InferenceRule α)


variable {H H₁ H₂ : Hilbert α}

inductive Hilbert.Deduction (H : Hilbert α) : (Formula α) → Type _
  | maxm {φ}     : φ ∈ H.axioms → Deduction H φ
  | rule {rl}    : rl ∈ H.rules → (∀ {φ}, φ ∈ rl.antecedents → Deduction H φ) → Deduction H rl.consequence
  | mdp {φ ψ}    : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | imply₁ φ ψ   : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ       : Deduction H $ Axioms.ElimContra φ ψ

namespace Hilbert.Deduction

instance : System (Formula α) (Hilbert α) := ⟨Deduction⟩

instance : System.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elim_contra := ec

instance : System.Classical H where

instance : System.HasDiaDuality H := inferInstance

lemma maxm! {φ} (h : φ ∈ H.axioms) : H ⊢! φ := ⟨maxm h⟩

end Hilbert.Deduction


namespace Hilbert

open Deduction

class HasNecessitation (H : Hilbert α) where
  has_necessitation : ⟮Nec⟯ ⊆ H.rules := by aesop

instance [HasNecessitation H] : System.Necessitation H where
  nec := @λ φ d => rule (show { antecedents := [φ], consequence := □φ } ∈ H.rules by apply HasNecessitation.has_necessitation; simp_all) (by aesop);


class HasLoebRule (H : Hilbert α) where
  has_loeb : ⟮Loeb⟯ ⊆ H.rules := by aesop

instance [HasLoebRule H] : System.LoebRule H where
  loeb := @λ φ d => rule (show { antecedents := [□φ ➝ φ], consequence := φ } ∈ H.rules by apply HasLoebRule.has_loeb; simp_all) (by aesop);


class HasHenkinRule (H : Hilbert α) where
  has_henkin : ⟮Henkin⟯ ⊆ H.rules := by aesop

instance [HasHenkinRule H] : System.HenkinRule H where
  henkin := @λ φ d => rule (show { antecedents := [□φ ⭤ φ], consequence := φ } ∈ H.rules by apply HasHenkinRule.has_henkin; simp_all) (by aesop);


class HasNecOnly (H : Hilbert α) where
  has_necessitation_only : H.rules = ⟮Nec⟯ := by rfl

instance [h : HasNecOnly H] : H.HasNecessitation where
  has_necessitation := by rw [h.has_necessitation_only]


class HasAxiomK (H : Hilbert α) where
  has_axiomK : 𝗞 ⊆ H.axioms := by aesop

instance [HasAxiomK H] : System.HasAxiomK H where
  K _ _ := maxm (by apply HasAxiomK.has_axiomK; simp_all)

class IsNormal (H : Hilbert α) extends H.HasNecOnly, H.HasAxiomK where

instance {H : Hilbert α} [H.IsNormal] : System.K H where


namespace Deduction

variable {H : Hilbert α}

noncomputable def inducition!
  {motive  : (φ : Formula α) → H ⊢! φ → Sort*}
  (hRules  : (r : InferenceRule α) → (hr : r ∈ H.rules) →
             (hant : ∀ {φ}, φ ∈ r.antecedents → H ⊢! φ) →
             (ih : ∀ {φ}, (hp : φ ∈ r.antecedents) →
             motive φ (hant hp)) → motive r.consequence ⟨rule hr (λ hp => (hant hp).some)⟩)
  (hMaxm     : ∀ {φ}, (h : φ ∈ H.axioms) → motive φ ⟨maxm h⟩)
  (hMdp      : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ ⟨mdp hpq.some hp.some⟩)
  (hImply₁     : ∀ {φ ψ}, motive (φ ➝ ψ ➝ φ) $ ⟨imply₁ φ ψ⟩)
  (hImply₂     : ∀ {φ ψ χ}, motive ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) $ ⟨imply₂ φ ψ χ⟩)
  (hElimContra : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | rule hr h ih => apply hRules _ hr; intro φ hp; exact ih hp ⟨h hp⟩;
  | imply₁ => exact hImply₁
  | imply₂ => exact hImply₂
  | ec => exact hElimContra

/-- Useful induction for normal modal logic. -/
noncomputable def inducition_with_necOnly! [H.HasNecOnly]
  {motive  : (φ : Formula α) → H ⊢! φ → Prop}
  (hMaxm   : ∀ {φ}, (h : φ ∈ H.axioms) → motive φ ⟨maxm h⟩)
  (hMdp    : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (hpq ⨀ hp))
  (hNec    : ∀ {φ}, {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (System.nec! hp))
  (hImply₁   : ∀ {φ ψ}, motive (φ ➝ ψ ➝ φ) $ ⟨imply₁ φ ψ⟩)
  (hImply₂   : ∀ {φ ψ χ}, motive ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) $ ⟨imply₂ φ ψ χ⟩)
  (hElimContra : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d using Deduction.inducition! with
  | hMaxm h => exact hMaxm h
  | hMdp ihpq ihp => exact hMdp (ihpq) (ihp);
  | hRules rl hrl hant ih =>
    rw [HasNecOnly.has_necessitation_only] at hrl;
    obtain ⟨φ, rfl⟩ := hrl;
    exact @hNec φ (hant (by simp)) $ ih (by simp);
  | hImply₁ => exact hImply₁
  | hImply₂ => exact hImply₂
  | hElimContra => exact hElimContra

end Deduction

variable {H H₁ H₂ : Hilbert α}

abbrev theorems (H : Hilbert α) := System.theory H

abbrev Consistent (H : Hilbert α) := System.Consistent H

lemma normal_weakerThan_of_maxm [H₁.IsNormal] [H₂.IsNormal]
  (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axioms → H₂ ⊢! φ)
  : H₁ ≤ₛ H₂ := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => exact hMaxm hp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec ihp => exact nec! ihp;
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra!

lemma normal_weakerThan_of_subset [H₁.IsNormal] [H₂.IsNormal] (hSubset : H₁.axioms ⊆ H₂.axioms)
  : H₁ ≤ₛ H₂ := by
  apply normal_weakerThan_of_maxm;
  intro φ hp;
  exact ⟨Deduction.maxm $ hSubset hp⟩;

end Hilbert

end LO.Modal
