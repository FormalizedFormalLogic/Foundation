import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Entailment.GL
import Mathlib.Tactic.TFAE


namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S}

protected class Modal.K4Loeb (𝓢 : S) extends Entailment.Modal.K4 𝓢, LoebRule 𝓢

namespace K4Loeb

variable [Entailment.Modal.K4Loeb 𝓢]

protected def axiomL : 𝓢 ⊢ Axioms.L φ := by
  dsimp [Axioms.L];
  generalize e : □(□φ ➝ φ) ➝ □φ = ψ;
  have d₁ : [□(□φ ➝ φ), □ψ] ⊢[𝓢] □□(□φ ➝ φ) ➝ □□φ := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₂ : [□(□φ ➝ φ), □ψ] ⊢[𝓢] □□φ ➝ □φ := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₃ : 𝓢 ⊢ □(□φ ➝ φ) ➝ □□(□φ ➝ φ) := axiomFour;
  have : 𝓢 ⊢ □ψ ➝ ψ := by
    nth_rw 2 [←e]; apply deduct'; apply deduct;
    exact d₂ ⨀ (d₁ ⨀ ((of d₃) ⨀ (FiniteContext.byAxm)));
  exact loeb this;
instance : HasAxiomL 𝓢 := ⟨fun _ ↦ K4Loeb.axiomL⟩

end K4Loeb


protected class Modal.K4Henkin (𝓢 : S) extends Entailment.Modal.K4 𝓢, HenkinRule 𝓢

namespace K4Henkin

variable [Entailment.Modal.K4Henkin 𝓢]

instance : LoebRule 𝓢 where
  loeb h := h ⨀ (henkin $ E_intro (axiomK' $ nec h) axiomFour);

end K4Henkin


protected class Modal.K4H (𝓢 : S) extends Entailment.Modal.K4 𝓢, HasAxiomH 𝓢

namespace K4H

variable [Entailment.Modal.K4H 𝓢]

instance : HenkinRule 𝓢 where
  henkin h := (K_left h) ⨀ (axiomH ⨀ nec h);

end K4H

end LO.Entailment



namespace LO.Modal

namespace Hilbert

open Entailment

variable {α : Type*}

protected structure WithLoebRule (α : Type*) where
  axioms : Set (Formula α)

namespace WithLoebRule

abbrev axiomInstances (H : Hilbert.WithLoebRule α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

inductive Deduction (H : Hilbert.WithLoebRule α) : (Formula α) → Type _
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | loeb {φ}      : Deduction H (□φ ➝ φ) → Deduction H φ
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

namespace Deduction

variable {H H₁ H₂ : Hilbert.WithLoebRule α}

instance : Entailment (Formula α) (Hilbert.WithLoebRule α) := ⟨Deduction⟩

instance : Entailment.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elimContra := ec

instance : Entailment.Cl H where

instance : Entailment.HasDiaDuality H := inferInstance

instance : Entailment.Necessitation H := ⟨nec⟩

instance : Entailment.LoebRule H := ⟨loeb⟩

lemma maxm! {φ} (h : φ ∈ H.axiomInstances) : H ⊢! φ := ⟨maxm h⟩

noncomputable def rec!
  {motive      : (φ : Formula α) → H ⊢! φ → Sort*}
  (maxm       : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (nec        : ∀ {φ}, {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (nec! hp))
  (loeb       : ∀ {φ}, {hp : H ⊢! □φ ➝ φ} → (ihp : motive (□φ ➝ φ) hp) → motive φ (loeb! hp))
  (imply₁     : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ ⟨imply₁ φ ψ⟩)
  (imply₂     : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ ⟨imply₂ φ ψ χ⟩)
  (ec : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact maxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec hp ih => exact nec (ih ⟨hp⟩)
  | loeb hp ih => exact loeb (ih ⟨hp⟩)
  | _ => aesop;

def subst! {φ} (s) (h : H ⊢! φ) : H ⊢! φ⟦s⟧ := by
  induction h using Deduction.rec! with
  | imply₁ => simp;
  | imply₂ => simp;
  | ec => simp;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | nec ihφ => exact nec! ihφ;
  | loeb ihφ => exact loeb! ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h;
    apply maxm!;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      simp;

end Deduction


section

open Deduction

variable {H : Hilbert.WithLoebRule α} [DecidableEq α]

class HasK (H : Hilbert.WithLoebRule α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [hK : H.HasK] : Entailment.HasAxiomK H where
  K φ ψ := by
    apply maxm;
    use Axioms.K (.atom hK.p) (.atom hK.q);
    constructor;
    . exact hK.mem_K;
    . use (λ b => if hK.p = b then φ else if hK.q = b then ψ else (.atom b));
      simp [hK.ne_pq];

class HasFour (H : Hilbert.WithLoebRule α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [hFour : H.HasFour] : Entailment.HasAxiomFour H where
  Four φ := by
    apply maxm;
    use Axioms.Four (.atom hFour.p);
    constructor;
    . exact hFour.mem_Four;
    . use (λ b => if hFour.p = b then φ else (.atom b));
      simp;

end

end WithLoebRule


protected structure WithHenkinRule (α : Type*) where
  axioms : Set (Formula α)

namespace WithHenkinRule

abbrev axiomInstances (H : Hilbert.WithHenkinRule α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

inductive Deduction (H : Hilbert.WithHenkinRule α) : (Formula α) → Type _
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | henkin {φ}    : Deduction H (□φ ⭤ φ) → Deduction H φ
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

namespace Deduction

variable {H H₁ H₂ : Hilbert.WithHenkinRule α}

instance : Entailment (Formula α) (Hilbert.WithHenkinRule α) := ⟨Deduction⟩

instance : Entailment.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elimContra := ec

instance : Entailment.Cl H where

instance : Entailment.HasDiaDuality H := inferInstance

instance : Entailment.Necessitation H := ⟨nec⟩

instance : Entailment.HenkinRule H := ⟨henkin⟩

lemma maxm! {φ} (h : φ ∈ H.axiomInstances) : H ⊢! φ := ⟨maxm h⟩

noncomputable def rec!
  {motive      : (φ : Formula α) → H ⊢! φ → Sort*}
  (maxm       : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (nec        : ∀ {φ}, {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (nec! hp))
  (henkin     : ∀ {φ}, {hp : H ⊢! □φ ⭤ φ} → (ihp : motive (□φ ⭤ φ) hp) → motive φ (henkin! hp))
  (imply₁     : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ ⟨imply₁ φ ψ⟩)
  (imply₂     : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ ⟨imply₂ φ ψ χ⟩)
  (ec : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact maxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec hp ih => exact nec (ih ⟨hp⟩)
  | henkin hp ih => exact henkin (ih ⟨hp⟩)
  | _ => aesop;

lemma subst! {φ} (s) (h : H ⊢! φ) : H ⊢! φ⟦s⟧ := by
  induction h using Deduction.rec! with
  | imply₁ => simp;
  | imply₂ => simp;
  | ec => simp;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | nec ihφ => exact nec! ihφ;
  | henkin ihφ => exact henkin! ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h;
    apply maxm!;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      simp;

end Deduction

section

open Deduction

variable {H : Hilbert.WithHenkinRule α} [DecidableEq α]

class HasK (H : Hilbert.WithHenkinRule α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [hK : H.HasK] : Entailment.HasAxiomK H where
  K φ ψ := by
    apply maxm;
    use Axioms.K (.atom hK.p) (.atom hK.q);
    constructor;
    . exact hK.mem_K;
    . use (λ b => if hK.p = b then φ else if hK.q = b then ψ else (.atom b));
      simp [hK.ne_pq];

class HasFour (H : Hilbert.WithHenkinRule α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [hFour : H.HasFour] : Entailment.HasAxiomFour H where
  Four φ := by
    apply maxm;
    use Axioms.Four (.atom hFour.p);
    constructor;
    . exact hFour.mem_Four;
    . use (λ b => if hFour.p = b then φ else (.atom b));
      simp;

end

end WithHenkinRule


protected abbrev K4H : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.H (.atom 0)}⟩
instance : (Hilbert.K4H).HasK where p := 0; q := 1;
instance : (Hilbert.K4H).HasFour where p := 0
instance : (Hilbert.K4H).HasH where p := 0
instance : Entailment.Modal.K4H (Hilbert.K4H) where

protected abbrev K4Loeb : Hilbert.WithLoebRule ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.K4Loeb).HasK where p := 0; q := 1;
instance : (Hilbert.K4Loeb).HasFour where p := 0
instance : Entailment.Modal.K4Loeb (Hilbert.K4Loeb) where

protected abbrev K4Henkin : Hilbert.WithHenkinRule ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.K4Henkin).HasK where p := 0; q := 1;
instance : (Hilbert.K4Henkin).HasFour where p := 0
instance : Entailment.Modal.K4Henkin (Hilbert.K4Henkin) where

theorem provable_GL_TFAE : [
    Hilbert.GL ⊢! φ,
    Hilbert.K4Loeb ⊢! φ,
    Hilbert.K4Henkin ⊢! φ,
    Hilbert.K4H ⊢! φ
  ].TFAE := by
  tfae_have 1 → 2 := by
    clear * -;
    intro h;
    induction h using Hilbert.Deduction.rec! with
    | maxm h =>  rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp only [axiomK!, axiomL!];
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  tfae_have 2 → 3 := by
    clear * -;
    intro h;
    induction h using Hilbert.WithLoebRule.Deduction.rec! with
    | maxm h => apply Hilbert.WithHenkinRule.Deduction.maxm! h;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | loeb ihφ => exact loeb! ihφ;
    | _ => simp;
  tfae_have 3 → 4 := by
    clear * -;
    intro h;
    induction h using Hilbert.WithHenkinRule.Deduction.rec! with
    | maxm h => rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp only [axiomK!, axiomFour!];
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | henkin ihφ => exact henkin! ihφ;
    | _ => simp;
  tfae_have 4 → 1 := by
    clear * -;
    intro h;
    induction h using Hilbert.Deduction.rec! with
    | maxm h => rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp only [axiomK!, axiomFour!, axiomH!];
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  tfae_finish;

end Hilbert

end LO.Modal
