import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Entailment.GL
import Mathlib.Tactic.TFAE


namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S}

protected class K4Loeb (𝓢 : S) extends Entailment.K4 𝓢, LoebRule 𝓢

namespace K4Loeb

variable [Entailment.K4Loeb 𝓢]

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


protected class K4Henkin (𝓢 : S) extends Entailment.K4 𝓢, HenkinRule 𝓢

namespace K4Henkin

variable [Entailment.K4Henkin 𝓢]

instance : LoebRule 𝓢 where
  loeb h := h ⨀ (henkin $ E_intro (axiomK' $ nec h) axiomFour);

end K4Henkin


protected class K4Hen (𝓢 : S) extends Entailment.K4 𝓢, HasAxiomHen 𝓢

namespace K4Hen

variable [Entailment.K4Hen 𝓢]

instance : HenkinRule 𝓢 where
  henkin h := (K_left h) ⨀ (axiomHen ⨀ nec h);

end K4Hen

end Entailment



namespace Hilbert

protected structure WithLoebRule (α : Type*) where
  axioms : Set (Formula α)

namespace WithLoebRule

variable {H H₁ H₂ : Hilbert.WithLoebRule α} {φ ψ : Formula α}

abbrev axiomInstances (H : Hilbert.WithLoebRule α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  . assumption;
  . use Substitution.id;
    simp;

inductive Deduction (H : Hilbert.WithLoebRule α) : (Formula α) → Prop
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | loeb {φ}      : Deduction H (□φ ➝ φ) → Deduction H φ
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

def Deduction.maxm' (h : φ ∈ H.axioms) : Deduction H φ := by
  apply Deduction.maxm;
  exact mem_axiomInstances_of_mem_axioms h;

def Deduction.subst {φ} (s) (h : Deduction H φ) : Deduction H (φ⟦s⟧) := by
  induction h with
  | imply₁ => apply imply₁;
  | imply₂ => apply imply₂;
  | ec => apply Deduction.ec;
  | mdp _ _ ihφψ ihφ => apply mdp ihφψ ihφ;
  | nec _ ihφ => apply nec; exact ihφ;
  | loeb _ ihφ => apply loeb; exact ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h;
    apply Deduction.maxm;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      simp;

abbrev logic (H : Hilbert.WithLoebRule α) : Logic α := H.Deduction

section

open Deduction

lemma iff_mem_logic : H.logic ⊢! φ ↔ Deduction H φ := by simp [logic]; rfl;

instance : Entailment.Lukasiewicz (H.logic) where
  mdp hφψ hφ := by
    constructor;
    apply Deduction.mdp;
    . exact PLift.down hφψ;
    . exact PLift.down hφ;
  imply₁ _ _ := by constructor; apply Deduction.imply₁;
  imply₂ _ _ _ := by constructor; apply Deduction.imply₂;
  elimContra _ _ := by constructor; apply Deduction.ec;

instance : Entailment.Cl (H.logic) where

instance : Entailment.HasDiaDuality H.logic := inferInstance

instance : Entailment.Necessitation H.logic where
  nec hφ := by
    constructor;
    apply Deduction.nec;
    exact PLift.down hφ

instance : Entailment.LoebRule H.logic where
  loeb h := by
    constructor;
    apply Deduction.loeb;
    exact PLift.down h

instance : H.logic.Substitution where
  subst s hφ := by
    constructor;
    apply Deduction.subst;
    exact PLift.down hφ

lemma maxm! (h : φ ∈ H.axiomInstances) : H.logic ⊢! φ := by
  apply iff_mem_logic.mpr;
  exact Deduction.maxm h;

lemma maxm'! (h : φ ∈ H.axioms) : H.logic ⊢! φ := by
  apply iff_mem_logic.mpr;
  exact Deduction.maxm' h;

protected lemma rec!
  {motive     : (φ : Formula α) → (H.logic ⊢! φ) → Sort}
  (maxm       : ∀ {φ : Formula α}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ : Formula α}, {hpq : H.logic ⊢! φ ➝ ψ} → {hp : H.logic ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (nec        : ∀ {φ : Formula α}, {hp : H.logic ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (nec! hp))
  (loeb       : ∀ {φ}, {hp : H.logic ⊢! □φ ➝ φ} → (ihp : motive (□φ ➝ φ) hp) → motive φ (loeb! hp))
  (imply₁     : ∀ {φ ψ : Formula α}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂     : ∀ {φ ψ χ : Formula α}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec         : ∀ {φ ψ : Formula α}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : H.logic ⊢! φ) → motive φ d := by
  rintro φ d;
  induction iff_mem_logic.mp d with
  | maxm h =>
    apply maxm h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ $ iff_mem_logic.mpr hφψ;
    . exact ihφ $ iff_mem_logic.mpr hφ;
  | nec hφ ihφ =>
    apply nec;
    exact ihφ $ iff_mem_logic.mpr hφ;
  | loeb hφ ihφ =>
    apply loeb;
    exact ihφ $ iff_mem_logic.mpr hφ;
  | imply₁ => apply imply₁;
  | imply₂ => apply imply₂;
  | ec => apply ec;

section

variable [DecidableEq α]

class HasK (H : Hilbert.WithLoebRule α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasK] : Entailment.HasAxiomK H.logic where
  K φ ψ := by
    constructor;
    apply maxm;
    use Axioms.K (.atom (HasK.p H)) (.atom (HasK.q H));
    constructor;
    . exact HasK.mem_K;
    . use (λ b => if (HasK.p H) = b then φ else if (HasK.q H) = b then ψ else (.atom b));
      simp [HasK.ne_pq];

class HasFour (H : Hilbert.WithLoebRule α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFour] : Entailment.HasAxiomFour H.logic where
  Four φ := by
    constructor;
    apply maxm;
    use Axioms.Four (.atom (HasFour.p H));
    constructor;
    . exact HasFour.mem_Four;
    . use (λ b => if (HasFour.p H) = b then φ else (.atom b));
      simp;

end

end


section

open Deduction

variable {H : Hilbert.WithLoebRule α} [DecidableEq α]

end

end WithLoebRule



protected structure WithHenkinRule (α : Type*) where
  axioms : Set (Formula α)

namespace WithHenkinRule

variable {H H₁ H₂ : Hilbert.WithHenkinRule α} {φ ψ : Formula α}

abbrev axiomInstances (H : Hilbert.WithHenkinRule α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  . assumption;
  . use Substitution.id;
    simp;

inductive Deduction (H : Hilbert.WithHenkinRule α) : (Formula α) → Prop
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | henkin {φ}    : Deduction H (□φ ⭤ φ) → Deduction H φ
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

def Deduction.maxm' (h : φ ∈ H.axioms) : Deduction H φ := by
  apply Deduction.maxm;
  exact mem_axiomInstances_of_mem_axioms h;

def Deduction.subst {φ} (s) (h : Deduction H φ) : Deduction H (φ⟦s⟧) := by
  induction h with
  | imply₁ => apply imply₁;
  | imply₂ => apply imply₂;
  | ec => apply Deduction.ec;
  | mdp _ _ ihφψ ihφ => apply mdp ihφψ ihφ;
  | nec _ ihφ => apply nec; exact ihφ;
  | henkin _ ihφ => apply henkin; exact ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h;
    apply Deduction.maxm;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      simp;

abbrev logic (H : Hilbert.WithHenkinRule α) : Logic α := H.Deduction

section

open Deduction

lemma iff_mem_logic : H.logic ⊢! φ ↔ Deduction H φ := by simp [logic]; rfl;

instance : Entailment.Lukasiewicz (H.logic) where
  mdp hφψ hφ := by
    constructor;
    apply Deduction.mdp;
    . exact PLift.down hφψ;
    . exact PLift.down hφ;
  imply₁ _ _ := by constructor; apply Deduction.imply₁;
  imply₂ _ _ _ := by constructor; apply Deduction.imply₂;
  elimContra _ _ := by constructor; apply Deduction.ec;

instance : Entailment.Cl (H.logic) where

instance : Entailment.HasDiaDuality H.logic := inferInstance

instance : Entailment.Necessitation H.logic where
  nec hφ := by
    constructor;
    apply Deduction.nec;
    exact PLift.down hφ

instance : Entailment.HenkinRule H.logic where
  henkin h := by
    constructor;
    apply Deduction.henkin;
    exact PLift.down h

instance : H.logic.Substitution where
  subst s hφ := by
    constructor;
    apply Deduction.subst;
    exact PLift.down hφ

lemma maxm! (h : φ ∈ H.axiomInstances) : H.logic ⊢! φ := by
  apply iff_mem_logic.mpr;
  exact Deduction.maxm h;

lemma maxm'! (h : φ ∈ H.axioms) : H.logic ⊢! φ := by
  apply iff_mem_logic.mpr;
  exact Deduction.maxm' h;

protected lemma rec!
  {motive     : (φ : Formula α) → (H.logic ⊢! φ) → Sort}
  (maxm       : ∀ {φ : Formula α}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ : Formula α}, {hpq : H.logic ⊢! φ ➝ ψ} → {hp : H.logic ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (nec        : ∀ {φ : Formula α}, {hp : H.logic ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (nec! hp))
  (henkin     : ∀ {φ}, {hp : H.logic ⊢! □φ ⭤ φ} → (ihp : motive (□φ ⭤ φ) hp) → motive φ (henkin! hp))
  (imply₁     : ∀ {φ ψ : Formula α}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂     : ∀ {φ ψ χ : Formula α}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec         : ∀ {φ ψ : Formula α}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : H.logic ⊢! φ) → motive φ d := by
  rintro φ d;
  induction iff_mem_logic.mp d with
  | maxm h =>
    apply maxm h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ $ iff_mem_logic.mpr hφψ;
    . exact ihφ $ iff_mem_logic.mpr hφ;
  | nec hφ ihφ =>
    apply nec;
    exact ihφ $ iff_mem_logic.mpr hφ;
  | henkin hφ ihφ =>
    apply henkin;
    exact ihφ $ iff_mem_logic.mpr hφ;
  | imply₁ => apply imply₁;
  | imply₂ => apply imply₂;
  | ec => apply ec;

section

variable [DecidableEq α]

class HasK (H : Hilbert.WithHenkinRule α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasK] : Entailment.HasAxiomK H.logic where
  K φ ψ := by
    constructor;
    apply maxm;
    use Axioms.K (.atom (HasK.p H)) (.atom (HasK.q H));
    constructor;
    . exact HasK.mem_K;
    . use (λ b => if (HasK.p H) = b then φ else if (HasK.q H) = b then ψ else (.atom b));
      simp [HasK.ne_pq];

class HasFour (H : Hilbert.WithHenkinRule α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFour] : Entailment.HasAxiomFour H.logic where
  Four φ := by
    constructor;
    apply maxm;
    use Axioms.Four (.atom (HasFour.p H));
    constructor;
    . exact HasFour.mem_Four;
    . use (λ b => if (HasFour.p H) = b then φ else (.atom b));
      simp;

end

end


section

open Deduction

variable {H : Hilbert.WithHenkinRule α} [DecidableEq α]

end

end WithHenkinRule

end Hilbert


protected abbrev Hilbert.K4Hen : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Hen (.atom 0)}⟩
protected abbrev Logic.K4Hen := Hilbert.K4Hen.logic
instance : (Hilbert.K4Hen).HasK where p := 0; q := 1;
instance : (Hilbert.K4Hen).HasFour where p := 0
instance : (Hilbert.K4Hen).HasHen where p := 0
instance : Entailment.K4Hen (Logic.K4Hen) where

protected abbrev Hilbert.K4Loeb : Hilbert.WithLoebRule ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.K4Loeb := Hilbert.K4Loeb.logic
instance : (Hilbert.K4Loeb).HasK where p := 0; q := 1;
instance : (Hilbert.K4Loeb).HasFour where p := 0
instance : Entailment.K4Loeb (Logic.K4Loeb) where

protected abbrev Hilbert.K4Henkin : Hilbert.WithHenkinRule ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.K4Henkin := Hilbert.K4Henkin.logic
instance : (Hilbert.K4Henkin).HasK where p := 0; q := 1;
instance : (Hilbert.K4Henkin).HasFour where p := 0
instance : Entailment.K4Henkin (Logic.K4Henkin) where

theorem provable_GL_TFAE : [
  Logic.GL ⊢! φ,
  Logic.K4Loeb ⊢! φ,
  Logic.K4Henkin ⊢! φ,
  Logic.K4Hen ⊢! φ
].TFAE := by
  tfae_have 1 → 2 := by
    intro h;
    induction h with
    | maxm h =>  rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  tfae_have 2 → 3 := by
    clear * -;
    intro h;
    induction h using Hilbert.WithLoebRule.rec! with
    | maxm h => apply Hilbert.WithHenkinRule.maxm! h;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | loeb ihφ => exact loeb! ihφ;
    | _ => simp;
  tfae_have 3 → 4 := by
    clear * -;
    intro h;
    induction h using Hilbert.WithHenkinRule.rec! with
    | maxm h => rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | henkin ihφ => exact henkin! ihφ;
    | _ => simp;
  tfae_have 4 → 1 := by
    clear * -;
    intro h;
    induction h with
    | maxm h => rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  tfae_finish;

instance : (Logic.GL) ≊ (Logic.K4Loeb) := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  apply provable_GL_TFAE.out 0 1;

instance : (Logic.GL) ≊ (Logic.K4Henkin) := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  apply provable_GL_TFAE.out 0 2;

instance : (Logic.GL) ≊ (Logic.K4Hen) := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  apply provable_GL_TFAE.out 0 3;


end LO.Modal
