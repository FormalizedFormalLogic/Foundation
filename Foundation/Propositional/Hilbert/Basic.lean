import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Propositional.Formula
import Foundation.Propositional.Logic.Basic
import Foundation.Logic.Disjunctive

namespace LO.Propositional

open LO.Entailment LO.Modal.Entailment

variable {α : Type u}

structure Hilbert (α) where
  axioms : Set (Formula α)

namespace Hilbert

variable {H H₁ H₂ : Hilbert α}

abbrev axiomInstances (H : Hilbert α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  . assumption;
  . use Substitution.id;
    simp;

variable {H : Hilbert α}

inductive Deduction (H : Hilbert α) : Formula α → Prop
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | verum         : Deduction H $ ⊤
  | implyS φ ψ    : Deduction H $ φ ➝ ψ ➝ φ
  | implyK φ ψ χ  : Deduction H $ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | andElimL φ ψ  : Deduction H $ φ ⋏ ψ ➝ φ
  | andElimR φ ψ  : Deduction H $ φ ⋏ ψ ➝ ψ
  | K_intro φ ψ   : Deduction H $ φ ➝ ψ ➝ φ ⋏ ψ
  | orIntroL φ ψ  : Deduction H $ φ ➝ φ ⋎ ψ
  | orIntroR φ ψ  : Deduction H $ ψ ➝ φ ⋎ ψ
  | orElim φ ψ χ  : Deduction H $ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

def Deduction.maxm' {H : Hilbert α} {φ} (h : φ ∈ H.axioms) : Deduction H φ := by
  apply Deduction.maxm;
  exact mem_axiomInstances_of_mem_axioms h;

def Deduction.subst {φ} (s) (h : Deduction H φ) : Deduction H (φ⟦s⟧) := by
  induction h with
  | implyK => apply Deduction.implyK;
  | implyS => apply Deduction.implyS;
  | andElimL => apply Deduction.andElimL;
  | andElimR => apply Deduction.andElimR;
  | orIntroL => apply Deduction.orIntroL;
  | orIntroR => apply Deduction.orIntroR;
  | orElim => apply Deduction.orElim;
  | verum => apply Deduction.verum;
  | K_intro => apply Deduction.K_intro;
  | mdp _ _ ihφψ ihφ => apply Deduction.mdp ihφψ ihφ;
  | maxm h =>
    apply Deduction.maxm;
    obtain ⟨ψ, h, s', rfl⟩ := h;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      simp;


abbrev logic (H : Hilbert α) : Logic α := H.Deduction

section

variable {H H₁ H₂ : Hilbert α} {φ ψ : Formula α}

lemma iff_mem_logic : H.logic ⊢! φ ↔ Deduction H φ := by simp [logic]; rfl;

instance : Entailment.ModusPonens H.logic where
  mdp hφψ hφ := by
    constructor;
    apply Deduction.mdp;
    . exact PLift.down hφψ;
    . exact PLift.down hφ;
instance : Entailment.HasAxiomImply₁ H.logic where
  imply₁ _ _ := by constructor; apply Deduction.implyS;
instance : Entailment.HasAxiomImply₂ H.logic where
  imply₂ _ _ _ := by constructor; apply Deduction.implyK;
instance : Entailment.HasAxiomAndInst H.logic where
  and₃ _ _ := by constructor; apply Deduction.K_intro;

instance : Entailment.Minimal (H.logic) where
  verum := by constructor; apply Deduction.verum;
  and₁ _ _ := by constructor; apply Deduction.andElimL;
  and₂ _ _ := by constructor; apply Deduction.andElimR;
  or₁ _ _ := by constructor; apply Deduction.orIntroL;
  or₂ _ _ := by constructor; apply Deduction.orIntroR;
  or₃ _ _ _ := by constructor; apply Deduction.orElim;

instance : H.logic.Substitution where
  subst! s hφ := by
    constructor;
    constructor;
    apply Deduction.subst;
    exact PLift.down hφ.some

lemma maxm! (h : φ ∈ H.axiomInstances) : H.logic ⊢! φ := by
  apply iff_mem_logic.mpr;
  exact Deduction.maxm h;

lemma maxm'! (h : φ ∈ H.axioms) : H.logic ⊢! φ := by
  apply iff_mem_logic.mpr;
  exact Deduction.maxm' h;

@[induction_eliminator]
protected lemma rec!
  {motive   : (φ : Formula α) → (H.logic ⊢! φ) → Sort}
  (maxm     : ∀ {φ : Formula α}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp      : ∀ {φ ψ : Formula α}, {hpq : H.logic ⊢! φ ➝ ψ} → {hp : H.logic ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (verum    : motive ⊤ verum!)
  (implyS   : ∀ {φ ψ},   motive (Axioms.Imply₁ φ ψ) $ by simp)
  (implyK   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (andElimL : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ φ) $ by simp)
  (andElimR : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ ψ) $ by simp)
  (K_intro  : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ ⋏ ψ) $ by simp)
  (orIntroL : ∀ {φ ψ},   motive (φ ➝ φ ⋎ ψ) $ by simp)
  (orIntroR : ∀ {φ ψ},   motive (ψ ➝ φ ⋎ ψ) $ by simp)
  (orElim   : ∀ {φ ψ χ}, motive ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ φ ⋎ ψ ➝ χ) $ by simp)
  : ∀ {φ}, (d : H.logic ⊢! φ) → motive φ d := by
  rintro φ d;
  induction iff_mem_logic.mp d with
  | maxm h =>
    apply maxm h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ $ iff_mem_logic.mpr hφψ;
    . exact ihφ $ iff_mem_logic.mpr hφ;
  | verum => simpa;
  | implyS => apply implyS;
  | implyK => apply implyK;
  | andElimL => apply andElimL;
  | andElimR => apply andElimR;
  | K_intro => apply K_intro;
  | orIntroL => apply orIntroL;
  | orIntroR => apply orIntroR;
  | orElim => apply orElim;

lemma weakerThan_of_subset_axioms (hs : H₁.axioms ⊆ H₂.axioms) : H₁.logic ⪯ H₂.logic := by
  apply weakerThan_iff.mpr;
  intro _ h;
  induction h with
  | maxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    apply H₂.logic.subst! s;
    exact maxm'! $ hs h;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂
  | _ => simp;

lemma weakerThan_of_provable_axiomInstances (hs : H₂.logic ⊢!* H₁.axiomInstances) : H₁.logic ⪯ H₂.logic := by
  apply weakerThan_iff.mpr;
  intro _ h;
  induction h with
  | maxm h => exact hs h;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂
  | _ => simp;

lemma weakerThan_of_provable_axioms (hs : H₂.logic ⊢!* H₁.axioms) : H₁.logic ⪯ H₂.logic := by
  apply weakerThan_of_provable_axiomInstances;
  rintro φ ⟨ψ, h, ⟨s, rfl⟩⟩;
  exact H₂.logic.subst! s (hs h);

end

end Hilbert

end LO.Propositional
