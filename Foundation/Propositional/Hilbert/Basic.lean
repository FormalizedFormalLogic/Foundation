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
  use φ
  constructor
  . assumption
  . use Substitution.id
    simp

variable {H : Hilbert α}

inductive Deduction (H : Hilbert α) : Formula α → Type u
  | axm {φ} (s : Substitution _) : φ ∈ H.axioms → Deduction H (φ⟦s⟧)
  | mdp {φ ψ}                    : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | verum                        : Deduction H $ ⊤
  | implyS φ ψ                   : Deduction H $ φ ➝ ψ ➝ φ
  | implyK φ ψ χ                 : Deduction H $ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | andElimL φ ψ                 : Deduction H $ φ ⋏ ψ ➝ φ
  | andElimR φ ψ                 : Deduction H $ φ ⋏ ψ ➝ ψ
  | K_intro φ ψ                  : Deduction H $ φ ➝ ψ ➝ φ ⋏ ψ
  | orIntroL φ ψ                 : Deduction H $ φ ➝ φ ⋎ ψ
  | orIntroR φ ψ                 : Deduction H $ ψ ➝ φ ⋎ ψ
  | orElim φ ψ χ                 : Deduction H $ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

def Deduction.axm' {H : Hilbert α} {φ} (h : φ ∈ H.axioms) : Deduction H φ := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply Deduction.axm _ h

instance : Entailment (Formula α) (Hilbert α) := ⟨Deduction⟩

instance : Entailment.ModusPonens H := ⟨.mdp⟩
instance : Entailment.HasAxiomImply₁ H := ⟨.implyS⟩
instance : Entailment.HasAxiomImply₂ H := ⟨.implyK⟩
instance : Entailment.HasAxiomAndInst H := ⟨.K_intro⟩
instance : Entailment.Minimal H where
  verum := .verum
  and₁  := .andElimL
  and₂  := .andElimR
  or₁   := .orIntroL
  or₂   := .orIntroR
  or₃   := .orElim

@[induction_eliminator]
protected lemma rec!
  {motive   : (φ : Formula α) → (H ⊢! φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ H.axioms) → motive (φ⟦s⟧) ⟨.axm s h⟩)
  (mdp      : ∀ {φ ψ : Formula α}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (verum    : motive ⊤ verum!)
  (implyS   : ∀ {φ ψ},   motive (Axioms.Imply₁ φ ψ) $ by simp)
  (implyK   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (andElimL : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ φ) $ by simp)
  (andElimR : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ ψ) $ by simp)
  (K_intro  : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ ⋏ ψ) $ by simp)
  (orIntroL : ∀ {φ ψ},   motive (φ ➝ φ ⋎ ψ) $ by simp)
  (orIntroR : ∀ {φ ψ},   motive (ψ ➝ φ ⋎ ψ) $ by simp)
  (orElim   : ∀ {φ ψ χ}, motive ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ φ ⋎ ψ ➝ χ) $ by simp)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  rintro φ ⟨d⟩
  induction d with
  | axm s h => apply axm s h
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp
    . apply ihφψ
    . apply ihφ
  | verum => simpa
  | implyS => apply implyS
  | implyK => apply implyK
  | andElimL => apply andElimL
  | andElimR => apply andElimR
  | K_intro => apply K_intro
  | orIntroL => apply orIntroL
  | orIntroR => apply orIntroR
  | orElim => apply orElim

lemma axm! {φ} (s) (h : φ ∈ H.axioms) : H ⊢! (φ⟦s⟧) := ⟨.axm s h⟩

lemma axm'! {φ} (h : φ ∈ H.axioms) : H ⊢! φ := by simpa using axm! Substitution.id h

lemma axm_instances! {φ} (h : φ ∈ H.axiomInstances) : H ⊢! φ := by
  obtain ⟨ψ, hψ, s, rfl⟩ := h
  apply axm! s hψ

lemma subst! {φ} (s) (h : H ⊢! φ) : H ⊢! (φ⟦s⟧) := by
  induction h with
  | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ
  | @axm φ s' h => rw [(show φ⟦s'⟧⟦s⟧ = φ⟦s' ∘ s⟧ by simp)]; apply axm!; exact h
  | _ => simp

lemma weakerThan_of_provable_axioms (hs : H₂ ⊢!* H₁.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_iff.mpr
  intro φ h
  induction h with
  | @axm φ s h => apply subst!; apply @hs φ h
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂
  | _ => simp

lemma weakerThan_of_subset_axioms (hs : H₁.axioms ⊆ H₂.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_of_provable_axioms
  intro φ h
  apply axm'!
  exact hs h


protected abbrev logic (H : Hilbert α) : Logic α := Entailment.theory H

instance [H₁ ⪯ H₂] : H₁.logic ⪯ H₂.logic := by
  apply weakerThan_iff.mpr
  simp only [theory, Logic.iff_provable, Set.mem_setOf_eq]
  apply WeakerThan.wk
  infer_instance

instance [H₁ ⪱ H₂] : H₁.logic ⪱ H₂.logic := by
  apply strictlyWeakerThan_iff.mpr
  simp only [theory, Logic.iff_provable, Set.mem_setOf_eq, Logic.iff_unprovable]
  apply strictlyWeakerThan_iff.mp
  infer_instance

instance [H₁ ≊ H₂] : H₁.logic ≊ H₂.logic := by
  apply Equiv.iff.mpr
  simp only [theory, Logic.iff_provable, Set.mem_setOf_eq]
  apply Equiv.iff.mp
  infer_instance

lemma iff_provable : H ⊢! φ ↔ H.logic ⊢! φ := by simp [theory]
lemma iff_not_provable : H ⊬ φ ↔ H.logic ⊬ φ := by simp [theory]

instance : Entailment.Minimal H.logic where
  and₁ _ _     := by constructor; simp [theory]
  and₂ _ _     := by constructor; simp [theory]
  and₃ _ _     := by constructor; simp [theory]
  or₁ _ _      := by constructor; simp [theory]
  or₂ _ _      := by constructor; simp [theory]
  or₃ _ _ _    := by constructor; simp [theory]
  verum        := by constructor; simp [theory]
  negEquiv _   := by constructor; simp [theory]
  imply₁ _ _   := by constructor; simp [theory]
  imply₂ _ _ _ := by constructor; simp [theory]
  mdp hφψ hφ := by
    constructor
    replace hφψ := hφψ.1
    replace hφ := hφ.1
    simp only [theory, Set.mem_setOf_eq] at hφψ hφ ⊢
    exact hφψ ⨀ hφ


end Hilbert

end LO.Propositional
