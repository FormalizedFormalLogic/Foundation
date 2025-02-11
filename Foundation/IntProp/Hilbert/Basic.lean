import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.IntProp.Substitution

namespace LO.IntProp

variable {α : Type u}

structure Hilbert (α) where
  axioms : Set (Formula α)

namespace Hilbert

abbrev axiomInstances (H : Hilbert α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

class FiniteAxiomatizable (H : Hilbert α) where
  axioms_fin : Set.Finite H.axioms := by simp

variable {H : Hilbert α}

inductive Deduction (H : Hilbert α) : Formula α → Type _
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | verum         : Deduction H $ ⊤
  | implyS φ ψ    : Deduction H $ φ ➝ ψ ➝ φ
  | implyK φ ψ χ  : Deduction H $ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | andElimL φ ψ  : Deduction H $ φ ⋏ ψ ➝ φ
  | andElimR φ ψ  : Deduction H $ φ ⋏ ψ ➝ ψ
  | andIntro φ ψ  : Deduction H $ φ ➝ ψ ➝ φ ⋏ ψ
  | orIntroL φ ψ  : Deduction H $ φ ➝ φ ⋎ ψ
  | orIntroR φ ψ  : Deduction H $ ψ ➝ φ ⋎ ψ
  | orElim φ ψ χ  : Deduction H $ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

instance : Entailment (Formula α) (Hilbert α) := ⟨Deduction⟩

open Deduction
open Hilbert

section

instance : Entailment.ModusPonens H := ⟨mdp⟩

instance : Entailment.HasAxiomImply₁ H := ⟨implyS⟩

instance : Entailment.HasAxiomImply₂ H := ⟨implyK⟩

instance : Entailment.HasAxiomAndInst H := ⟨andIntro⟩

instance : Entailment.Minimal H where
  mdp := mdp
  verum := verum
  and₁ := andElimL
  and₂ := andElimR
  and₃ := andIntro
  or₁ := orIntroL
  or₂ := orIntroR
  or₃ := orElim

namespace Deduction

lemma maxm! {φ} (h : φ ∈ H.axiomInstances) : H ⊢! φ := ⟨maxm h⟩

open Entailment

noncomputable def rec!
  {motive      : (φ : Formula α) → H ⊢! φ → Sort*}
  (maxm       : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (verum      : motive ⊤ verum!)
  (implyS     : ∀ {φ ψ},   motive (Axioms.Imply₁ φ ψ) $ ⟨implyS φ ψ⟩)
  (implyK     : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ ⟨implyK φ ψ χ⟩)
  (andElimL   : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ φ) $ ⟨andElimL φ ψ⟩)
  (andElimR   : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ ψ) $ ⟨andElimR φ ψ⟩)
  (andIntro   : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ ⋏ ψ) $ ⟨andIntro φ ψ⟩)
  (orIntroL   : ∀ {φ ψ},   motive (φ ➝ φ ⋎ ψ) $ ⟨orIntroL φ ψ⟩)
  (orIntroR   : ∀ {φ ψ},   motive (ψ ➝ φ ⋎ ψ) $ ⟨orIntroR φ ψ⟩)
  (orElim     : ∀ {φ ψ χ}, motive ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ φ ⋎ ψ ➝ χ) $ ⟨orElim φ ψ χ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact maxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | _ => aesop

def subst! {φ} (s) (h : H ⊢! φ) : H ⊢! φ⟦s⟧ := by
  induction h using Deduction.rec! with
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h;
    apply maxm!;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      exact subst_comp;
  | _ => simp;

end Deduction

end



section

open Entailment

variable {H₁ H₂ : Hilbert α}

lemma weakerThan_of_dominate_axiomInstances (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axiomInstances → H₂ ⊢! φ)
  : H₁ ⪯ H₂ := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.rec! with
  | maxm hp => apply hMaxm hp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => simp;

lemma weakerThan_of_subset_axioms (hSubset : H₁.axioms ⊆ H₂.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_of_dominate_axiomInstances;
  rintro φ ⟨ψ, hs, ⟨s, rfl⟩⟩;
  apply maxm!;
  use ψ;
  constructor;
  . exact hSubset hs;
  . use s;

end

end Hilbert

end LO.IntProp
