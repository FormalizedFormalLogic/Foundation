import Foundation.Propositional.Hilbert.Axiom
import Foundation.Propositional.Logic.Basic

namespace LO.Propositional

open Entailment.Corsi

variable {α : Type*} {Ax Ax₁ Ax₂ : Axiom α} {φ ψ χ : Formula _}

protected inductive Hilbert.VCorsi (Ax : Axiom α) : Logic α
| protected axm {φ} (s)             : φ ∈ Ax → Hilbert.VCorsi Ax (φ⟦s⟧)
| protected andElimL {φ ψ}          : Hilbert.VCorsi Ax $ Axioms.AndElim₁ φ ψ
| protected andElimR {φ ψ}          : Hilbert.VCorsi Ax $ Axioms.AndElim₂ φ ψ
| protected orIntroL {φ ψ}          : Hilbert.VCorsi Ax $ Axioms.OrInst₁ φ ψ
| protected orIntroR {φ ψ}          : Hilbert.VCorsi Ax $ Axioms.OrInst₂ φ ψ
| protected distributeAndOr {φ ψ χ} : Hilbert.VCorsi Ax $ Axioms.DistributeAndOr φ ψ χ
| protected axiomC {φ ψ χ}          : Hilbert.VCorsi Ax $ Axioms.C φ ψ χ
| protected impId {φ}               : Hilbert.VCorsi Ax $ Axioms.ImpId φ
| protected efq {φ}                 : Hilbert.VCorsi Ax $ Axioms.EFQ φ
| protected mdp {φ ψ}               : Hilbert.VCorsi Ax (φ ➝ ψ) → Hilbert.VCorsi Ax φ → Hilbert.VCorsi Ax ψ
| protected af {φ ψ}                : Hilbert.VCorsi Ax φ → Hilbert.VCorsi Ax (ψ ➝ φ)
| protected andIR {φ ψ}             : Hilbert.VCorsi Ax φ → Hilbert.VCorsi Ax ψ → Hilbert.VCorsi Ax (φ ⋏ ψ)
| protected dilemma {φ ψ χ}         : Hilbert.VCorsi Ax (φ ➝ χ) → Hilbert.VCorsi Ax (ψ ➝ χ) → Hilbert.VCorsi Ax (φ ⋎ ψ ➝ χ)
| protected greedy {φ ψ χ}          : Hilbert.VCorsi Ax (φ ➝ ψ) → Hilbert.VCorsi Ax (φ ➝ χ) → Hilbert.VCorsi Ax (φ ➝ ψ ⋏ χ)
| protected transRule {φ ψ χ}       : Hilbert.VCorsi Ax (φ ➝ ψ) → Hilbert.VCorsi Ax (ψ ➝ χ) → Hilbert.VCorsi Ax (φ ➝ χ)

namespace Hilbert.VCorsi

@[grind ⇒]
protected lemma axm' (h : φ ∈ Ax) : φ ∈ Hilbert.VCorsi Ax := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply VCorsi.axm _ h;

@[grind ⇒]
protected lemma axm! (s : Substitution α) (h : φ ∈ Ax) : Hilbert.VCorsi Ax ⊢ φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply VCorsi.axm s h;

@[grind ⇒]
protected lemma axm'! (h : φ ∈ Ax) : Hilbert.VCorsi Ax ⊢ φ := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply VCorsi.axm! _ h;

@[grind ⇒]
protected lemma axm_instances! (h : φ ∈ Ax.instances) : Hilbert.VCorsi Ax ⊢ φ := by
  rcases h with ⟨ψ, _, s, rfl⟩;
  grind;

instance : Entailment.VF (Hilbert.VCorsi Ax) where
  and₁ := ⟨VCorsi.andElimL⟩
  and₂ := ⟨VCorsi.andElimR⟩
  or₁  := ⟨VCorsi.orIntroL⟩
  or₂  := ⟨VCorsi.orIntroR⟩
  distributeAndOr! := ⟨VCorsi.distributeAndOr⟩
  axiomC! := ⟨VCorsi.axiomC⟩
  impId! := ⟨VCorsi.impId⟩
  verum := ⟨VCorsi.impId⟩
  efq := ⟨VCorsi.efq⟩
  mdp hφψ hφ := ⟨VCorsi.mdp hφψ.1 hφ.1⟩
  af! hφ := ⟨VCorsi.af hφ.1⟩
  andIR! h₁ h₂ := ⟨VCorsi.andIR h₁.1 h₂.1⟩
  dilemma! h₁ h₂ := ⟨VCorsi.dilemma h₁.1 h₂.1⟩
  greedy! h₁ h₂ := ⟨VCorsi.greedy h₁.1 h₂.1⟩
  transRule! h₁ h₂ := ⟨VCorsi.transRule h₁.1 h₂.1⟩

@[induction_eliminator]
protected lemma rec!
  {motive    : (φ : Formula α) → (Hilbert.VCorsi Ax ⊢ φ) → Sort}
  (axm       : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (VCorsi.axm! _ h))
  (mdp       : ∀ {φ ψ : Formula α}, {hφψ : (Hilbert.VCorsi Ax) ⊢ φ ➝ ψ} → {hφ : (Hilbert.VCorsi Ax) ⊢ φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → (motive ψ (hφψ ⨀ hφ)))
  (af        : ∀ {φ ψ : Formula α}, {hφ : (Hilbert.VCorsi Ax) ⊢ φ} → (motive φ hφ) → (motive (ψ ➝ φ) (af hφ)))
  (andIR     : ∀ {φ ψ : Formula α}, {hφ : (Hilbert.VCorsi Ax) ⊢ φ} → {hψ : (Hilbert.VCorsi Ax) ⊢ ψ} → (motive φ hφ) → (motive ψ hψ) → (motive (φ ⋏ ψ) (andIR hφ hψ)))
  (dilemma   : ∀ {φ ψ χ : Formula α}, {h₁ : (Hilbert.VCorsi Ax) ⊢ φ ➝ χ} → {h₂ : (Hilbert.VCorsi Ax) ⊢ ψ ➝ χ} → (motive (φ ➝ χ) h₁) → (motive (ψ ➝ χ) h₂) → (motive (φ ⋎ ψ ➝ χ) (dilemma h₁ h₂)))
  (greedy    : ∀ {φ ψ χ : Formula α}, {h₁ : (Hilbert.VCorsi Ax) ⊢ φ ➝ ψ} → {h₂ : (Hilbert.VCorsi Ax) ⊢ φ ➝ χ} → (motive (φ ➝ ψ) h₁) → (motive (φ ➝ χ) h₂) → (motive (φ ➝ ψ ⋏ χ) (greedy h₁ h₂)))
  (transRule : ∀ {φ ψ χ : Formula α}, {h₁ : (Hilbert.VCorsi Ax) ⊢ φ ➝ ψ} → {h₂ : (Hilbert.VCorsi Ax) ⊢ ψ ➝ χ} → (motive (φ ➝ ψ) h₁) → (motive (ψ ➝ χ) h₂) → (motive (φ ➝ χ) (transRule h₁ h₂)))
  (impId     : ∀ {φ : Formula α}, (motive (Axioms.ImpId φ) impId))
  (andElimL  : ∀ {φ ψ : Formula α}, (motive (Axioms.AndElim₁ φ ψ) andElimL))
  (andElimR  : ∀ {φ ψ : Formula α}, (motive (Axioms.AndElim₂ φ ψ) andElimR))
  (orIntroL  : ∀ {φ ψ : Formula α}, (motive (Axioms.OrInst₁ φ ψ) orIntroL))
  (orIntroR  : ∀ {φ ψ : Formula α}, (motive (Axioms.OrInst₂ φ ψ) orIntroR))
  (distributeAndOr : ∀ {φ ψ χ : Formula α}, (motive (Axioms.DistributeAndOr φ ψ χ) distributeAndOr))
  (axiomC   : ∀ {φ ψ χ : Formula α}, (motive (Axioms.C φ ψ χ) axiomC))
  (efq      : ∀ {φ : Formula α}, (motive (Axioms.EFQ φ) efq))
  : ∀ {φ}, (d : Hilbert.VCorsi Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ => apply mdp (ihφψ (Logic.iff_provable.mpr hφψ)) (ihφ (Logic.iff_provable.mpr hφ));
  | af hφ ihφ => apply af $ ihφ (Logic.iff_provable.mpr hφ);
  | andIR hφ hψ ihφ ihψ => apply andIR (ihφ (Logic.iff_provable.mpr hφ)) (ihψ (Logic.iff_provable.mpr hψ));
  | dilemma h₁ h₂ ih₁ ih₂ => apply dilemma (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | greedy h₁ h₂ ih₁ ih₂ => apply greedy (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | transRule h₁ h₂ ih₁ ih₂ => apply transRule (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | _ => grind;

instance : Logic.Substitution (Hilbert.VCorsi Ax) where
  subst s h := by
    induction h using Hilbert.VCorsi.rec! with
    | axm s' h => simpa [Formula.subst_comp] using VCorsi.axm! (s' ∘ s) h;
    | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
    | af ih => exact af ih;
    | andIR ih₁ ih₂ => exact andIR ih₁ ih₂;
    | dilemma ih₁ ih₂ => exact dilemma ih₁ ih₂;
    | greedy ih₁ ih₂ => exact greedy ih₁ ih₂;
    | transRule ih₁ ih₂ => exact transRule ih₁ ih₂;
    | _ =>
      first
      | apply impId;
      | apply andElimL;
      | apply andElimR;
      | apply orIntroL;
      | apply orIntroR;
      | apply distributeAndOr;
      | apply axiomC;
      | apply efq;

lemma weakerThan_of_provable_axioms (hs : (Hilbert.VCorsi Ax₂) ⊢* Ax₁) : (Hilbert.VCorsi Ax₁) ⪯ (Hilbert.VCorsi Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.VCorsi.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | af ih => exact af ih;
  | andIR ih₁ ih₂ => exact andIR ih₁ ih₂;
  | dilemma ih₁ ih₂ => exact dilemma ih₁ ih₂;
  | greedy ih₁ ih₂ => exact greedy ih₁ ih₂;
  | transRule ih₁ ih₂ => exact transRule ih₁ ih₂;
  | _ =>
      first
      | apply impId;
      | apply andElimL;
      | apply andElimR;
      | apply orIntroL;
      | apply orIntroR;
      | apply distributeAndOr;
      | apply axiomC;
      | apply efq;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert.VCorsi Ax₁) ⪯ (Hilbert.VCorsi Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.VCorsi.axm'!;
  grind;

section

variable [DecidableEq α]
open Axiom

instance [Ax.HasAxiomD] : Entailment.HasAxiomD (Hilbert.VCorsi Ax) where
  axiomD! {φ ψ χ} := ⟨by
    simpa using Hilbert.VCorsi.axm
      (φ := Axioms.D (#(HasAxiomD.p Ax)) (#(HasAxiomD.q Ax)) (#(HasAxiomD.r Ax)))
      (s := λ b =>
        if (HasAxiomD.p Ax) = b then φ
        else if (HasAxiomD.q Ax) = b then ψ
        else if (HasAxiomD.r Ax) = b then χ
        else (.atom b)
      )
      $ (HasAxiomD.mem_d)
  ⟩;

instance [Ax.HasAxiomI] : Entailment.HasAxiomI (Hilbert.VCorsi Ax) where
  axiomI! {φ ψ χ} := ⟨by
    simpa using Hilbert.VCorsi.axm
      (φ := Axioms.I (#(HasAxiomI.p Ax)) (#(HasAxiomI.q Ax)) (#(HasAxiomI.r Ax)))
      (s := λ b =>
        if (HasAxiomI.p Ax) = b then φ
        else if (HasAxiomI.q Ax) = b then ψ
        else if (HasAxiomI.r Ax) = b then χ
        else (.atom b)
      )
      $ (HasAxiomI.mem_i)
  ⟩;

end

end Hilbert.VCorsi



protected abbrev VF.axioms : Axiom ℕ := ∅
protected abbrev VF := Hilbert.VCorsi VF.axioms
instance : Entailment.VF Propositional.VF where


protected abbrev VF_D.axioms : Axiom ℕ := {Axioms.D #0 #1 #2}
namespace VF_D.axioms
instance : VF_D.axioms.HasAxiomD where p := 0; q := 1; r := 2; mem_d := by simp;
end VF_D.axioms
protected abbrev VF_D := Hilbert.VCorsi VF_D.axioms
instance : Entailment.VF Propositional.VF_D where


protected abbrev VF_I.axioms : Axiom ℕ := {Axioms.I #0 #1 #2}
namespace VF_I.axioms
instance : VF_I.axioms.HasAxiomI where p := 0; q := 1; r := 2; mem_i := by simp;
end VF_I.axioms
protected abbrev VF_I := Hilbert.VCorsi VF_I.axioms
instance : Entailment.VF Propositional.VF_I where


protected abbrev VF_D_I.axioms : Axiom ℕ := {Axioms.D #0 #1 #2, Axioms.I #0 #1 #2}
namespace VF_D_I.axioms
instance : VF_D_I.axioms.HasAxiomD where p := 0; q := 1; r := 2; mem_d := by simp;
instance : VF_D_I.axioms.HasAxiomI where p := 0; q := 1; r := 2; mem_i := by simp;
end VF_D_I.axioms
protected abbrev VF_D_I := Hilbert.VCorsi VF_D_I.axioms
instance : Entailment.VF Propositional.VF_D_I where


end LO.Propositional
