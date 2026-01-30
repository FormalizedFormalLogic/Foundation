module

public import Foundation.Propositional.Hilbert.Axiom
public import Foundation.Propositional.Logic.Basic

@[expose] public section

namespace LO.Propositional

open Entailment.Corsi

variable {α : Type*} {Ax Ax₁ Ax₂ : Axiom α} {φ ψ χ : Formula _}

protected inductive Hilbert.VF (Ax : Axiom α) : Logic α
| protected axm {φ}                 : φ ∈ Ax → Hilbert.VF Ax φ
| protected andElimL {φ ψ}          : Hilbert.VF Ax $ Axioms.AndElim₁ φ ψ
| protected andElimR {φ ψ}          : Hilbert.VF Ax $ Axioms.AndElim₂ φ ψ
| protected orIntroL {φ ψ}          : Hilbert.VF Ax $ Axioms.OrInst₁ φ ψ
| protected orIntroR {φ ψ}          : Hilbert.VF Ax $ Axioms.OrInst₂ φ ψ
| protected distributeAndOr {φ ψ χ} : Hilbert.VF Ax $ Axioms.DistributeAndOr φ ψ χ
| protected impId {φ}               : Hilbert.VF Ax $ Axioms.ImpId φ
| protected efq {φ}                 : Hilbert.VF Ax $ Axioms.EFQ φ
| protected mdp {φ ψ}               : Hilbert.VF Ax (φ ➝ ψ) → Hilbert.VF Ax φ → Hilbert.VF Ax ψ
| protected af {φ ψ}                : Hilbert.VF Ax φ → Hilbert.VF Ax (ψ ➝ φ)
| protected andIR {φ ψ}             : Hilbert.VF Ax φ → Hilbert.VF Ax ψ → Hilbert.VF Ax (φ ⋏ ψ)
| protected ruleC {φ ψ χ}           : Hilbert.VF Ax (φ ➝ ψ) → Hilbert.VF Ax (φ ➝ χ) → Hilbert.VF Ax (φ ➝ (ψ ⋏ χ))
| protected ruleD {φ ψ χ}           : Hilbert.VF Ax (φ ➝ χ) → Hilbert.VF Ax (ψ ➝ χ) → Hilbert.VF Ax (φ ⋎ ψ ➝ χ)
| protected ruleI {φ ψ χ}           : Hilbert.VF Ax (φ ➝ ψ) → Hilbert.VF Ax (ψ ➝ χ) → Hilbert.VF Ax (φ ➝ χ)

namespace Hilbert.VF

@[grind ⇒]
protected lemma axm' (h : φ ∈ Ax) : φ ∈ Hilbert.VF Ax := by apply VF.axm h;

@[grind ⇒]
protected lemma axm'! (h : φ ∈ Ax) : Hilbert.VF Ax ⊢ φ := by
  apply Logic.iff_provable.mpr;
  apply VF.axm h;

instance : Entailment.VF (Hilbert.VF Ax) where
  and₁ := ⟨VF.andElimL⟩
  and₂ := ⟨VF.andElimR⟩
  or₁  := ⟨VF.orIntroL⟩
  or₂  := ⟨VF.orIntroR⟩
  distributeAndOr! := ⟨VF.distributeAndOr⟩
  impId! := ⟨VF.impId⟩
  verum := ⟨VF.impId⟩
  mdp hφψ hφ := ⟨VF.mdp hφψ.1 hφ.1⟩
  efq := ⟨VF.efq⟩
  af! hφ := ⟨VF.af hφ.1⟩
  andIR! hφ hψ := ⟨VF.andIR hφ.1 hψ.1⟩
  ruleC! h₁ h₂ := ⟨VF.ruleC h₁.1 h₂.1⟩
  ruleD! h₁ h₂ := ⟨VF.ruleD h₁.1 h₂.1⟩
  ruleI! h₁ h₂ := ⟨VF.ruleI h₁.1 h₂.1⟩

@[induction_eliminator]
protected lemma rec!
  {motive    : (φ : Formula α) → (Hilbert.VF Ax ⊢ φ) → Sort}
  (axm       : ∀ {φ}, (h : φ ∈ Ax) → motive (φ) (VF.axm'! h))
  (mdp       : ∀ {φ ψ}, {hφψ : (Hilbert.VF Ax) ⊢ φ ➝ ψ} → {hφ : (Hilbert.VF Ax) ⊢ φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → (motive ψ (hφψ ⨀ hφ)))
  (af        : ∀ {φ ψ}, {hφ : (Hilbert.VF Ax) ⊢ φ} → (motive φ hφ) → (motive (ψ ➝ φ) (af hφ)))
  (ruleC     : ∀ {φ ψ χ}, {h₁ : (Hilbert.VF Ax) ⊢ φ ➝ ψ} → {h₂ : (Hilbert.VF Ax) ⊢ φ ➝ χ} → (motive (φ ➝ ψ) h₁) → (motive (φ ➝ χ) h₂) → (motive (φ ➝ (ψ ⋏ χ)) (ruleC h₁ h₂)))
  (ruleD     : ∀ {φ ψ χ}, {h₁ : (Hilbert.VF Ax) ⊢ φ ➝ χ} → {h₂ : (Hilbert.VF Ax) ⊢ ψ ➝ χ} → (motive (φ ➝ χ) h₁) → (motive (ψ ➝ χ) h₂) → (motive (φ ⋎ ψ ➝ χ) (ruleD h₁ h₂)))
  (ruleI     : ∀ {φ ψ χ}, {h₁ : (Hilbert.VF Ax) ⊢ φ ➝ ψ} → {h₂ : (Hilbert.VF Ax) ⊢ ψ ➝ χ} → (motive (φ ➝ ψ) h₁) → (motive (ψ ➝ χ) h₂) → (motive (φ ➝ χ) (ruleI h₁ h₂)))
  (impId     : ∀ {φ}, (motive (Axioms.ImpId φ) impId))
  (andElimL  : ∀ {φ ψ}, (motive (Axioms.AndElim₁ φ ψ) andElimL))
  (andElimR  : ∀ {φ ψ}, (motive (Axioms.AndElim₂ φ ψ) andElimR))
  (orIntroL  : ∀ {φ ψ}, (motive (Axioms.OrInst₁ φ ψ) orIntroL))
  (orIntroR  : ∀ {φ ψ}, (motive (Axioms.OrInst₂ φ ψ) orIntroR))
  (efq       : ∀ {φ}, (motive (Axioms.EFQ φ) efq))
  (distributeAndOr : ∀ {φ ψ χ : Formula α}, (motive (Axioms.DistributeAndOr φ ψ χ) distributeAndOr))
  : ∀ {φ}, (d : Hilbert.VF Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm h => apply axm h;
  | mdp hφψ hφ ihφψ ihφ => apply mdp (ihφψ (Logic.iff_provable.mpr hφψ)) (ihφ (Logic.iff_provable.mpr hφ));
  | af hφ ihφ => apply af $ ihφ (Logic.iff_provable.mpr hφ);
  | ruleC h₁ h₂ ih₁ ih₂ => apply ruleC (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | ruleD h₁ h₂ ih₁ ih₂ => apply ruleD (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | ruleI h₁ h₂ ih₁ ih₂ => apply ruleI (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | andIR h₁ h₂ ih₁ ih₂ => grind
  | _ => grind;


lemma weakerThan_of_provable_axioms (hs : (Hilbert.VF Ax₂) ⊢* Ax₁) : (Hilbert.VF Ax₁) ⪯ (Hilbert.VF Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.VF.rec! with
  | axm h => apply hs; assumption;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | af ih => exact af ih;
  | ruleC ih₁ ih₂ => exact ruleC ih₁ ih₂;
  | ruleD ih₁ ih₂ => exact ruleD ih₁ ih₂;
  | ruleI ih₁ ih₂ => exact ruleI ih₁ ih₂;
  | _ =>
      first
      | apply impId;
      | apply andElimL;
      | apply andElimR;
      | apply orIntroL;
      | apply orIntroR;
      | apply distributeAndOr;
      | apply efq;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert.VF Ax₁) ⪯ (Hilbert.VF Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.VF.axm'!;
  grind;

end Hilbert.VF

protected abbrev VF : Logic ℕ := Hilbert.VF ∅
instance : Entailment.VF Propositional.VF where

protected abbrev VF_Ser : Logic ℕ := Hilbert.VF { Axioms.Ser }
instance : Entailment.VF Propositional.VF_Ser where
instance : Entailment.HasAxiomSer Propositional.VF_Ser where
  axiomSer! := ⟨by apply Hilbert.VF.axm'; simp⟩

end LO.Propositional
end
