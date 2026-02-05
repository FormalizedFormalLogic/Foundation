module

/-
  `WF` system by de Jongh and Shirmohammadzadeh Maleki
-/
public import Foundation.Propositional.Hilbert.Axiom
public import Foundation.Propositional.Logic.Basic

@[expose] public section

namespace LO.Propositional

open Entailment.Corsi

variable {α : Type*} {Ax Ax₁ Ax₂ : Axiom α} {φ ψ χ : Formula _}

protected inductive Hilbert.WF (Ax : Axiom α) : Logic α
| protected axm {φ}                 : φ ∈ Ax → Hilbert.WF Ax φ
| protected andElimL {φ ψ}          : Hilbert.WF Ax $ Axioms.AndElim₁ φ ψ
| protected andElimR {φ ψ}          : Hilbert.WF Ax $ Axioms.AndElim₂ φ ψ
| protected orIntroL {φ ψ}          : Hilbert.WF Ax $ Axioms.OrInst₁ φ ψ
| protected orIntroR {φ ψ}          : Hilbert.WF Ax $ Axioms.OrInst₂ φ ψ
| protected distributeAndOr {φ ψ χ} : Hilbert.WF Ax $ Axioms.DistributeAndOr φ ψ χ
| protected impId {φ}               : Hilbert.WF Ax $ Axioms.ImpId φ
| protected efq {φ}                 : Hilbert.WF Ax $ Axioms.EFQ φ
| protected mdp {φ ψ}               : Hilbert.WF Ax (φ ➝ ψ) → Hilbert.WF Ax φ → Hilbert.WF Ax ψ
| protected af {φ ψ}                : Hilbert.WF Ax φ → Hilbert.WF Ax (ψ ➝ φ)
| protected andIR {φ ψ}             : Hilbert.WF Ax φ → Hilbert.WF Ax ψ → Hilbert.WF Ax (φ ⋏ ψ)
| protected ruleC {φ ψ χ}           : Hilbert.WF Ax (φ ➝ ψ) → Hilbert.WF Ax (φ ➝ χ) → Hilbert.WF Ax (φ ➝ (ψ ⋏ χ))
| protected ruleD {φ ψ χ}           : Hilbert.WF Ax (φ ➝ χ) → Hilbert.WF Ax (ψ ➝ χ) → Hilbert.WF Ax (φ ⋎ ψ ➝ χ)
| protected ruleI {φ ψ χ}           : Hilbert.WF Ax (φ ➝ ψ) → Hilbert.WF Ax (ψ ➝ χ) → Hilbert.WF Ax (φ ➝ χ)
| protected ruleE {φ ψ χ ξ}         : Hilbert.WF Ax (φ ⭤ ψ) → Hilbert.WF Ax (χ ⭤ ξ) → Hilbert.WF Ax ((φ ➝ χ) ⭤ (ψ ➝ ξ))

namespace Hilbert.WF

@[grind ⇒]
protected lemma axm' (h : φ ∈ Ax) : φ ∈ Hilbert.WF Ax := by apply WF.axm h;

@[grind ⇒]
protected lemma axm'! (h : φ ∈ Ax) : Hilbert.WF Ax ⊢ φ := by
  apply Logic.iff_provable.mpr;
  apply WF.axm h;

instance : Entailment.WF (Hilbert.WF Ax) where
  and₁ := ⟨WF.andElimL⟩
  and₂ := ⟨WF.andElimR⟩
  or₁  := ⟨WF.orIntroL⟩
  or₂  := ⟨WF.orIntroR⟩
  distributeAndOr! := ⟨WF.distributeAndOr⟩
  impId! := ⟨WF.impId⟩
  verum := ⟨WF.impId⟩
  mdp hφψ hφ := ⟨WF.mdp hφψ.1 hφ.1⟩
  efq := ⟨WF.efq⟩
  af! hφ := ⟨WF.af hφ.1⟩
  andIR! h₁ h₂ := ⟨WF.andIR h₁.1 h₂.1⟩
  ruleC! h₁ h₂ := ⟨WF.ruleC h₁.1 h₂.1⟩
  ruleD! h₁ h₂ := ⟨WF.ruleD h₁.1 h₂.1⟩
  ruleI! h₁ h₂ := ⟨WF.ruleI h₁.1 h₂.1⟩
  ruleE! h₁ h₂ := ⟨WF.ruleE h₁.1 h₂.1⟩

@[induction_eliminator]
protected lemma rec!
  {motive    : (φ : Formula α) → (Hilbert.WF Ax ⊢ φ) → Sort}
  (axm       : ∀ {φ}, (h : φ ∈ Ax) → motive (φ) (WF.axm'! h))
  (mdp       : ∀ {φ ψ}, {hφψ : (Hilbert.WF Ax) ⊢ φ ➝ ψ} → {hφ : (Hilbert.WF Ax) ⊢ φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → (motive ψ (hφψ ⨀ hφ)))
  (af        : ∀ {φ ψ}, {hφ : (Hilbert.WF Ax) ⊢ φ} → (motive φ hφ) → (motive (ψ ➝ φ) (af hφ)))
  (andIR     : ∀ {φ ψ}, {hφ : (Hilbert.WF Ax) ⊢ φ} → {hψ : (Hilbert.WF Ax) ⊢ ψ} → (motive φ hφ) → (motive ψ hψ) → (motive (φ ⋏ ψ) (andIR hφ hψ)))
  (ruleC     : ∀ {φ ψ χ}, {h₁ : (Hilbert.WF Ax) ⊢ φ ➝ ψ} → {h₂ : (Hilbert.WF Ax) ⊢ φ ➝ χ} → (motive (φ ➝ ψ) h₁) → (motive (φ ➝ χ) h₂) → (motive (φ ➝ (ψ ⋏ χ)) (ruleC h₁ h₂)))
  (ruleD     : ∀ {φ ψ χ}, {h₁ : (Hilbert.WF Ax) ⊢ φ ➝ χ} → {h₂ : (Hilbert.WF Ax) ⊢ ψ ➝ χ} → (motive (φ ➝ χ) h₁) → (motive (ψ ➝ χ) h₂) → (motive (φ ⋎ ψ ➝ χ) (ruleD h₁ h₂)))
  (ruleI     : ∀ {φ ψ χ}, {h₁ : (Hilbert.WF Ax) ⊢ φ ➝ ψ} → {h₂ : (Hilbert.WF Ax) ⊢ ψ ➝ χ} → (motive (φ ➝ ψ) h₁) → (motive (ψ ➝ χ) h₂) → (motive (φ ➝ χ) (ruleI h₁ h₂)))
  (ruleE     : ∀ {φ ψ χ ξ}, {h₁ : (Hilbert.WF Ax) ⊢ φ ⭤ ψ} → {h₂ : (Hilbert.WF Ax) ⊢ χ ⭤ ξ} → (motive (φ ⭤ ψ) h₁) → (motive (χ ⭤ ξ) h₂) → (motive ((φ ➝ χ) ⭤ (ψ ➝ ξ)) (ruleE h₁ h₂)))
  (impId     : ∀ {φ}, (motive (Axioms.ImpId φ) impId))
  (andElimL  : ∀ {φ ψ}, (motive (Axioms.AndElim₁ φ ψ) andElimL))
  (andElimR  : ∀ {φ ψ}, (motive (Axioms.AndElim₂ φ ψ) andElimR))
  (orIntroL  : ∀ {φ ψ}, (motive (Axioms.OrInst₁ φ ψ) orIntroL))
  (orIntroR  : ∀ {φ ψ}, (motive (Axioms.OrInst₂ φ ψ) orIntroR))
  (efq       : ∀ {φ}, (motive (Axioms.EFQ φ) efq))
  (distributeAndOr : ∀ {φ ψ χ : Formula α}, (motive (Axioms.DistributeAndOr φ ψ χ) distributeAndOr))
  : ∀ {φ}, (d : Hilbert.WF Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm h => apply axm h;
  | mdp hφψ hφ ihφψ ihφ => apply mdp (ihφψ (Logic.iff_provable.mpr hφψ)) (ihφ (Logic.iff_provable.mpr hφ));
  | af hφ ihφ => apply af $ ihφ (Logic.iff_provable.mpr hφ);
  | andIR hφ hψ ihφ ihψ => apply andIR (ihφ (Logic.iff_provable.mpr hφ)) (ihψ (Logic.iff_provable.mpr hψ));
  | ruleC h₁ h₂ ih₁ ih₂ => apply ruleC (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | ruleD h₁ h₂ ih₁ ih₂ => apply ruleD (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | ruleI h₁ h₂ ih₁ ih₂ => apply ruleI (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | ruleE h₁ h₂ ih₁ ih₂ => apply ruleE (ih₁ (Logic.iff_provable.mpr h₁)) (ih₂ (Logic.iff_provable.mpr h₂));
  | _ => grind;


lemma weakerThan_of_provable_axioms (hs : (Hilbert.WF Ax₂) ⊢* Ax₁) : (Hilbert.WF Ax₁) ⪯ (Hilbert.WF Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.WF.rec! with
  | axm h => apply hs; assumption;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | af ih => exact af ih;
  | andIR ih₁ ih₂ => exact andIR ih₁ ih₂;
  | ruleC ih₁ ih₂ => exact ruleC ih₁ ih₂;
  | ruleD ih₁ ih₂ => exact ruleD ih₁ ih₂;
  | ruleI ih₁ ih₂ => exact ruleI ih₁ ih₂;
  | ruleE ih₁ ih₂ => exact ruleE ih₁ ih₂;
  | _ =>
      first
      | apply impId;
      | apply andElimL;
      | apply andElimR;
      | apply orIntroL;
      | apply orIntroR;
      | apply distributeAndOr;
      | apply efq;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert.WF Ax₁) ⪯ (Hilbert.WF Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.WF.axm'!;
  grind;

end Hilbert.WF

protected abbrev WF : Logic ℕ := Hilbert.WF ∅
instance : Entailment.WF Propositional.WF where

end LO.Propositional
end
