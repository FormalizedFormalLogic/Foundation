/-
  Corsi's `F` system by de Jongh and Shirmohammadzadeh Maleki
-/
import Foundation.Propositional.Entailment.Int.DNE_of_LEM
import Foundation.Propositional.Entailment.Corsi
import Foundation.Propositional.Hilbert.Axiom
import Foundation.Propositional.Formula
import Foundation.Propositional.Logic.Basic
import Foundation.Logic.Disjunctive

namespace LO.Propositional

open Entailment

variable {α : Type*} {Ax Ax₁ Ax₂ : Axiom α} {φ ψ χ : Formula _}

protected inductive Hilbert.Corsi (Ax : Axiom α) : Logic α
| protected axm {φ} (s)             : φ ∈ Ax → Hilbert.Corsi Ax (φ⟦s⟧)
| protected andElimL {φ ψ}          : Hilbert.Corsi Ax $ Axioms.AndElim₁ φ ψ
| protected andElimR {φ ψ}          : Hilbert.Corsi Ax $ Axioms.AndElim₂ φ ψ
| protected orIntroL {φ ψ}          : Hilbert.Corsi Ax $ Axioms.OrInst₁ φ ψ
| protected orIntroR {φ ψ}          : Hilbert.Corsi Ax $ Axioms.OrInst₂ φ ψ
| protected distributeAndOr {φ ψ χ} : Hilbert.Corsi Ax $ Axioms.DistributeAndOr φ ψ χ
| protected axiomC {φ ψ χ}          : Hilbert.Corsi Ax $ Axioms.C φ ψ χ
| protected axiomD {φ ψ χ}          : Hilbert.Corsi Ax $ Axioms.D φ ψ χ
| protected axiomI {φ ψ χ}          : Hilbert.Corsi Ax $ Axioms.I φ ψ χ
| protected impId {φ}               : Hilbert.Corsi Ax $ Axioms.ImpId φ
| protected mdp {φ ψ}               : Hilbert.Corsi Ax (φ ➝ ψ) → Hilbert.Corsi Ax φ → Hilbert.Corsi Ax ψ
| protected af {φ ψ}                : Hilbert.Corsi Ax φ → Hilbert.Corsi Ax (ψ ➝ φ)
| protected andIR {φ ψ}             : Hilbert.Corsi Ax φ → Hilbert.Corsi Ax ψ → Hilbert.Corsi Ax (φ ⋏ ψ)

namespace Hilbert.Corsi

@[grind ⇒]
protected lemma axm' (h : φ ∈ Ax) : φ ∈ Hilbert.Corsi Ax := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply Corsi.axm _ h;

@[grind ⇒]
protected lemma axm! (s : Substitution α) (h : φ ∈ Ax) : Hilbert.Corsi Ax ⊢ φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply Corsi.axm s h;

@[grind ⇒]
protected lemma axm'! (h : φ ∈ Ax) : Hilbert.Corsi Ax ⊢ φ := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply Corsi.axm! _ h;

@[grind ⇒]
protected lemma axm_instances! (h : φ ∈ Ax.instances) : Hilbert.Corsi Ax ⊢ φ := by
  rcases h with ⟨ψ, _, s, rfl⟩;
  grind;

instance : Entailment.F (Hilbert.Corsi Ax) where
  and₁ := ⟨Corsi.andElimL⟩
  and₂ := ⟨Corsi.andElimR⟩
  or₁  := ⟨Corsi.orIntroL⟩
  or₂  := ⟨Corsi.orIntroR⟩
  distributeAndOr! := ⟨Corsi.distributeAndOr⟩
  axiomC! := ⟨Corsi.axiomC⟩
  axiomD! := ⟨Corsi.axiomD⟩
  axiomI! := ⟨Corsi.axiomI⟩
  impId! := ⟨Corsi.impId⟩
  mdp hφψ hφ := ⟨Corsi.mdp hφψ.1 hφ.1⟩
  af! hφ := ⟨Corsi.af hφ.1⟩
  andIR! h₁ h₂ := ⟨Corsi.andIR h₁.1 h₂.1⟩

@[induction_eliminator]
protected lemma rec!
  {motive   : (φ : Formula α) → (Hilbert.Corsi Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (Corsi.axm! _ h))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Hilbert.Corsi Ax) ⊢ φ ➝ ψ} → {hφ : (Hilbert.Corsi Ax) ⊢ φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → (motive ψ (hφψ ⨀ hφ)))
  (af       : ∀ {φ ψ : Formula α}, {hφ : (Hilbert.Corsi Ax) ⊢ φ} → (motive φ hφ) → (motive (ψ ➝ φ) (af hφ)))
  (andIR    : ∀ {φ ψ : Formula α}, {hφ : (Hilbert.Corsi Ax) ⊢ φ} → {hψ : (Hilbert.Corsi Ax) ⊢ ψ} → (motive φ hφ) → (motive ψ hψ) → (motive (φ ⋏ ψ) (andIR hφ hψ)))
  (impId    : ∀ {φ : Formula α}, (motive (Axioms.ImpId φ) impId))
  (andElimL : ∀ {φ ψ : Formula α}, (motive (Axioms.AndElim₁ φ ψ) Entailment.and₁!))
  (andElimR : ∀ {φ ψ : Formula α}, (motive (Axioms.AndElim₂ φ ψ) Entailment.and₂!))
  (orIntroL  : ∀ {φ ψ : Formula α}, (motive (Axioms.OrInst₁ φ ψ) Entailment.or₁!))
  (orIntroR  : ∀ {φ ψ : Formula α}, (motive (Axioms.OrInst₂ φ ψ) Entailment.or₂!))
  (distributeAndOr : ∀ {φ ψ χ : Formula α}, (motive (Axioms.DistributeAndOr φ ψ χ) distributeAndOr))
  (axiomC   : ∀ {φ ψ χ : Formula α}, (motive (Axioms.C φ ψ χ) axiomC))
  (axiomD   : ∀ {φ ψ χ : Formula α}, (motive (Axioms.D φ ψ χ) axiomD))
  (axiomI   : ∀ {φ ψ χ : Formula α}, (motive (Axioms.I φ ψ χ) axiomI))
  : ∀ {φ}, (d : Hilbert.Corsi Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ => apply mdp (ihφψ (Logic.iff_provable.mpr hφψ)) (ihφ (Logic.iff_provable.mpr hφ));
  | af hφ ihφ => apply af $ ihφ (Logic.iff_provable.mpr hφ);
  | andIR hφ hψ ihφ ihψ => apply andIR (ihφ (Logic.iff_provable.mpr hφ)) (ihψ (Logic.iff_provable.mpr hψ));
  | _ => grind;

instance : Logic.Substitution (Hilbert.Corsi Ax) where
  subst s h := by
    induction h using Hilbert.Corsi.rec! with
    | axm s' h => simpa [Formula.subst_comp] using Corsi.axm! (s' ∘ s) h;
    | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
    | af ih => exact af ih;
    | andIR ih₁ ih₂ => exact andIR ih₁ ih₂;
    | _ =>
      first
      | apply impId;
      | apply Entailment.and₁!;
      | apply Entailment.and₂!;
      | apply Entailment.or₁!;
      | apply Entailment.or₂!;
      | apply distributeAndOr;
      | apply axiomC;
      | apply axiomD;
      | apply axiomI;

lemma weakerThan_of_provable_axioms (hs : (Hilbert.Corsi Ax₂) ⊢* Ax₁) : (Hilbert.Corsi Ax₁) ⪯ (Hilbert.Corsi Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.Corsi.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | af ih => exact af ih;
  | andIR ih₁ ih₂ => exact andIR ih₁ ih₂;
  | _ =>
      first
      | apply impId;
      | apply Entailment.and₁!;
      | apply Entailment.and₂!;
      | apply Entailment.or₁!;
      | apply Entailment.or₂!;
      | apply distributeAndOr;
      | apply axiomC;
      | apply axiomD;
      | apply axiomI;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert.Corsi Ax₁) ⪯ (Hilbert.Corsi Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.Corsi.axm'!;
  grind;

section

variable [DecidableEq α]
open Axiom

instance [Ax.HasAxiomRfl] : Entailment.HasAxiomRfl (Hilbert.Corsi Ax) where
  axiomRfl! {φ ψ} := ⟨by
    simpa using Hilbert.Corsi.axm
      (φ := Axioms.Rfl (.atom (HasAxiomRfl.p Ax)) (.atom (HasAxiomRfl.q Ax)))
      (s := λ b =>
        if (HasAxiomRfl.p Ax) = b then φ
        else if (HasAxiomRfl.q Ax) = b then ψ
        else (.atom b))
      $ (HasAxiomRfl.mem_rfl);
  ⟩

instance [Ax.HasAxiomSym] : Entailment.HasAxiomSym (Hilbert.Corsi Ax) where
  axiomSym! {φ ψ} := ⟨by
    simpa using Hilbert.Corsi.axm
      (φ := Axioms.Sym (.atom (HasAxiomSym.p Ax)) (.atom (HasAxiomSym.q Ax)))
      (s := λ b =>
        if (HasAxiomSym.p Ax) = b then φ
        else if (HasAxiomSym.q Ax) = b then ψ
        else (.atom b))
      $ (HasAxiomSym.mem_sym);
  ⟩

instance [Ax.HasAxiomTra1] : Entailment.HasAxiomTra1 (Hilbert.Corsi Ax) where
  axiomTra1! {φ ψ χ} := ⟨by
    simpa using Hilbert.Corsi.axm
      (φ := Axioms.Tra1 (#(HasAxiomTra1.p Ax)) (#(HasAxiomTra1.q Ax)) (#(HasAxiomTra1.r Ax)))
      (s := λ b =>
        if (HasAxiomTra1.p Ax) = b then φ
        else if (HasAxiomTra1.q Ax) = b then ψ
        else if (HasAxiomTra1.r Ax) = b then χ
        else (.atom b)
      )
      $ (HasAxiomTra1.mem_tra1);
  ⟩

end

end Hilbert.Corsi



protected abbrev F.axioms : Axiom ℕ := ∅
protected abbrev F := Hilbert.Corsi F.axioms
instance : Entailment.F Propositional.F where


protected abbrev F_Ser.axioms : Axiom ℕ := { Axioms.Ser }
namespace F_Ser
instance : F_Ser.axioms.HasAxiomSer where
end F_Ser
protected abbrev F_Ser := Hilbert.Corsi F_Ser.axioms
instance : Entailment.F Propositional.F_Ser where


protected abbrev F_Rfl.axioms : Axiom ℕ := { Axioms.Rfl #0 #1 }
namespace F_Rfl
instance : F_Rfl.axioms.HasAxiomRfl where p := 0; q := 1
end F_Rfl
protected abbrev F_Rfl := Hilbert.Corsi F_Rfl.axioms
instance : Entailment.F Propositional.F_Rfl where


protected abbrev F_Sym.axioms : Axiom ℕ := { Axioms.Sym #0 #1 }
namespace F_Sym
instance : F_Sym.axioms.HasAxiomSym where p := 0; q := 1
end F_Sym
protected abbrev F_Sym := Hilbert.Corsi F_Sym.axioms
instance : Entailment.F Propositional.F_Sym where


end LO.Propositional
