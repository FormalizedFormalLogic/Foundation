module
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

open Entailment.Corsi

variable {α : Type*} {Ax Ax₁ Ax₂ : Axiom α} {φ ψ χ : Formula _}

protected inductive Hilbert.F (Ax : Axiom α) : Logic α
| protected axm {φ}                 : φ ∈ Ax → Hilbert.F Ax φ
| protected andElimL {φ ψ}          : Hilbert.F Ax $ Axioms.AndElim₁ φ ψ
| protected andElimR {φ ψ}          : Hilbert.F Ax $ Axioms.AndElim₂ φ ψ
| protected orIntroL {φ ψ}          : Hilbert.F Ax $ Axioms.OrInst₁ φ ψ
| protected orIntroR {φ ψ}          : Hilbert.F Ax $ Axioms.OrInst₂ φ ψ
| protected distributeAndOr {φ ψ χ} : Hilbert.F Ax $ Axioms.DistributeAndOr φ ψ χ
| protected axiomC {φ ψ χ}          : Hilbert.F Ax $ Axioms.C φ ψ χ
| protected axiomD {φ ψ χ}          : Hilbert.F Ax $ Axioms.D φ ψ χ
| protected axiomI {φ ψ χ}          : Hilbert.F Ax $ Axioms.I φ ψ χ
| protected impId {φ}               : Hilbert.F Ax $ Axioms.ImpId φ
| protected efq {φ}                 : Hilbert.F Ax $ Axioms.EFQ φ
| protected mdp {φ ψ}               : Hilbert.F Ax (φ ➝ ψ) → Hilbert.F Ax φ → Hilbert.F Ax ψ
| protected af {φ ψ}                : Hilbert.F Ax φ → Hilbert.F Ax (ψ ➝ φ)
| protected andIR {φ ψ}             : Hilbert.F Ax φ → Hilbert.F Ax ψ → Hilbert.F Ax (φ ⋏ ψ)

namespace Hilbert.F

@[grind ⇒]
protected lemma axm' (h : φ ∈ Ax) : φ ∈ Hilbert.F Ax := by apply F.axm h;

@[grind ⇒]
protected lemma axm'! (h : φ ∈ Ax) : Hilbert.F Ax ⊢ φ := by
  apply Logic.iff_provable.mpr;
  apply F.axm h;

instance : Entailment.F (Hilbert.F Ax) where
  and₁ := ⟨F.andElimL⟩
  and₂ := ⟨F.andElimR⟩
  or₁  := ⟨F.orIntroL⟩
  or₂  := ⟨F.orIntroR⟩
  distributeAndOr! := ⟨F.distributeAndOr⟩
  axiomC! := ⟨F.axiomC⟩
  axiomD! := ⟨F.axiomD⟩
  axiomI! := ⟨F.axiomI⟩
  impId! := ⟨F.impId⟩
  verum := ⟨F.impId⟩
  efq := ⟨F.efq⟩
  mdp hφψ hφ := ⟨F.mdp hφψ.1 hφ.1⟩
  af! hφ := ⟨F.af hφ.1⟩
  andIR! h₁ h₂ := ⟨F.andIR h₁.1 h₂.1⟩

@[induction_eliminator]
protected lemma rec!
  {motive   : (φ : Formula α) → (Hilbert.F Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α}, (h : φ ∈ Ax) → motive (φ) (F.axm'! h))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Hilbert.F Ax) ⊢ φ ➝ ψ} → {hφ : (Hilbert.F Ax) ⊢ φ} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → (motive ψ (hφψ ⨀ hφ)))
  (af       : ∀ {φ ψ : Formula α}, {hφ : (Hilbert.F Ax) ⊢ φ} → (motive φ hφ) → (motive (ψ ➝ φ) (af hφ)))
  (andIR    : ∀ {φ ψ : Formula α}, {hφ : (Hilbert.F Ax) ⊢ φ} → {hψ : (Hilbert.F Ax) ⊢ ψ} → (motive φ hφ) → (motive ψ hψ) → (motive (φ ⋏ ψ) (andIR hφ hψ)))
  (impId    : ∀ {φ : Formula α}, (motive (Axioms.ImpId φ) impId))
  (andElimL : ∀ {φ ψ : Formula α}, (motive (Axioms.AndElim₁ φ ψ) andElimL))
  (andElimR : ∀ {φ ψ : Formula α}, (motive (Axioms.AndElim₂ φ ψ) andElimR))
  (orIntroL  : ∀ {φ ψ : Formula α}, (motive (Axioms.OrInst₁ φ ψ) orIntroL))
  (orIntroR  : ∀ {φ ψ : Formula α}, (motive (Axioms.OrInst₂ φ ψ) orIntroR))
  (distributeAndOr : ∀ {φ ψ χ : Formula α}, (motive (Axioms.DistributeAndOr φ ψ χ) distributeAndOr))
  (axiomC   : ∀ {φ ψ χ : Formula α}, (motive (Axioms.C φ ψ χ) axiomC))
  (axiomD   : ∀ {φ ψ χ : Formula α}, (motive (Axioms.D φ ψ χ) axiomD))
  (axiomI   : ∀ {φ ψ χ : Formula α}, (motive (Axioms.I φ ψ χ) axiomI))
  (efq      : ∀ {φ : Formula α}, (motive (Axioms.EFQ φ) efq))
  : ∀ {φ}, (d : Hilbert.F Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm h => apply axm h;
  | mdp hφψ hφ ihφψ ihφ => apply mdp (ihφψ (Logic.iff_provable.mpr hφψ)) (ihφ (Logic.iff_provable.mpr hφ));
  | af hφ ihφ => apply af $ ihφ (Logic.iff_provable.mpr hφ);
  | andIR hφ hψ ihφ ihψ => apply andIR (ihφ (Logic.iff_provable.mpr hφ)) (ihψ (Logic.iff_provable.mpr hψ));
  | _ => grind;

/-
instance : Logic.Substitution (Hilbert.F Ax) where
  subst s h := by
    induction h using Hilbert.F.rec! with
    | axm s' h => simpa [Formula.subst_comp] using F.axm! (s' ∘ s) h;
    | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
    | af ih => exact af ih;
    | andIR ih₁ ih₂ => exact andIR ih₁ ih₂;
    | _ =>
      first
      | apply impId;
      | apply andElimL;
      | apply andElimR;
      | apply orIntroL;
      | apply orIntroR;
      | apply distributeAndOr;
      | apply axiomC;
      | apply axiomD;
      | apply axiomI;
-/

lemma weakerThan_of_provable_axioms (hs : (Hilbert.F Ax₂) ⊢* Ax₁) : (Hilbert.F Ax₁) ⪯ (Hilbert.F Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.F.rec! with
  | axm h => apply hs; assumption;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | af ih => exact af ih;
  | andIR ih₁ ih₂ => exact andIR ih₁ ih₂;
  | _ =>
      first
      | apply impId;
      | apply andElimL;
      | apply andElimR;
      | apply orIntroL;
      | apply orIntroR;
      | apply distributeAndOr;
      | apply axiomC;
      | apply axiomD;
      | apply axiomI;
      | apply efq;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert.F Ax₁) ⪯ (Hilbert.F Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.F.axm'!;
  grind;

section

variable [DecidableEq α]
open Axiom

/-
instance [Ax.HasAxiomRfl] : Entailment.HasAxiomRfl (Hilbert.F Ax) where
  axiomRfl! {φ ψ} := ⟨by
    simpa using Hilbert.F.axm
      (φ := Axioms.Rfl (.atom (HasAxiomRfl.p Ax)) (.atom (HasAxiomRfl.q Ax)))
      (s := λ b =>
        if (HasAxiomRfl.p Ax) = b then φ
        else if (HasAxiomRfl.q Ax) = b then ψ
        else (.atom b))
      $ (HasAxiomRfl.mem_rfl);
  ⟩

instance [Ax.HasAxiomSer] : Entailment.HasAxiomSer (Hilbert.F Ax) where
  axiomSer! := ⟨by simpa using Hilbert.F.axm' $ HasAxiomSer.mem_ser⟩

instance [Ax.HasAxiomSym] : Entailment.HasAxiomSym (Hilbert.F Ax) where
  axiomSym! {φ ψ} := ⟨by
    simpa using Hilbert.F.axm
      (φ := Axioms.Sym (.atom (HasAxiomSym.p Ax)) (.atom (HasAxiomSym.q Ax)))
      (s := λ b =>
        if (HasAxiomSym.p Ax) = b then φ
        else if (HasAxiomSym.q Ax) = b then ψ
        else (.atom b))
      $ (HasAxiomSym.mem_sym);
  ⟩

instance [Ax.HasAxiomTra1] : Entailment.HasAxiomTra1 (Hilbert.F Ax) where
  axiomTra1! {φ ψ χ} := ⟨by
    simpa using Hilbert.F.axm
      (φ := Axioms.Tra1 (#(HasAxiomTra1.p Ax)) (#(HasAxiomTra1.q Ax)) (#(HasAxiomTra1.r Ax)))
      (s := λ b =>
        if (HasAxiomTra1.p Ax) = b then φ
        else if (HasAxiomTra1.q Ax) = b then ψ
        else if (HasAxiomTra1.r Ax) = b then χ
        else (.atom b)
      )
      $ (HasAxiomTra1.mem_tra1);
  ⟩

instance [Ax.HasAxiomHrd] : Entailment.HasAxiomHrd (Hilbert.F Ax) where
  axiomHrd! {φ} := ⟨by
    simpa using Hilbert.F.axm
      (φ := Axioms.Hrd (.atom (HasAxiomHrd.p Ax)))
      (s := λ b =>
        if (HasAxiomHrd.p Ax) = b then φ
        else (.atom b))
      $ (HasAxiomHrd.mem_hrd);
  ⟩
-/

end

end Hilbert.F



protected abbrev F : Logic ℕ := Hilbert.F ∅
instance : Entailment.F Propositional.F where


protected abbrev F_Ser : Logic ℕ := Hilbert.F { Axioms.Ser }
instance : Entailment.F Propositional.F_Ser where
instance : Entailment.HasAxiomSer Propositional.F_Ser where
  axiomSer! := ⟨by apply Hilbert.F.axm'; simp⟩


protected abbrev F_Rfl : Logic ℕ := Hilbert.F { Axioms.Rfl φ ψ | (φ) (ψ) }
instance : Entailment.F Propositional.F_Rfl where
instance : Entailment.HasAxiomRfl Propositional.F_Rfl where
  axiomRfl! {φ ψ} := ⟨by apply Hilbert.F.axm'; simp⟩


protected abbrev F_Sym : Logic ℕ := Hilbert.F { Axioms.Sym φ ψ | (φ) (ψ) }
instance : Entailment.F Propositional.F_Sym where
instance : Entailment.HasAxiomSym Propositional.F_Sym where
  axiomSym! {φ ψ} := ⟨by apply Hilbert.F.axm'; simp⟩


protected abbrev F_Rfl_Sym : Logic ℕ := Hilbert.F (
  { Axioms.Rfl φ ψ | (φ) (ψ) } ∪
  { Axioms.Sym φ ψ | (φ) (ψ) }
)
instance : Entailment.F Propositional.F_Rfl_Sym where
instance : Entailment.HasAxiomRfl Propositional.F_Rfl_Sym where
  axiomRfl! {_ _} := ⟨by apply Hilbert.F.axm'; simp⟩
instance : Entailment.HasAxiomSym Propositional.F_Rfl_Sym where
  axiomSym! {_ _} := ⟨by apply Hilbert.F.axm'; simp⟩


protected abbrev F_Tra1 : Logic ℕ := Hilbert.F { Axioms.Tra1 φ ψ χ | (φ) (ψ) (χ) }
instance : Entailment.F Propositional.F_Tra1 where
instance : Entailment.HasAxiomTra1 Propositional.F_Tra1 where
  axiomTra1! {_ _ _} := ⟨by apply Hilbert.F.axm'; simp⟩


protected abbrev F_Rfl_Tra1 : Logic ℕ := Hilbert.F (
  { Axioms.Rfl φ ψ | (φ) (ψ) } ∪
  { Axioms.Tra1 φ ψ χ | (φ) (ψ) (χ) }
)
instance : Entailment.F Propositional.F_Rfl_Tra1 where
instance : Entailment.HasAxiomRfl Propositional.F_Rfl_Tra1 where
  axiomRfl! {_ _} := ⟨by apply Hilbert.F.axm'; simp⟩
instance : Entailment.HasAxiomTra1 Propositional.F_Rfl_Tra1 where
  axiomTra1! {_ _ _} := ⟨by apply Hilbert.F.axm'; simp⟩


protected abbrev F_Tra1_Hrd : Logic ℕ := Hilbert.F (
  { Axioms.Tra1 φ ψ χ | (φ) (ψ) (χ) } ∪
  { Axioms.Hrd #a | (a : ℕ) }
)
instance : Entailment.F Propositional.F_Tra1_Hrd where
instance : Entailment.HasAxiomTra1 Propositional.F_Tra1_Hrd where
  axiomTra1! {φ ψ χ} := ⟨by apply Hilbert.F.axm'; simp⟩


protected abbrev F_Rfl_Tra1_Hrd := Hilbert.F (
  { Axioms.Rfl φ ψ | (φ) (ψ) } ∪
  { Axioms.Tra1 φ ψ χ | (φ) (ψ) (χ) } ∪
  { Axioms.Hrd #a | (a : ℕ) }
)
instance : Entailment.F Propositional.F_Rfl_Tra1_Hrd where
instance : Entailment.HasAxiomRfl Propositional.F_Rfl_Tra1_Hrd where
  axiomRfl! {_ _} := ⟨by apply Hilbert.F.axm'; simp⟩
instance : Entailment.HasAxiomTra1 Propositional.F_Rfl_Tra1_Hrd where
  axiomTra1! {_ _ _} := ⟨by apply Hilbert.F.axm'; simp⟩

end LO.Propositional
