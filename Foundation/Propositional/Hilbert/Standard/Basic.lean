module

public import Foundation.Propositional.Entailment.Int.DNE_of_LEM
public import Foundation.Propositional.Hilbert.Axiom
public import Foundation.Propositional.Logic.Basic

@[expose] public section

namespace LO.Propositional

variable {α : Type*} {Ax Ax₁ Ax₂ : Axiom α} {φ ψ χ : Formula α}


inductive Hilbert.Standard (Ax : Axiom α) : Logic α
| axm {φ} (s : Substitution _) : φ ∈ Ax → Hilbert.Standard Ax (φ⟦s⟧)
| mdp {φ ψ}                    : Hilbert.Standard Ax (φ ➝ ψ) → Hilbert.Standard Ax φ → Hilbert.Standard Ax ψ
| verum                        : Hilbert.Standard Ax $ ⊤
| implyS φ ψ                   : Hilbert.Standard Ax $ φ ➝ ψ ➝ φ
| implyK φ ψ χ                 : Hilbert.Standard Ax $ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
| andElimL φ ψ                 : Hilbert.Standard Ax $ φ ⋏ ψ ➝ φ
| andElimR φ ψ                 : Hilbert.Standard Ax $ φ ⋏ ψ ➝ ψ
| andIntro φ ψ                 : Hilbert.Standard Ax $ φ ➝ ψ ➝ φ ⋏ ψ
| orIntroL φ ψ                 : Hilbert.Standard Ax $ φ ➝ φ ⋎ ψ
| orIntroR φ ψ                 : Hilbert.Standard Ax $ ψ ➝ φ ⋎ ψ
| orElim φ ψ χ                 : Hilbert.Standard Ax $ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)


namespace Hilbert.Standard

@[grind →]
lemma axm' (h : φ ∈ Ax) : φ ∈ Hilbert.Standard Ax := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply axm _ h;

@[grind <=]
lemma axm! (s : Substitution α) (h : φ ∈ Ax) : Hilbert.Standard Ax ⊢ (φ⟦s⟧)  := by
  apply Logic.iff_provable.mpr;
  apply axm s h;

@[grind →]
lemma axm'! (h : φ ∈ Ax) : Hilbert.Standard Ax ⊢ φ := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply axm! _ h;

@[grind <=]
lemma axm_instances! (h : φ ∈ Ax.instances) : Hilbert.Standard Ax ⊢ φ := by
  rcases h with ⟨ψ, _, s, rfl⟩;
  grind;

instance : Entailment.ModusPonens (Hilbert.Standard Ax) where
  mdp h₁ h₂ := by
    constructor;
    apply mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.HasAxiomImplyK (Hilbert.Standard Ax) := ⟨λ {_ _} => by constructor; apply implyS⟩
instance : Entailment.HasAxiomImplyS (Hilbert.Standard Ax) := ⟨λ {_ _ _} => by constructor; apply implyK⟩
instance : Entailment.HasAxiomAndInst (Hilbert.Standard Ax) := ⟨λ {_ _} => by constructor; apply andIntro⟩
instance : Entailment.Minimal (Hilbert.Standard Ax) where
  verum := by constructor; apply verum;
  and₁ {_ _} := by constructor; apply andElimL;
  and₂ {_ _} := by constructor; apply andElimR;
  or₁  {_ _} := by constructor; apply orIntroL;
  or₂  {_ _} := by constructor; apply orIntroR;
  or₃  {_ _ _} := by constructor; apply orElim;

@[induction_eliminator]
protected lemma rec!
  {motive   : (φ : Formula α) → (Hilbert.Standard Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hpq : (Hilbert.Standard Ax) ⊢ φ ➝ ψ} → {hp : (Hilbert.Standard Ax) ⊢ φ} → (motive (φ ➝ ψ) hpq) → (motive φ hp) → (motive ψ (hpq ⨀ hp)))
  (verum    : motive ⊤ $ by simp)
  (implyS   : ∀ {φ ψ},   motive (Axioms.ImplyK φ ψ) $ by simp)
  (implyK   : ∀ {φ ψ χ}, motive (Axioms.ImplyS φ ψ χ) $ by simp)
  (andElimL : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ φ) $ by simp)
  (andElimR : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ ψ) $ by simp)
  (andIntro : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ ⋏ ψ) $ by simp)
  (orIntroL : ∀ {φ ψ},   motive (φ ➝ φ ⋎ ψ) $ by simp)
  (orIntroR : ∀ {φ ψ},   motive (ψ ➝ φ ⋎ ψ) $ by simp)
  (orElim   : ∀ {φ ψ χ}, motive ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ φ ⋎ ψ ➝ χ) $ by simp)
  : ∀ {φ}, (d : Hilbert.Standard Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | _ => grind;

instance : Logic.Substitution (Hilbert.Standard Ax) where
  subst s h := by
    induction h using Standard.rec! with
    | axm s' h => simpa [Formula.subst_comp] using axm! (s' ∘ s) h;
    | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
    | _ => first
      | apply Entailment.verum!;
      | apply Entailment.implyK!
      | apply Entailment.implyS!
      | apply Entailment.and₁!
      | apply Entailment.and₂!
      | apply Entailment.and₃!
      | apply Entailment.or₁!
      | apply Entailment.or₂!
      | apply Entailment.or₃!;

lemma weakerThan_of_provable_axioms (hs : Hilbert.Standard Ax₂ ⊢* Ax₁) : (Hilbert.Standard Ax₁) ⪯ (Hilbert.Standard Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Standard.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => first
    | apply Entailment.verum!;
    | apply Entailment.implyK!
    | apply Entailment.implyS!
    | apply Entailment.and₁!
    | apply Entailment.and₂!
    | apply Entailment.and₃!
    | apply Entailment.or₁!
    | apply Entailment.or₂!
    | apply Entailment.or₃!;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert.Standard Ax₁) ⪯ (Hilbert.Standard Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply axm'!;
  apply h;
  assumption;


section

variable [DecidableEq α]
open Axiom

instance [Ax.HasEFQ] : Entailment.HasAxiomEFQ (Hilbert.Standard Ax) where
  efq {φ} := by
    constructor;
    simpa using axm
      (s := λ b => if (HasEFQ.p Ax) = b then φ else (.atom b))
      (φ := Axioms.EFQ (.atom (HasEFQ.p Ax)))
      $ HasEFQ.mem_efq;
instance  [Ax.HasEFQ] : Entailment.Int (Hilbert.Standard Ax) where

instance [Ax.HasLEM] : Entailment.HasAxiomLEM (Hilbert.Standard Ax) where
  lem {φ} := by
    constructor;
    simpa using axm
      (s := λ b => if (HasLEM.p Ax) = b then φ else (.atom b))
      (φ := Axioms.LEM (.atom (HasLEM.p Ax)))
      $ HasLEM.mem_lem;

instance [Ax.HasWLEM] : Entailment.HasAxiomWLEM (Hilbert.Standard Ax) where
  wlem {φ} := by
    constructor;
    simpa using axm
      (s := λ b => if (HasWLEM.p Ax) = b then φ else (.atom b))
      (φ := Axioms.WLEM (.atom (HasWLEM.p Ax)))
      $ HasWLEM.mem_lem;

instance [Ax.HasDummett] : Entailment.HasAxiomDummett (Hilbert.Standard Ax) where
  dummett {φ ψ} := by
    constructor;
    simpa [HasDummett.ne_pq] using axm
      (φ := Axioms.Dummett (.atom (HasDummett.p Ax)) (.atom (HasDummett.q Ax)))
      (s := λ b =>
        if (HasDummett.p Ax) = b then φ
        else if (HasDummett.q Ax) = b then ψ
        else (.atom b))
      $ (HasDummett.mem_m);

instance [Ax.HasPeirce] : Entailment.HasAxiomPeirce (Hilbert.Standard Ax) where
  peirce {φ ψ} := by
    constructor;
    simpa [HasPeirce.ne_pq] using axm
      (φ := Axioms.Peirce (.atom (HasPeirce.p Ax)) (.atom (HasPeirce.q Ax)))
      (s := λ b =>
        if (HasPeirce.p Ax) = b then φ
        else if (HasPeirce.q Ax) = b then ψ
        else (.atom b))
      $ (HasPeirce.mem_peirce);

instance [Ax.HasKreiselPutnam] : Entailment.HasAxiomKreiselPutnam (Hilbert.Standard Ax) where
  kreiselputnam {φ ψ χ} := by
    constructor;
    simpa [HasKreiselPutnam.ne_pq, HasKreiselPutnam.ne_qr, HasKreiselPutnam.ne_rp.symm] using axm
      (φ := Axioms.KreiselPutnam (.atom (HasKreiselPutnam.p Ax)) (.atom (HasKreiselPutnam.q Ax)) (.atom (HasKreiselPutnam.r Ax)))
      (s := λ b =>
        if (HasKreiselPutnam.p Ax) = b then φ
        else if (HasKreiselPutnam.q Ax) = b then ψ
        else if (HasKreiselPutnam.r Ax) = b then χ
        else (.atom b))
      $ (HasKreiselPutnam.mem_kreisel_putnam);

end

end Hilbert.Standard



protected abbrev Int.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0)}
namespace Int.axioms
instance : Int.axioms.HasEFQ where p := 0;
end Int.axioms
protected abbrev Int := Hilbert.Standard Int.axioms
instance : Entailment.Int Propositional.Int where


protected abbrev Cl.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0), Axioms.LEM (.atom 0)}
namespace Cl.axioms
instance : Cl.axioms.HasEFQ where p := 0;
instance : Cl.axioms.HasLEM where p := 0;
end Cl.axioms
protected abbrev Cl := Hilbert.Standard Cl.axioms
instance : Entailment.Cl Propositional.Cl where


protected abbrev KC.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0), Axioms.WLEM (.atom 0)}
namespace KC.axioms
instance : KC.axioms.HasEFQ where p := 0;
instance : KC.axioms.HasWLEM where p := 0;
end KC.axioms
protected abbrev KC := Hilbert.Standard KC.axioms
instance : Entailment.KC Propositional.KC where


protected abbrev LC.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0), Axioms.Dummett (.atom 0) (.atom 1)}
namespace LC.axioms
instance : LC.axioms.HasEFQ where p := 0;
instance : LC.axioms.HasDummett where p := 0; q := 1;
end LC.axioms
protected abbrev LC := Hilbert.Standard LC.axioms
instance : Entailment.LC Propositional.LC where


protected abbrev KreiselPutnam.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0), Axioms.KreiselPutnam (.atom 0) (.atom 1) (.atom 2)}
namespace KreiselPutnam.axioms
instance : KreiselPutnam.axioms.HasEFQ where p := 0;
instance : KreiselPutnam.axioms.HasKreiselPutnam where p := 0; q := 1; r := 2;
end KreiselPutnam.axioms
protected abbrev KreiselPutnam := Hilbert.Standard KreiselPutnam.axioms
instance : Entailment.KreiselPutnam Propositional.KreiselPutnam where


end LO.Propositional
end
