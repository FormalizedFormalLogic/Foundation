import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Propositional.Hilbert.Axiom
import Foundation.Propositional.Formula
import Foundation.Propositional.Logic.Basic
import Foundation.Logic.Disjunctive

namespace LO.Propositional

variable {α : Type*}

inductive Hilbert (Ax : Axiom α) : Logic α
| axm {φ} (s : Substitution _) : φ ∈ Ax → Hilbert Ax (φ⟦s⟧)
| mdp {φ ψ}                    : Hilbert Ax (φ ➝ ψ) → Hilbert Ax φ → Hilbert Ax ψ
| verum                        : Hilbert Ax $ ⊤
| implyS φ ψ                   : Hilbert Ax $ φ ➝ ψ ➝ φ
| implyK φ ψ χ                 : Hilbert Ax $ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
| andElimL φ ψ                 : Hilbert Ax $ φ ⋏ ψ ➝ φ
| andElimR φ ψ                 : Hilbert Ax $ φ ⋏ ψ ➝ ψ
| andIntro φ ψ                  : Hilbert Ax $ φ ➝ ψ ➝ φ ⋏ ψ
| orIntroL φ ψ                 : Hilbert Ax $ φ ➝ φ ⋎ ψ
| orIntroR φ ψ                 : Hilbert Ax $ ψ ➝ φ ⋎ ψ
| orElim φ ψ χ                 : Hilbert Ax $ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

namespace Hilbert

variable {Ax Ax₁ Ax₂ : Axiom α}

@[grind] lemma axm' (h : φ ∈ Ax) : φ ∈ Hilbert Ax := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply axm _ h;

@[grind] lemma axm! (s : Substitution α) (h : φ ∈ Ax) : Hilbert Ax ⊢! (φ⟦s⟧)  := by
  apply Logic.iff_provable.mpr;
  apply axm s h;

@[grind] lemma axm'! (h : φ ∈ Ax) : Hilbert Ax ⊢! φ := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply axm! _ h;

@[grind]
lemma axm_instances! (h : φ ∈ Ax.instances) : Hilbert Ax ⊢! φ := by
  rcases h with ⟨ψ, _, s, rfl⟩;
  grind;

instance : Entailment.ModusPonens (Hilbert Ax) where
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.HasAxiomImply₁ (Hilbert Ax) := ⟨λ _ _ => by constructor; apply Hilbert.implyS⟩
instance : Entailment.HasAxiomImply₂ (Hilbert Ax) := ⟨λ _ _ _ => by constructor; apply Hilbert.implyK⟩
instance : Entailment.HasAxiomAndInst (Hilbert Ax) := ⟨λ _ _ => by constructor; apply Hilbert.andIntro⟩
instance : Entailment.Minimal (Hilbert Ax) where
  verum := by constructor; apply Hilbert.verum;
  and₁ _ _ := by constructor; apply Hilbert.andElimL;
  and₂ _ _ := by constructor; apply Hilbert.andElimR;
  or₁  _ _ := by constructor; apply Hilbert.orIntroL;
  or₂  _ _ := by constructor; apply Hilbert.orIntroR;
  or₃  _ _ _ := by constructor; apply Hilbert.orElim;

@[induction_eliminator]
protected lemma rec!
  {motive   : (φ : Formula α) → (Hilbert Ax ⊢! φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hpq : (Hilbert Ax) ⊢! φ ➝ ψ} → {hp : (Hilbert Ax) ⊢! φ} → (motive (φ ➝ ψ) hpq) → (motive φ hp) → (motive ψ (hpq ⨀ hp)))
  (verum    : motive ⊤ $ by simp)
  (implyS   : ∀ {φ ψ},   motive (Axioms.Imply₁ φ ψ) $ by simp)
  (implyK   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (andElimL : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ φ) $ by simp)
  (andElimR : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ ψ) $ by simp)
  (andIntro : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ ⋏ ψ) $ by simp)
  (orIntroL : ∀ {φ ψ},   motive (φ ➝ φ ⋎ ψ) $ by simp)
  (orIntroR : ∀ {φ ψ},   motive (ψ ➝ φ ⋎ ψ) $ by simp)
  (orElim   : ∀ {φ ψ χ}, motive ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ φ ⋎ ψ ➝ χ) $ by simp)
  : ∀ {φ}, (d : Hilbert Ax ⊢! φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | _ => grind;

instance : Logic.Substitution (Hilbert Ax) where
  subst! s h := by
    induction h using Hilbert.rec! with
    | axm s' h => simpa [Formula.subst_comp] using axm! (s' ∘ s) h;
    | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
    | _ => simp;

lemma weakerThan_of_provable_axioms (hs : Hilbert Ax₂ ⊢!* Ax₁) : (Hilbert Ax₁) ⪯ (Hilbert Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.rec! with
  | axm h => apply Logic.subst!; apply hs; assumption;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert Ax₁) ⪯ (Hilbert Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.axm'!;
  apply h;
  assumption;


section

variable [DecidableEq α]
open Axiom

instance [Ax.HasEFQ] : Entailment.HasAxiomEFQ (Hilbert Ax) where
  efq φ := by
    constructor;
    simpa using Hilbert.axm
      (s := λ b => if (HasEFQ.p Ax) = b then φ else (.atom b))
      (φ := Axioms.EFQ (.atom (HasEFQ.p Ax)))
      $ HasEFQ.mem_efq;
instance  [Ax.HasEFQ] : Entailment.Int (Hilbert Ax) where

instance [Ax.HasLEM] : Entailment.HasAxiomLEM (Hilbert Ax) where
  lem φ := by
    constructor;
    simpa using Hilbert.axm
      (s := λ b => if (HasLEM.p Ax) = b then φ else (.atom b))
      (φ := Axioms.LEM (.atom (HasLEM.p Ax)))
      $ HasLEM.mem_lem;

instance [Ax.HasWLEM] : Entailment.HasAxiomWeakLEM (Hilbert Ax) where
  wlem φ := by
    constructor;
    simpa using Hilbert.axm
      (s := λ b => if (HasWLEM.p Ax) = b then φ else (.atom b))
      (φ := Axioms.WeakLEM (.atom (HasWLEM.p Ax)))
      $ HasWLEM.mem_lem;

instance [Ax.HasDummett] : Entailment.HasAxiomDummett (Hilbert Ax) where
  dummett φ ψ := by
    constructor;
    simpa [HasDummett.ne_pq] using Hilbert.axm
      (φ := Axioms.Dummett (.atom (HasDummett.p Ax)) (.atom (HasDummett.q Ax)))
      (s := λ b =>
        if (HasDummett.p Ax) = b then φ
        else if (HasDummett.q Ax) = b then ψ
        else (.atom b))
      $ (HasDummett.mem_m);

instance [Ax.HasPeirce] : Entailment.HasAxiomPeirce (Hilbert Ax) where
  peirce φ ψ := by
    constructor;
    simpa [HasPeirce.ne_pq] using Hilbert.axm
      (φ := Axioms.Peirce (.atom (HasPeirce.p Ax)) (.atom (HasPeirce.q Ax)))
      (s := λ b =>
        if (HasPeirce.p Ax) = b then φ
        else if (HasPeirce.q Ax) = b then ψ
        else (.atom b))
      $ (HasPeirce.mem_peirce);

instance [Ax.HasKrieselPutnam] : Entailment.HasAxiomKrieselPutnam (Hilbert Ax) where
  krieselputnam φ ψ χ := by
    constructor;
    simpa [HasKrieselPutnam.ne_pq, HasKrieselPutnam.ne_qr, HasKrieselPutnam.ne_rp.symm] using Hilbert.axm
      (φ := Axioms.KrieselPutnam (.atom (HasKrieselPutnam.p Ax)) (.atom (HasKrieselPutnam.q Ax)) (.atom (HasKrieselPutnam.r Ax)))
      (s := λ b =>
        if (HasKrieselPutnam.p Ax) = b then φ
        else if (HasKrieselPutnam.q Ax) = b then ψ
        else if (HasKrieselPutnam.r Ax) = b then χ
        else (.atom b))
      $ (HasKrieselPutnam.mem_kriesel_putnam);

end

end Hilbert


protected abbrev Int.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0)}
namespace Int.axioms
instance : Int.axioms.HasEFQ where p := 0;
end Int.axioms
protected abbrev Int := Hilbert Int.axioms
notation "𝐈𝐧𝐭" => Propositional.Int
instance : Entailment.Int 𝐈𝐧𝐭 where


protected abbrev Cl.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0), Axioms.LEM (.atom 0)}
namespace Cl.axioms
instance : Cl.axioms.HasEFQ where p := 0;
instance : Cl.axioms.HasLEM where p := 0;
end Cl.axioms
protected abbrev Cl := Hilbert Cl.axioms
notation "𝐂𝐥" => Propositional.Cl
instance : Entailment.Cl 𝐂𝐥 where


protected abbrev KC.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0), Axioms.WeakLEM (.atom 0)}
namespace KC.axioms
instance : KC.axioms.HasEFQ where p := 0;
instance : KC.axioms.HasWLEM where p := 0;
end KC.axioms
protected abbrev KC := Hilbert KC.axioms
notation "𝐊𝐂" => Propositional.KC
instance : Entailment.KC 𝐊𝐂 where


protected abbrev LC.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0), Axioms.Dummett (.atom 0) (.atom 1)}
namespace LC.axioms
instance : LC.axioms.HasEFQ where p := 0;
instance : LC.axioms.HasDummett where p := 0; q := 1;
end LC.axioms
protected abbrev LC := Hilbert LC.axioms
notation "𝐋𝐂" => Propositional.LC
instance : Entailment.LC 𝐋𝐂 where


protected abbrev KrieselPutnam.axioms : Axiom ℕ := {Axioms.EFQ (.atom 0), Axioms.KrieselPutnam (.atom 0) (.atom 1) (.atom 2)}
namespace KrieselPutnam.axioms
instance : KrieselPutnam.axioms.HasEFQ where p := 0;
instance : KrieselPutnam.axioms.HasKrieselPutnam where p := 0; q := 1; r := 2;
end KrieselPutnam.axioms
protected abbrev KrieselPutnam := Hilbert KrieselPutnam.axioms
notation "𝐊𝐏" => Propositional.KrieselPutnam
instance : Entailment.KrieselPutnam 𝐊𝐏 where


end LO.Propositional
