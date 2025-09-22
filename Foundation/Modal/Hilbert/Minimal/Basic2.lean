import Foundation.Modal.Formula
import Foundation.Modal.Entailment.K
import Foundation.Modal.Entailment.EMCN
import Foundation.Modal.Entailment.END
import Foundation.Logic.HilbertStyle.Lukasiewicz
import Foundation.Logic.Incomparable
import Foundation.Modal.Logic.Basic
import Foundation.Modal.Hilbert.Axiom

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

inductive Hilbert.WithRE {α} (Ax : Axiom α) : Logic α
| axm {φ} (s : Substitution _) : φ ∈ Ax → WithRE Ax (φ⟦s⟧)
| mdp {φ ψ}     : WithRE Ax (φ ➝ ψ) → WithRE Ax φ → WithRE Ax ψ
| re {φ ψ}      : WithRE Ax (φ ⭤ ψ) → WithRE Ax (□φ ⭤ □ψ)
| imply₁ φ ψ    : WithRE Ax $ Axioms.Imply₁ φ ψ
| imply₂ φ ψ χ  : WithRE Ax $ Axioms.Imply₂ φ ψ χ
| ec φ ψ        : WithRE Ax $ Axioms.ElimContra φ ψ

namespace Hilbert.WithRE

variable {Ax Ax₁ Ax₂ : Axiom α}

@[grind] lemma axm! {φ} (s : Substitution _) (h : φ ∈ Ax) : WithRE Ax ⊢! φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply axm s h;

@[grind] lemma axm'! {φ} (h : φ ∈ Ax) : WithRE Ax ⊢! φ := by simpa using axm! .id h;

instance : Entailment.Lukasiewicz (Hilbert.WithRE Ax) where
  imply₁ _ _ := by constructor; apply Hilbert.WithRE.imply₁;
  imply₂ _ _ _ := by constructor; apply Hilbert.WithRE.imply₂;
  elimContra _ _ := by constructor; apply Hilbert.WithRE.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.WithRE.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.E (Hilbert.WithRE Ax) where
  re h := by constructor; apply Hilbert.WithRE.re; exact h.1;

instance : Logic.Substitution (Hilbert.WithRE Ax) where
  subst {φ} s h := by
    constructor;
    replace h := h.1;
    induction h with
    | @axm _ s' ih => simpa using axm (s := s' ∘ s) ih;
    | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
    | re hφψ ihφψ => apply re; assumption;
    | imply₁ φ ψ => apply imply₁;
    | imply₂ φ ψ χ => apply imply₂;
    | ec φ ψ => apply ec;

protected lemma rec!
  {motive   : (φ : Formula α) → (WithRE Ax ⊢! φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (WithRE Ax) ⊢! φ ➝ ψ} → {hφ : (WithRE Ax) ⊢! φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (re       : ∀ {φ ψ}, {hφψ : (WithRE Ax) ⊢! φ ⭤ ψ} → motive (φ ⭤ ψ) hφψ → motive (□φ ⭤ □ψ) (re! hφψ))
  (imply₁   : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : WithRE Ax ⊢! φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | re hφψ ihφψ =>
    apply re;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
  | imply₁ φ ψ => apply imply₁;
  | imply₂ φ ψ χ => apply imply₂;
  | ec φ ψ => apply ec;

lemma weakerThan_of_provable_axioms (hs : WithRE Ax₂ ⊢!* Ax₁) : (WithRE Ax₁) ⪯ (WithRE Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using WithRE.rec! with
  | axm h => apply Logic.subst!; apply hs; assumption;
  | @re φ ψ h => apply re!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (WithRE Ax₁) ⪯ (WithRE Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply WithRE.axm'!;
  apply h;
  assumption;

open Axiom


section

variable [DecidableEq α]

instance instHasAxiomM [Ax.HasM] : Entailment.HasAxiomM (Hilbert.WithRE Ax) where
  M φ ψ := by
    constructor;
    simpa [HasM.ne_pq] using Hilbert.WithRE.axm
      (φ := Axioms.M (.atom (HasM.p Ax)) (.atom (HasM.q Ax)))
      (s := λ b => if (HasM.p Ax) = b then φ else if (HasM.q Ax) = b then ψ else (.atom b))
      (by exact HasM.mem_m);

instance instHasAxiomC [Ax.HasC] : Entailment.HasAxiomC (Hilbert.WithRE Ax) where
  C φ ψ := by
    constructor;
    simpa [HasC.ne_pq] using Hilbert.WithRE.axm
      (φ := Axioms.C (.atom (HasC.p Ax)) (.atom (HasC.q Ax)))
      (s := λ b => if (HasC.p Ax) = b then φ else if (HasC.q Ax) = b then ψ else (.atom b))
      (by exact HasC.mem_c);

instance instHasAxiomN [Ax.HasN] : Entailment.HasAxiomN (Hilbert.WithRE Ax) where
  N := by constructor; apply Hilbert.WithRE.axm (φ := Axioms.N) (s := .id) (by exact HasN.mem_n);

instance instHasAxiomK [Ax.HasK] : Entailment.HasAxiomK (Hilbert.WithRE Ax) where
  K φ ψ := by
    constructor;
    simpa [HasK.ne_pq] using Hilbert.WithRE.axm
      (φ := Axioms.K (.atom (HasK.p Ax)) (.atom (HasK.q Ax)))
      (s := λ b => if (HasK.p Ax) = b then φ else if (HasK.q Ax) = b then ψ else (.atom b))
      (by exact HasK.mem_K);

instance instHasAxiomT [Ax.HasT] : Entailment.HasAxiomT (Hilbert.WithRE Ax) where
  T φ := by
    constructor;
    simpa using Hilbert.WithRE.axm
      (φ := Axioms.T (.atom (HasT.p Ax)))
      (s := λ b => if (HasT.p Ax) = b then φ else (.atom b))
      (by exact HasT.mem_T);

instance instHasAxiomD [Ax.HasD] : Entailment.HasAxiomD (Hilbert.WithRE Ax) where
  D φ := by
    constructor;
    simpa using Hilbert.WithRE.axm
      (φ := Axioms.D (.atom (HasD.p Ax)))
      (s := λ b => if (HasD.p Ax) = b then φ else (.atom b))
      (by exact HasD.mem_D);

instance instHasAxiomP [Ax.HasP] : Entailment.HasAxiomP (Hilbert.WithRE Ax) where
  P := by constructor; simpa using Hilbert.WithRE.axm (φ := Axioms.P) (s := .id) (by exact HasP.mem_P);

instance instHasAxiomFour [Ax.HasFour] : Entailment.HasAxiomFour (Hilbert.WithRE Ax) where
  Four φ := by
    constructor;
    simpa using Hilbert.WithRE.axm
      (φ := Axioms.Four (.atom (HasFour.p Ax)))
      (s := λ b => if (HasFour.p Ax) = b then φ else (.atom b))
      (by exact HasFour.mem_Four);

end

end Hilbert.WithRE


section

open Hilbert.WithRE

protected abbrev E : Logic ℕ := Hilbert.WithRE ∅

protected abbrev EM.axioms : Axiom ℕ := {Axioms.M (.atom 0) (.atom 1)}
protected abbrev EM : Logic ℕ := Hilbert.WithRE EM.axioms
instance : EM.axioms.HasM where p := 0; q := 1;
instance : Entailment.HasAxiomM Modal.EM := instHasAxiomM
instance : Entailment.EM Modal.EM where

protected abbrev EC : Logic ℕ := Hilbert.WithRE {Axioms.C (.atom 0) (.atom 1)}

protected abbrev EN.axioms : Axiom ℕ := {Axioms.N}
protected abbrev EN : Logic ℕ := Hilbert.WithRE EN.axioms
instance : EN.axioms.HasN where mem_n := by simp;
instance : Entailment.HasAxiomN Modal.EN := instHasAxiomN

protected abbrev EMC : Logic ℕ := Hilbert.WithRE {Axioms.M (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1)}

protected abbrev EMN : Logic ℕ := Hilbert.WithRE {Axioms.M (.atom 0) (.atom 1), Axioms.N}

protected abbrev ECN : Logic ℕ := Hilbert.WithRE {Axioms.C (.atom 0) (.atom 1), Axioms.N}

protected abbrev EMCN : Logic ℕ := Hilbert.WithRE {Axioms.M (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1), Axioms.N}

protected abbrev EK.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1)}
protected abbrev EK : Logic ℕ := Hilbert.WithRE EK.axioms
instance : EK.axioms.HasK where p := 0; q := 1;
instance : Entailment.HasAxiomK Modal.EK := instHasAxiomK

protected abbrev E4 : Logic ℕ := Hilbert.WithRE {Axioms.Four (.atom 0)}

protected abbrev ED : Logic ℕ := Hilbert.WithRE {Axioms.D (.atom 0)}

protected abbrev END : Logic ℕ := Hilbert.WithRE {Axioms.N, Axioms.D (.atom 0)}

protected abbrev EP : Logic ℕ := Hilbert.WithRE {Axioms.P}

protected abbrev ET : Logic ℕ := Hilbert.WithRE {Axioms.T (.atom 0)}

protected abbrev EMT : Logic ℕ := Hilbert.WithRE {Axioms.M (.atom 0) (.atom 1), Axioms.T (.atom 0)}

protected abbrev EMT4 : Logic ℕ := Hilbert.WithRE {Axioms.M (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}

protected abbrev EMCN4 : Logic ℕ := Hilbert.WithRE {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.Four (.atom 0)
}

protected abbrev EMCNT : Logic ℕ := Hilbert.WithRE {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.T (.atom 0)
}

protected abbrev EMCNT4 : Logic ℕ := Hilbert.WithRE {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.T (.atom 0),
  Axioms.Four (.atom 0)
}

end

end LO.Modal
