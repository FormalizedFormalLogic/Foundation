import Foundation.Modal.Formula
import Foundation.Modal.Entailment.K
import Foundation.Modal.Entailment.EMCN
import Foundation.Modal.Entailment.END
import Foundation.Modal.Entailment.ET5
import Foundation.Modal.Entailment.EMK
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

@[grind] lemma axm! {φ} (s : Substitution _) (h : φ ∈ Ax) : WithRE Ax ⊢ φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply axm s h;

@[grind] lemma axm'! {φ} (h : φ ∈ Ax) : WithRE Ax ⊢ φ := by simpa using axm! .id h;

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
    rw [Logic.iff_provable] at h ⊢;
    induction h with
    | @axm _ s' ih => simpa using axm (s := s' ∘ s) ih;
    | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
    | re hφψ ihφψ => apply re; assumption;
    | imply₁ φ ψ => apply imply₁;
    | imply₂ φ ψ χ => apply imply₂;
    | ec φ ψ => apply ec;

protected lemma rec!
  {motive   : (φ : Formula α) → (WithRE Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (WithRE Ax) ⊢ φ ➝ ψ} → {hφ : (WithRE Ax) ⊢ φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (re       : ∀ {φ ψ}, {hφψ : (WithRE Ax) ⊢ φ ⭤ ψ} → motive (φ ⭤ ψ) hφψ → motive (□φ ⭤ □ψ) (re! hφψ))
  (imply₁   : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : WithRE Ax ⊢ φ) → motive φ d := by
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

lemma weakerThan_of_provable_axioms (hs : WithRE Ax₂ ⊢* Ax₁) : (WithRE Ax₁) ⪯ (WithRE Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using WithRE.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
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

instance [Ax.HasB] : Entailment.HasAxiomB (Hilbert.WithRE Ax) where
  B φ := by
    constructor;
    simpa using Hilbert.WithRE.axm
      (φ := Axioms.B (.atom (HasB.p Ax)))
      (s := λ b => if (HasB.p Ax) = b then φ else (.atom b))
      (by exact HasB.mem_B);

instance [Ax.HasFive] : Entailment.HasAxiomFive (Hilbert.WithRE Ax) where
  Five φ := by
    constructor;
    simpa using Hilbert.WithRE.axm
      (φ := Axioms.Five (.atom (HasFive.p Ax)))
      (s := λ b => if (HasFive.p Ax) = b then φ else (.atom b))
      (by exact HasFive.mem_Five);

end

end Hilbert.WithRE


section

open Hilbert.WithRE

protected abbrev E : Logic ℕ := Hilbert.WithRE ∅

protected abbrev EM.axioms : Axiom ℕ := {Axioms.M (.atom 0) (.atom 1)}
instance : EM.axioms.HasM where p := 0; q := 1;
protected abbrev EM : Logic ℕ := Hilbert.WithRE EM.axioms
instance : Entailment.EM Modal.EM where

protected abbrev EC.axioms : Axiom ℕ := {Axioms.C (.atom 0) (.atom 1)}
instance : EC.axioms.HasC where p := 0; q := 1;
protected abbrev EC : Logic ℕ := Hilbert.WithRE EC.axioms
instance : Entailment.EC Modal.EC where

protected abbrev EN.axioms : Axiom ℕ := {Axioms.N}
instance : EN.axioms.HasN where mem_n := by simp;
protected abbrev EN : Logic ℕ := Hilbert.WithRE EN.axioms
instance : Entailment.EN Modal.EN where

protected abbrev EMC.axioms : Axiom ℕ := {Axioms.M (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1)}
instance : EMC.axioms.HasM where p := 0; q := 1;
instance : EMC.axioms.HasC where p := 0; q := 1;
protected abbrev EMC : Logic ℕ := Hilbert.WithRE EMC.axioms
instance : Entailment.EMC Modal.EMC where

protected abbrev EMN.axioms : Axiom ℕ := {Axioms.M (.atom 0) (.atom 1), Axioms.N}
instance : EMN.axioms.HasM where p := 0; q := 1;
instance : EMN.axioms.HasN where
protected abbrev EMN : Logic ℕ := Hilbert.WithRE EMN.axioms
instance : Entailment.EMN Modal.EMN where

protected abbrev ECN.axioms : Axiom ℕ := {Axioms.C (.atom 0) (.atom 1), Axioms.N}
instance : ECN.axioms.HasC where p := 0; q := 1
instance : ECN.axioms.HasN where
protected abbrev ECN : Logic ℕ := Hilbert.WithRE ECN.axioms
instance : Entailment.ECN Modal.ECN where

protected abbrev EMCN.axioms : Axiom ℕ := {Axioms.M (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1), Axioms.N}
instance : EMCN.axioms.HasM where p := 0; q := 1
instance : EMCN.axioms.HasC where p := 0; q := 1
instance : EMCN.axioms.HasN where
protected abbrev EMCN : Logic ℕ := Hilbert.WithRE EMCN.axioms
instance : Entailment.EMCN Modal.EMCN where

protected abbrev EK.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1)}
instance : EK.axioms.HasK where p := 0; q := 1;
protected abbrev EK : Logic ℕ := Hilbert.WithRE EK.axioms
instance : Entailment.EK Modal.EK where

protected abbrev EKC.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1)}
namespace EKC.axioms
instance : EKC.axioms.HasK where p := 0; q := 1;
instance : EKC.axioms.HasC where p := 0; q := 1;
end EKC.axioms
protected abbrev EKC : Logic ℕ := Hilbert.WithRE EKC.axioms
instance : Entailment.EK Modal.EKC where
instance : Entailment.EC Modal.EKC where

protected abbrev EKP.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.P}
namespace EKP.axioms
instance : EKP.axioms.HasK where p := 0; q := 1;
instance : EKP.axioms.HasP where mem_P := by simp;
end EKP.axioms
protected abbrev EKP : Logic ℕ := Hilbert.WithRE EKP.axioms
instance : Entailment.EK Modal.EKP where
instance : Entailment.HasAxiomP Modal.EKP := instHasAxiomP

protected abbrev ECKP.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1), Axioms.P}
namespace ECKP.axioms
instance : ECKP.axioms.HasK where p := 0; q := 1;
instance : ECKP.axioms.HasC where p := 0; q := 1;
instance : ECKP.axioms.HasP where mem_P := by simp;
end ECKP.axioms
protected abbrev ECKP : Logic ℕ := Hilbert.WithRE ECKP.axioms
instance : Entailment.EK Modal.ECKP where
instance : Entailment.EC Modal.ECKP where
instance : Entailment.HasAxiomP Modal.ECKP := instHasAxiomP

protected abbrev EKT.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0)}
namespace EKT.axioms
instance : EKT.axioms.HasK where p := 0; q := 1;
instance : EKT.axioms.HasT where p := 0;
end EKT.axioms
protected abbrev EKT : Logic ℕ := Hilbert.WithRE EKT.axioms
instance : Entailment.EK Modal.EKT where
instance : Entailment.ET Modal.EKT where

protected abbrev ECKT.axioms : Axiom ℕ := {
  Axioms.K (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.T (.atom 0)
}
namespace ECKT.axioms
instance : ECKT.axioms.HasK where p := 0; q := 1;
instance : ECKT.axioms.HasC where p := 0; q := 1;
instance : ECKT.axioms.HasT where p := 0;
end ECKT.axioms
protected abbrev ECKT : Logic ℕ := Hilbert.WithRE ECKT.axioms
instance : Entailment.EK Modal.ECKT where
instance : Entailment.EC Modal.ECKT where
instance : Entailment.ET Modal.ECKT where

protected abbrev E4.axioms : Axiom ℕ := {Axioms.Four (.atom 0)}
instance : E4.axioms.HasFour where p := 0; mem_Four := by simp;
protected abbrev E4 : Logic ℕ := Hilbert.WithRE E4.axioms
instance : Entailment.E4 Modal.E4 where

protected abbrev EN4.axioms : Axiom ℕ := {Axioms.N, Axioms.Four (.atom 0)}
namespace EN4.axioms
instance : EN4.axioms.HasN where
instance : EN4.axioms.HasFour where p := 0;
end EN4.axioms
protected abbrev EN4 : Logic ℕ := Hilbert.WithRE EN4.axioms
instance : Entailment.EN Modal.EN4 where
instance : Entailment.E4 Modal.EN4 where
instance : Modal.E4 ⪯ Modal.EN4 := weakerThan_of_subset_axioms (by simp)

protected abbrev ET4.axioms : Axiom ℕ := {Axioms.Four (.atom 0), Axioms.T (.atom 0)}
namespace ET4.axioms
instance : ET4.axioms.HasFour where p := 0;
instance : ET4.axioms.HasT where p := 0;
end ET4.axioms
protected abbrev ET4 : Logic ℕ := Hilbert.WithRE ET4.axioms
instance : Entailment.E Modal.ET4 where
instance : Entailment.ET Modal.ET4 where
instance : Entailment.E4 Modal.ET4 where

protected abbrev ENT4.axioms : Axiom ℕ := {Axioms.N, Axioms.T (.atom 0), Axioms.Four (.atom 0)}
namespace ENT4.axioms
instance : ENT4.axioms.HasN where
instance : ENT4.axioms.HasT where p := 0;
instance : ENT4.axioms.HasFour where p := 0;
end ENT4.axioms
protected abbrev ENT4 : Logic ℕ := Hilbert.WithRE ENT4.axioms
instance : Entailment.EN Modal.ENT4 where
instance : Entailment.ET Modal.ENT4 where
instance : Entailment.E4 Modal.ENT4 where

protected abbrev ED.axioms : Axiom ℕ := {Axioms.D (.atom 0)}
instance : ED.axioms.HasD where p := 0; mem_D := by simp;
protected abbrev ED : Logic ℕ := Hilbert.WithRE ED.axioms
instance : Entailment.HasAxiomD Modal.ED := instHasAxiomD

protected abbrev END.axioms : Axiom ℕ := {Axioms.N, Axioms.D (.atom 0)}
instance : END.axioms.HasN where
instance : END.axioms.HasD where p := 0; mem_D := by simp
protected abbrev END : Logic ℕ := Hilbert.WithRE {Axioms.N, Axioms.D (.atom 0)}
instance : Entailment.END Modal.END where

protected abbrev END4.axioms : Axiom ℕ := {Axioms.N, Axioms.D (.atom 0), Axioms.Four (.atom 0)}
namespace END4.axioms
instance : END4.axioms.HasN where
instance : END4.axioms.HasD where p := 0;
instance : END4.axioms.HasFour where p := 0; mem_Four := by simp;
end END4.axioms
protected abbrev END4 : Logic ℕ := Hilbert.WithRE END4.axioms
instance : Entailment.END Modal.END where
instance : Entailment.E4 Modal.END4 where

protected abbrev EMND4.axioms : Axiom ℕ := {Axioms.M (.atom 0) (.atom 1), Axioms.N, Axioms.D (.atom 0), Axioms.Four (.atom 0)}
namespace EMND4.axioms
instance : EMND4.axioms.HasM where p := 0; q := 1;
instance : EMND4.axioms.HasN where
instance : EMND4.axioms.HasD where p := 0;
instance : EMND4.axioms.HasFour where p := 0; mem_Four := by simp;
end EMND4.axioms
protected abbrev EMND4 : Logic ℕ := Hilbert.WithRE EMND4.axioms
instance : Entailment.END Modal.END where
instance : Entailment.EM Modal.EMND4 where
instance : Entailment.E4 Modal.EMND4 where


protected abbrev EP.axioms : Axiom ℕ := {Axioms.P}
instance : EP.axioms.HasP where mem_P := by simp;
protected abbrev EP : Logic ℕ := Hilbert.WithRE EP.axioms
instance : Entailment.HasAxiomP Modal.EP := instHasAxiomP

protected abbrev ET.axioms : Axiom ℕ := {Axioms.T (.atom 0)}
namespace ET.axioms
instance : ET.axioms.HasT where p := 0;
end ET.axioms
protected abbrev ET : Logic ℕ := Hilbert.WithRE ET.axioms
instance : Entailment.ET Modal.ET where

protected abbrev EMT.axioms : Axiom ℕ := {Axioms.M (.atom 0) (.atom 1), Axioms.T (.atom 0)}
namespace EMT.axioms
instance : EMT.axioms.HasM where p := 0; q := 1;
instance : EMT.axioms.HasT where p := 0;
end EMT.axioms
protected abbrev EMT : Logic ℕ := Hilbert.WithRE EMT.axioms
instance : Entailment.EMT Modal.EMT where

protected abbrev EMK.axioms : Axiom ℕ := {Axioms.M (.atom 0) (.atom 1), Axioms.K (.atom 0) (.atom 1)}
namespace EMK.axioms
instance : EMK.axioms.HasM where p := 0; q := 1;
instance : EMK.axioms.HasK where p := 0; q := 1;
end EMK.axioms
protected abbrev EMK : Logic ℕ := Hilbert.WithRE EMK.axioms
instance : Entailment.EMK Modal.EMK where

protected abbrev EMCK.axioms : Axiom ℕ := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.K (.atom 0) (.atom 1)
}
namespace EMCK.axioms
instance : EMCK.axioms.HasM where p := 0; q := 1;
instance : EMCK.axioms.HasC where p := 0; q := 1;
instance : EMCK.axioms.HasK where p := 0; q := 1;
end EMCK.axioms
protected abbrev EMCK : Logic ℕ := Hilbert.WithRE EMCK.axioms

instance : Modal.EMK ≊ Modal.EMCK := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;

protected abbrev EMT4.axioms : Axiom ℕ := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.T (.atom 0),
  Axioms.Four (.atom 0)
}
namespace EMT4.axioms
instance : EMT4.axioms.HasM where p := 0; q := 1;
instance : EMT4.axioms.HasT where p := 0;
instance : EMT4.axioms.HasFour where p := 0;
end EMT4.axioms
protected abbrev EMT4 : Logic ℕ := Hilbert.WithRE EMT4.axioms
instance : Entailment.EMT4 Modal.EMT4 where


protected abbrev EMNT4.axioms : Axiom ℕ := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.T (.atom 0),
  Axioms.Four (.atom 0)
}
namespace EMNT4.axioms
instance : EMNT4.axioms.HasM where p := 0; q := 1;
instance : EMNT4.axioms.HasN where
instance : EMNT4.axioms.HasT where p := 0;
instance : EMNT4.axioms.HasFour where p := 0;
end EMNT4.axioms
protected abbrev EMNT4 : Logic ℕ := Hilbert.WithRE EMNT4.axioms
instance : Entailment.EM Modal.EMNT4 where
instance : Entailment.EN Modal.EMNT4 where
instance : Entailment.ET Modal.EMNT4 where
instance : Entailment.E4 Modal.EMNT4 where


protected abbrev EMC4.axioms : Axiom ℕ := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.Four (.atom 0)
}
instance : EMC4.axioms.HasM where p := 0; q := 1
instance : EMC4.axioms.HasC where p := 0; q := 1;
instance : EMC4.axioms.HasFour where p := 0;
protected abbrev EMC4 : Logic ℕ := Hilbert.WithRE EMC4.axioms
instance : Entailment.EMC4 Modal.EMC4 where


protected abbrev EMCN4.axioms : Axiom ℕ := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.Four (.atom 0)
}
instance : EMCN4.axioms.HasM where p := 0; q := 1;
instance : EMCN4.axioms.HasC where p := 0; q := 1;
instance : EMCN4.axioms.HasN where
instance : EMCN4.axioms.HasFour where p := 0;
protected abbrev EMCN4 : Logic ℕ := Hilbert.WithRE EMCN4.axioms
instance : Entailment.EMC Modal.EMCN4 where


protected abbrev EMCNT.axioms : Axiom ℕ := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.T (.atom 0)
}
namespace EMCNT.axioms
instance : EMCNT.axioms.HasM where p := 0; q := 1;
instance : EMCNT.axioms.HasC where p := 0; q := 1
instance : EMCNT.axioms.HasN where
instance : EMCNT.axioms.HasT where p := 0;
end EMCNT.axioms
protected abbrev EMCNT : Logic ℕ := Hilbert.WithRE EMCNT.axioms
instance : Entailment.EMC Modal.EMCNT where
instance : Entailment.EN Modal.EMCNT where


protected abbrev EMCNT4.axioms : Axiom ℕ := {
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.T (.atom 0),
  Axioms.Four (.atom 0)
}
namespace EMCNT4.axioms
instance : EMCNT4.axioms.HasM where p := 0; q := 1;
instance : EMCNT4.axioms.HasC where p := 0; q := 1
instance : EMCNT4.axioms.HasN where
instance : EMCNT4.axioms.HasT where p := 0;
instance : EMCNT4.axioms.HasFour where p := 0;
end EMCNT4.axioms
protected abbrev EMCNT4 : Logic ℕ := Hilbert.WithRE EMCNT4.axioms
instance : Entailment.EMC Modal.EMCNT4 where
instance : Entailment.EN Modal.EMCNT4 where

protected abbrev EB.axioms : Axiom ℕ := {Axioms.B (.atom 0)}
namespace EB.axioms
instance : EB.axioms.HasB where p := 0;
end EB.axioms
protected abbrev EB : Logic ℕ := Hilbert.WithRE EB.axioms
instance : Entailment.EB Modal.EB where


protected abbrev ETB.axioms : Axiom ℕ := {Axioms.B (.atom 0), Axioms.T (.atom 0)}
namespace ETB.axioms
instance : ETB.axioms.HasB where p := 0;
instance : ETB.axioms.HasT where p := 0;
end ETB.axioms
protected abbrev ETB : Logic ℕ := Hilbert.WithRE ETB.axioms
instance : Entailment.ETB Modal.ETB where
instance : Entailment.EN Modal.ETB where

protected abbrev ENTB.axioms : Axiom ℕ := {Axioms.N, Axioms.B (.atom 0), Axioms.T (.atom 0)}
namespace ENTB.axioms
instance : ENTB.axioms.HasN where
instance : ENTB.axioms.HasT where p := 0;
instance : ENTB.axioms.HasB where p := 0;
end ENTB.axioms
protected abbrev ENTB : Logic ℕ := Hilbert.WithRE ENTB.axioms
instance : Entailment.ETB Modal.ENTB where
instance : Entailment.EN Modal.ENTB where

instance : Modal.ETB ≊ Modal.ENTB := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;


protected abbrev E5.axioms : Axiom ℕ := {Axioms.Five (.atom 0)}
namespace E5.axioms
instance : E5.axioms.HasFive where p := 0;
end E5.axioms
protected abbrev E5 : Logic ℕ := Hilbert.WithRE E5.axioms
instance : Entailment.E5 Modal.E5 where


protected abbrev ET5.axioms : Axiom ℕ := {Axioms.T (.atom 0), Axioms.Five (.atom 0)}
namespace ET5.axioms
instance : ET5.axioms.HasFive where p := 0;
instance : ET5.axioms.HasT where p := 0;
end ET5.axioms
protected abbrev ET5 : Logic ℕ := Hilbert.WithRE ET5.axioms
instance : Entailment.ET5 Modal.ET5 where

end



end LO.Modal
