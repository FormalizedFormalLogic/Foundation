module

public import Foundation.Modal.Entailment.GL
public import Foundation.Modal.Entailment.Grz
public import Foundation.Modal.Entailment.K4Hen
public import Foundation.Modal.Entailment.K4Henkin
public import Foundation.Modal.Entailment.S5Grz
public import Foundation.Modal.Hilbert.Axiom
public import Foundation.Modal.Logic.Basic
public import Foundation.Modal.Logic.Basic
public import Foundation.Propositional.Entailment.Cl.Łukasiewicz

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

inductive Hilbert.Normal {α} (Ax : Axiom α) : Logic α
| axm {φ} (s : Substitution _) : φ ∈ Ax → Normal Ax (φ⟦s⟧)
| mdp {φ ψ}     : Normal Ax (φ 🡒 ψ) → Normal Ax φ → Normal Ax ψ
| nec {φ}       : Normal Ax φ → Normal Ax (□φ)
| implyK φ ψ    : Normal Ax $ Axioms.ImplyK φ ψ
| implyS φ ψ χ  : Normal Ax $ Axioms.ImplyS φ ψ χ
| ec φ ψ        : Normal Ax $ Axioms.ElimContra φ ψ

namespace Hilbert.Normal

variable {Ax Ax₁ Ax₂ : Axiom α}

@[grind <=]
lemma axm' {φ} (h : φ ∈ Ax) : Normal Ax ⊢ φ := by
  apply Logic.iff_provable.mpr;
  simpa using axm (s := .id) h;

@[grind <=] lemma axm! {φ} (s : Substitution _) (h : φ ∈ Ax) : Normal Ax ⊢ φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply axm s h;

@[grind <=] lemma axm'! {φ} (h : φ ∈ Ax) : Normal Ax ⊢ φ := by simpa using axm! .id h;

instance : Entailment.Łukasiewicz (Hilbert.Normal Ax) where
  implyK {_ _} := by constructor; apply Hilbert.Normal.implyK;
  implyS {_ _ _} := by constructor; apply Hilbert.Normal.implyS;
  elimContra {_ _} := by constructor; apply Hilbert.Normal.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.Normal.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.Necessitation (Hilbert.Normal Ax) where
  nec h := by constructor; apply Hilbert.Normal.nec; exact h.1;

instance : Logic.Substitution (Hilbert.Normal Ax) where
  subst {φ} s h := by
    rw [Logic.iff_provable] at h ⊢;
    induction h with
    | @axm _ s' ih => simpa using axm (s := s' ∘ s) ih;
    | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
    | nec hφ ihφ => apply nec ihφ;
    | implyK φ ψ => apply implyK;
    | implyS φ ψ χ => apply implyS;
    | ec φ ψ => apply ec;

protected lemma rec!
  {motive   : (φ : Formula α) → (Normal Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Normal Ax) ⊢ φ 🡒 ψ} → {hφ : (Normal Ax) ⊢ φ} → motive (φ 🡒 ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (Normal Ax) ⊢ φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (implyK   : ∀ {φ ψ}, motive (Axioms.ImplyK φ ψ) $ by simp)
  (implyS   : ∀ {φ ψ χ}, motive (Axioms.ImplyS φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : Normal Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | nec hφ ihφ => apply nec; exact ihφ (Logic.iff_provable.mpr hφ);
  | implyK φ ψ => apply implyK;
  | implyS φ ψ χ => apply implyS;
  | ec φ ψ => apply ec;

lemma weakerThan_of_provable_axioms (hs : Normal Ax₂ ⊢* Ax₁) : (Normal Ax₁) ⪯ (Normal Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Normal.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
  | nec ihφ => apply nec!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

@[grind <=]
lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Normal Ax₁) ⪯ (Normal Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Normal.axm'!;
  apply h;
  assumption;

open Axiom


section

variable [DecidableEq α]

instance [Ax.HasK] : Entailment.HasAxiomK (Hilbert.Normal Ax) where
  K φ ψ := by
    constructor;
    simpa [HasK.ne_pq] using Hilbert.Normal.axm
      (φ := Axioms.K (.atom (HasK.p Ax)) (.atom (HasK.q Ax)))
      (s := λ b => if (HasK.p Ax) = b then φ else if (HasK.q Ax) = b then ψ else (.atom b))
      (HasK.mem_K);
instance [Ax.HasK] : Logic.IsNormal (Hilbert.Normal Ax) where

instance [Ax.HasT] : Entailment.HasAxiomT (Hilbert.Normal Ax) where
  T φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.T (.atom (HasT.p Ax)))
      (s := λ b => if (HasT.p Ax) = b then φ else (.atom b))
      (HasT.mem_T);

instance [Ax.HasD] : Entailment.HasAxiomD (Hilbert.Normal Ax) where
  D φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.D (.atom (HasD.p Ax)))
      (s := λ b => if (HasD.p Ax) = b then φ else (.atom b))
      HasD.mem_D;

instance [Ax.HasP] : Entailment.HasAxiomP (Hilbert.Normal Ax) where
  P := by
    constructor;
    simpa using Hilbert.Normal.axm (s := .id) HasP.mem_P

instance [Ax.HasB] : Entailment.HasAxiomB (Hilbert.Normal Ax) where
  B φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.B (.atom (HasB.p Ax)))
      (s := λ b => if (HasB.p Ax) = b then φ else (.atom b))
      (HasB.mem_B);

instance [Ax.HasFour] : Entailment.HasAxiomFour (Hilbert.Normal Ax) where
  Four φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Four (.atom (HasFour.p Ax)))
      (s := λ b => if (HasFour.p Ax) = b then φ else (.atom b))
      (HasFour.mem_Four);

instance [Ax.HasFourN n] : Entailment.HasAxiomFourN n (Hilbert.Normal Ax) where
  FourN φ := by
    constructor;
    simpa [Axioms.FourN] using Hilbert.Normal.axm
      (φ := Axioms.FourN n (.atom (HasFourN.p n Ax)))
      (s := λ b => if (HasFourN.p n Ax) = b then φ else (.atom b))
      (HasFourN.mem_FourN);

instance [Ax.HasFive] : Entailment.HasAxiomFive (Hilbert.Normal Ax) where
  Five φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Five (.atom (HasFive.p Ax)))
      (s := λ b => if (HasFive.p Ax) = b then φ else (.atom b))
      (HasFive.mem_Five);

instance [Ax.HasL] : Entailment.HasAxiomL (Hilbert.Normal Ax) where
  L φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.L (.atom (HasL.p Ax)))
      (s := λ b => if (HasL.p Ax) = b then φ else (.atom b))
      (HasL.mem_L);

instance [Ax.HasZ] : Entailment.HasAxiomZ (Hilbert.Normal Ax) where
  Z φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Z (.atom (HasZ.p Ax)))
      (s := λ b => if (HasZ.p Ax) = b then φ else (.atom b))
      (HasZ.mem_Z);

instance [Ax.HasHen] : Entailment.HasAxiomHen (Hilbert.Normal Ax) where
  Hen φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Hen (.atom (HasHen.p Ax)))
      (s := λ b => if (HasHen.p Ax) = b then φ else (.atom b))
      (HasHen.mem_Hen);

instance [Ax.HasPoint2] : Entailment.HasAxiomPoint2 (Hilbert.Normal Ax) where
  Point2 φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Point2 (.atom (HasPoint2.p Ax)))
      (s := λ b => if (HasPoint2.p Ax) = b then φ else (.atom b))
      (HasPoint2.mem_Point2);

instance [Ax.HasWeakPoint2] : Entailment.HasAxiomWeakPoint2 (Hilbert.Normal Ax) where
  WeakPoint2 φ ψ := by
    constructor;
    simpa [HasWeakPoint2.ne_pq] using Hilbert.Normal.axm
      (φ := Axioms.WeakPoint2 (.atom (HasWeakPoint2.p Ax)) (.atom (HasWeakPoint2.q Ax)))
      (s := λ b => if (HasWeakPoint2.p Ax) = b then φ else if (HasWeakPoint2.q Ax) = b then ψ else (.atom b))
      (HasWeakPoint2.mem_WeakPoint2);

instance [Ax.HasPoint3] : Entailment.HasAxiomPoint3 (Hilbert.Normal Ax) where
  Point3 φ ψ := by
    constructor;
    simpa [HasPoint3.ne_pq] using Hilbert.Normal.axm
      (φ := Axioms.Point3 (.atom (HasPoint3.p Ax)) (.atom (HasPoint3.q Ax)))
      (s := λ b => if (HasPoint3.p Ax) = b then φ else if (HasPoint3.q Ax) = b then ψ else (.atom b))
      (HasPoint3.mem_Point3);

instance [Ax.HasWeakPoint3] : Entailment.HasAxiomWeakPoint3 (Hilbert.Normal Ax) where
  WeakPoint3 φ ψ := by
    constructor;
    simpa [HasWeakPoint3.ne_pq] using Hilbert.Normal.axm
      (φ := Axioms.WeakPoint3 (.atom (HasWeakPoint3.p Ax)) (.atom (HasWeakPoint3.q Ax)))
      (s := λ b => if (HasWeakPoint3.p Ax) = b then φ else if (HasWeakPoint3.q Ax) = b then ψ else (.atom b))
      (HasWeakPoint3.mem_WeakPoint3);

instance [Ax.HasPoint4] : Entailment.HasAxiomPoint4 (Hilbert.Normal Ax) where
  Point4 φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Point4 (.atom (HasPoint4.p Ax)))
      (s := λ b => if (HasPoint4.p Ax) = b then φ else (.atom b))
      (HasPoint4.mem_Point4);

instance [Ax.HasGrz] : Entailment.HasAxiomGrz (Hilbert.Normal Ax) where
  Grz φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Grz (.atom (HasGrz.p Ax)))
      (s := λ b => if (HasGrz.p Ax) = b then φ else (.atom b))
      (HasGrz.mem_Grz);

instance [Ax.HasDum] : Entailment.HasAxiomDum (Hilbert.Normal Ax) where
  Dum φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Dum (.atom (HasDum.p Ax)))
      (s := λ b => if (HasDum.p Ax) = b then φ  else (.atom b))
      (HasDum.mem_Dum);

instance [Ax.HasTc] : Entailment.HasAxiomTc (Hilbert.Normal Ax) where
  Tc φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Tc (.atom (HasTc.p Ax)))
      (s := λ b => if (HasTc.p Ax) = b then φ else (.atom b))
      (HasTc.mem_Tc);

instance [Ax.HasVer] : Entailment.HasAxiomVer (Hilbert.Normal Ax) where
  Ver φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Ver (.atom (HasVer.p Ax)))
      (s := λ b => if (HasVer.p Ax) = b then φ else (.atom b))
      (HasVer.mem_Ver);

instance [Ax.HasMcK] : Entailment.HasAxiomMcK (Hilbert.Normal Ax) where
  McK φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.McK (.atom (HasMcK.p Ax)))
      (s := λ b => if (HasMcK.p Ax) = b then φ else (.atom b))
      (HasMcK.mem_McK);

instance [Ax.HasMk] : Entailment.HasAxiomMk (Hilbert.Normal Ax) where
  Mk φ ψ := by
    constructor;
    simpa [HasMk.ne_pq] using Hilbert.Normal.axm
      (φ := Axioms.Mk (.atom (HasMk.p Ax)) (.atom (HasMk.q Ax)))
      (s := λ b => if (HasMk.p Ax) = b then φ else if (HasMk.q Ax) = b then ψ else (.atom b))
      (HasMk.mem_Mk);

instance [Ax.HasH1] : Entailment.HasAxiomH (Hilbert.Normal Ax) where
  H1 φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.H (.atom (HasH1.p Ax)))
      (s := λ b => if (HasH1.p Ax) = b then φ else (.atom b))
      (HasH1.mem_H1);

instance [Ax.HasGeach g] : Entailment.HasAxiomGeach g (Hilbert.Normal Ax) where
  Geach φ := by
    constructor;
    simpa using Hilbert.Normal.axm
      (φ := Axioms.Geach g (.atom (HasGeach.p g Ax)))
      (s := λ b => if (HasGeach.p g Ax) = b then φ else (.atom b))
      (HasGeach.mem_Geach);

end

end Hilbert.Normal


section

open Hilbert.Normal

protected abbrev K.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1)}
namespace K.axioms
instance : K.axioms.HasK where p := 0; q := 1;
end K.axioms
protected abbrev K := Hilbert.Normal K.axioms
instance : Entailment.K Modal.K where

instance {L : Logic ℕ} [L.IsNormal] : Modal.K ⪯ L := by
  apply Logic.weakerThan_of_provable;
  intro φ hφ;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h => rcases h with rfl; simp;
  | nec hφ => apply nec! hφ;
  | mdp hφψ hφ => exact mdp! hφψ hφ
  | implyK | implyS | ec => simp;

protected abbrev KT.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0)}
namespace KT.axioms
instance : KT.axioms.HasK where p := 0; q := 1;
instance : KT.axioms.HasT where p := 0;
end KT.axioms
protected abbrev KT := Hilbert.Normal KT.axioms
instance : Entailment.KT Modal.KT where

protected abbrev KD.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0)}
namespace KD.axioms
instance : KD.axioms.HasK where p := 0; q := 1;
instance : KD.axioms.HasD where p := 0;
end KD.axioms
protected abbrev KD := Hilbert.Normal KD.axioms
instance : Entailment.KD Modal.KD where

protected abbrev KP.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.P}
namespace KP.axioms
instance : KP.axioms.HasK where p := 0; q := 1;
instance : KP.axioms.HasP where
end KP.axioms
protected abbrev KP := Hilbert.Normal KP.axioms
instance : Entailment.KP Modal.KP where

instance : Modal.KP ≊ Modal.KD := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_provable_axioms; rintro φ (rfl | rfl) <;> simp;
  . apply weakerThan_of_provable_axioms; rintro φ (rfl | rfl) <;> simp;


protected abbrev KB.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0)}
namespace KB.axioms
instance : KB.axioms.HasK where p := 0; q := 1;
instance : KB.axioms.HasB where p := 0;
end KB.axioms
protected abbrev KB := Hilbert.Normal KB.axioms
instance : Entailment.KB Modal.KB where

protected abbrev KDB.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.B (.atom 0)}
namespace KDB.axioms
instance : KDB.axioms.HasK where p := 0; q := 1
instance : KDB.axioms.HasD where p := 0
instance : KDB.axioms.HasB where p := 0
end KDB.axioms
protected abbrev KDB := Hilbert.Normal KDB.axioms
instance : Entailment.KDB Modal.KDB where

protected abbrev KTB.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.B (.atom 0)}
namespace KTB.axioms
instance : KTB.axioms.HasK where p := 0; q := 1
instance : KTB.axioms.HasT where p := 0
instance : KTB.axioms.HasB where p := 0
end KTB.axioms
protected abbrev KTB := Hilbert.Normal KTB.axioms
instance : Entailment.KTB Modal.KTB where

protected abbrev KMcK.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.McK (.atom 0)}
namespace KMcK.axioms
instance : KMcK.axioms.HasK where p := 0; q := 1
instance : KMcK.axioms.HasMcK where p := 0
end KMcK.axioms
protected abbrev KMcK := Hilbert.Normal KMcK.axioms
instance : Entailment.KMcK Modal.KMcK where

protected abbrev K4.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}
namespace K4.axioms
instance : K4.axioms.HasK where p := 0; q := 1
instance : K4.axioms.HasFour where p := 0;
end K4.axioms
protected abbrev K4 := Hilbert.Normal K4.axioms
instance : Entailment.K4 Modal.K4 where

protected abbrev K4n.axioms (n : ℕ) : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.FourN n (.atom 0)}
namespace K4n.axioms
instance {n : ℕ} : K4n.axioms n |>.HasK where p := 0; q := 1
instance {n : ℕ} : K4n.axioms n |>.HasFourN n where p := 0;
end K4n.axioms
protected abbrev K4n (n : ℕ) := Hilbert.Normal (K4n.axioms n)
instance {n : ℕ} : Entailment.K4n n (Modal.K4n n) where

protected abbrev K4McK.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.McK (.atom 0)}
namespace K4McK.axioms
instance : K4McK.axioms.HasK where p := 0; q := 1
instance : K4McK.axioms.HasFour where p := 0;
instance : K4McK.axioms.HasMcK where p := 0;
end K4McK.axioms
protected abbrev K4McK := Hilbert.Normal K4McK.axioms
instance : Entailment.K4McK Modal.K4McK where

noncomputable instance [Entailment.K (Hilbert.Normal Ax)] [Modal.K4McK ⪯ Hilbert.Normal Ax] : Entailment.K4McK (Hilbert.Normal Ax) where
  Four _ := Entailment.WeakerThan.pbl (𝓢 := Modal.K4McK) (by simp) |>.some
  McK _ := Entailment.WeakerThan.pbl (𝓢 := Modal.K4McK) (by simp) |>.some


protected abbrev K4Point2.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}
namespace K4Point2.axioms
instance : K4Point2.axioms.HasK where p := 0; q := 1
instance : K4Point2.axioms.HasFour where p := 0;
instance : K4Point2.axioms.HasWeakPoint2 where p := 0; q := 1;
end K4Point2.axioms
protected abbrev K4Point2 := Hilbert.Normal K4Point2.axioms
instance : Entailment.K4Point2 Modal.K4Point2 where

protected abbrev K4Point3.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}
namespace K4Point3.axioms
instance : K4Point3.axioms.HasK where p := 0; q := 1
instance : K4Point3.axioms.HasFour where p := 0;
instance : K4Point3.axioms.HasWeakPoint3 where p := 0; q := 1;
end K4Point3.axioms
protected abbrev K4Point3 := Hilbert.Normal K4Point3.axioms
instance : Entailment.K4Point3 Modal.K4Point3 where


protected abbrev KT4B.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.B (.atom 0)}
namespace KT4B.axioms
instance : KT4B.axioms.HasK where p := 0; q := 1;
instance : KT4B.axioms.HasT where p := 0
instance : KT4B.axioms.HasFour where p := 0
instance : KT4B.axioms.HasB where p := 0
end KT4B.axioms
protected abbrev KT4B := Hilbert.Normal KT4B.axioms
instance : Entailment.KT4B (Modal.KT4B) where


protected abbrev K45.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}
namespace K45.axioms
instance : K45.axioms.HasK where p := 0; q := 1;
instance : K45.axioms.HasFour where p := 0
instance : K45.axioms.HasFive where p := 0
end K45.axioms
protected abbrev K45 := Hilbert.Normal K45.axioms
instance : Entailment.K45 (Modal.K45) where


protected abbrev KD4.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0)}
namespace KD4.axioms
instance : KD4.axioms.HasK where p := 0; q := 1;
instance : KD4.axioms.HasD where p := 0
instance : KD4.axioms.HasFour where p := 0
end KD4.axioms
protected abbrev KD4 := Hilbert.Normal KD4.axioms
instance : Entailment.KD4 (Modal.KD4) where


protected abbrev KD5.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Five (.atom 0)}
namespace KD5.axioms
instance : KD5.axioms.HasK where p := 0; q := 1;
instance : KD5.axioms.HasD where p := 0
instance : KD5.axioms.HasFive where p := 0
end KD5.axioms
protected abbrev KD5 := Hilbert.Normal KD5.axioms
instance : Entailment.KD5 (Modal.KD5) where


protected abbrev KD45.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}
namespace KD45.axioms
instance : KD45.axioms.HasK where p := 0; q := 1;
instance : KD45.axioms.HasD where p := 0
instance : KD45.axioms.HasFour where p := 0
instance : KD45.axioms.HasFive where p := 0
end KD45.axioms
protected abbrev KD45 := Hilbert.Normal KD45.axioms
instance : Entailment.KD45 (Modal.KD45) where


protected abbrev KB4.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Four (.atom 0)}
namespace KB4.axioms
instance : KB4.axioms.HasK where p := 0; q := 1;
instance : KB4.axioms.HasB where p := 0
instance : KB4.axioms.HasFour where p := 0
end KB4.axioms
protected abbrev KB4 := Hilbert.Normal KB4.axioms
instance : Entailment.KB4 (Modal.KB4) where


protected abbrev KB5.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Five (.atom 0)}
namespace KB5.axioms
instance : KB5.axioms.HasK where p := 0; q := 1;
instance : KB5.axioms.HasB where p := 0
instance : KB5.axioms.HasFive where p := 0
end KB5.axioms
protected abbrev KB5 := Hilbert.Normal KB5.axioms
instance : Entailment.KB5 (Modal.KB5) where


protected abbrev S4.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}
namespace S4.axioms
instance : S4.axioms.HasK where p := 0; q := 1;
instance : S4.axioms.HasT where p := 0
instance : S4.axioms.HasFour where p := 0
end S4.axioms
protected abbrev S4 := Hilbert.Normal S4.axioms
instance : Entailment.S4 (Modal.S4) where
instance : Modal.K4 ⪯ Modal.S4 := weakerThan_of_subset_axioms $ by grind;


protected abbrev S4McK.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0)}
namespace S4McK.axioms
instance : S4McK.axioms.HasK where p := 0; q := 1;
instance : S4McK.axioms.HasT where p := 0
instance : S4McK.axioms.HasFour where p := 0
instance : S4McK.axioms.HasMcK where p := 0
end S4McK.axioms
protected abbrev S4McK := Hilbert.Normal S4McK.axioms
instance : Entailment.S4McK (Modal.S4McK) where
instance : Modal.K4McK ⪯ Modal.S4McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev S4Point2McK.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point2 (.atom 0)}
namespace S4Point2McK.axioms
instance : S4Point2McK.axioms.HasK where p := 0; q := 1;
instance : S4Point2McK.axioms.HasT where p := 0
instance : S4Point2McK.axioms.HasFour where p := 0
instance : S4Point2McK.axioms.HasMcK where p := 0
instance : S4Point2McK.axioms.HasPoint2 where p := 0
end S4Point2McK.axioms
protected abbrev S4Point2McK := Hilbert.Normal S4Point2McK.axioms
instance : Entailment.S4Point2McK (Modal.S4Point2McK) where
instance : Modal.K4McK ⪯ Modal.S4Point2McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev S4Point3McK.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}
namespace S4Point3McK.axioms
instance : S4Point3McK.axioms.HasK where p := 0; q := 1;
instance : S4Point3McK.axioms.HasT where p := 0
instance : S4Point3McK.axioms.HasFour where p := 0
instance : S4Point3McK.axioms.HasMcK where p := 0
instance : S4Point3McK.axioms.HasPoint3 where p := 0; q := 1;
end S4Point3McK.axioms
protected abbrev S4Point3McK := Hilbert.Normal S4Point3McK.axioms
instance : Entailment.S4Point3McK (Modal.S4Point3McK) where
instance : Modal.K4McK ⪯ Modal.S4Point3McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev S4Point4McK.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point4 (.atom 0)}
namespace S4Point4McK.axioms
instance : S4Point4McK.axioms.HasK where p := 0; q := 1;
instance : S4Point4McK.axioms.HasT where p := 0
instance : S4Point4McK.axioms.HasFour where p := 0
instance : S4Point4McK.axioms.HasMcK where p := 0
instance : S4Point4McK.axioms.HasPoint4 where p := 0
end S4Point4McK.axioms
protected abbrev S4Point4McK := Hilbert.Normal S4Point4McK.axioms
instance : Entailment.S4Point4McK (Modal.S4Point4McK) where
instance : Modal.K4McK ⪯ Modal.S4Point4McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev S4Point2.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point2 (.atom 0)}
namespace S4Point2.axioms
instance : S4Point2.axioms.HasK where p := 0; q := 1;
instance : S4Point2.axioms.HasT where p := 0
instance : S4Point2.axioms.HasFour where p := 0
instance : S4Point2.axioms.HasPoint2 where p := 0
end S4Point2.axioms
protected abbrev S4Point2 := Hilbert.Normal S4Point2.axioms
instance : Entailment.S4Point2 (Modal.S4Point2) where


protected abbrev S4Point3.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}
namespace S4Point3.axioms
instance : S4Point3.axioms.HasK where p := 0; q := 1;
instance : S4Point3.axioms.HasT where p := 0
instance : S4Point3.axioms.HasFour where p := 0
instance : S4Point3.axioms.HasPoint3 where p := 0; q := 1;
end S4Point3.axioms
protected abbrev S4Point3 := Hilbert.Normal S4Point3.axioms
instance : Entailment.S4Point3 (Modal.S4Point3) where


protected abbrev S4Point4.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point4 (.atom 0)}
namespace S4Point4.axioms
instance : S4Point4.axioms.HasK where p := 0; q := 1;
instance : S4Point4.axioms.HasT where p := 0
instance : S4Point4.axioms.HasFour where p := 0
instance : S4Point4.axioms.HasPoint4 where p := 0
end S4Point4.axioms
protected abbrev S4Point4 := Hilbert.Normal S4Point4.axioms
instance : Entailment.S4Point4 (Modal.S4Point4) where


protected abbrev K5.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Five (.atom 0)}
namespace K5.axioms
instance : K5.axioms.HasK where p := 0; q := 1;
instance : K5.axioms.HasFive where p := 0
end K5.axioms
protected abbrev K5 := Hilbert.Normal K5.axioms
instance : Entailment.K5 (Modal.K5) where


protected abbrev S5.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}
namespace S5.axioms
instance : S5.axioms.HasK where p := 0; q := 1;
instance : S5.axioms.HasT where p := 0
instance : S5.axioms.HasFive where p := 0
end S5.axioms
protected abbrev S5 := Hilbert.Normal S5.axioms
instance : Entailment.S5 (Modal.S5) where


protected abbrev GL.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}
namespace GL.axioms
instance : GL.axioms.HasK where p := 0; q := 1;
instance : GL.axioms.HasL where p := 0;
end GL.axioms
protected abbrev GL := Hilbert.Normal GL.axioms
instance : Entailment.GL (Modal.GL) where
instance : Entailment.GL (Modal.GL) where

protected abbrev GLPoint2.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}
namespace GLPoint2.axioms
instance : GLPoint2.axioms.HasK where p := 0; q := 1;
instance : GLPoint2.axioms.HasL where p := 0
instance : GLPoint2.axioms.HasWeakPoint2 where p := 0; q := 1;
end GLPoint2.axioms
protected abbrev GLPoint2 := Hilbert.Normal GLPoint2.axioms
instance : Entailment.GLPoint2 (Modal.GLPoint2) where
instance : Entailment.GLPoint2 (Modal.GLPoint2) where
instance : Modal.GL ⪯ Modal.GLPoint2 := weakerThan_of_subset_axioms $ by grind


protected abbrev GLPoint3.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}
namespace GLPoint3.axioms
instance : GLPoint3.axioms.HasK where p := 0; q := 1;
instance : GLPoint3.axioms.HasL where p := 0
instance : GLPoint3.axioms.HasWeakPoint3 where p := 0; q := 1;
end GLPoint3.axioms
protected abbrev GLPoint3 := Hilbert.Normal GLPoint3.axioms
instance : Entailment.GLPoint3 (Modal.GLPoint3) where


protected abbrev K4Z.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0)}
namespace K4Z.axioms
instance : K4Z.axioms.HasK where p := 0; q := 1;
instance : K4Z.axioms.HasFour where p := 0
instance : K4Z.axioms.HasZ where p := 0
end K4Z.axioms
protected abbrev K4Z := Hilbert.Normal K4Z.axioms
instance : Entailment.K4Z (Modal.K4Z) where

instance : Modal.K4 ⪯ Modal.K4Z := weakerThan_of_subset_axioms $ by grind;
instance : Modal.K4 ⪯ Modal.K4Z := inferInstance

instance : Modal.K4Z ⪯ Modal.GL := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.K4Z ⪯ Modal.GL := inferInstance


protected abbrev K4Point2Z.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}
namespace K4Point2Z.axioms
instance : K4Point2Z.axioms.HasK where p := 0; q := 1;
instance : K4Point2Z.axioms.HasFour where p := 0
instance : K4Point2Z.axioms.HasZ where p := 0
instance : K4Point2Z.axioms.HasWeakPoint2 where p := 0; q := 1;
end K4Point2Z.axioms
protected abbrev K4Point2Z := Hilbert.Normal K4Point2Z.axioms
instance : Entailment.K4Point2Z (Modal.K4Point2Z) where

instance : Modal.K4Point2 ⪯ Modal.K4Point2Z := weakerThan_of_subset_axioms $ by grind;
instance : Modal.K4Point2 ⪯ Modal.K4Point2Z := inferInstance

instance : Modal.K4Z ⪯ Modal.K4Point2Z := weakerThan_of_subset_axioms $ by grind;
instance : Modal.K4Point2 ⪯ Modal.K4Point2Z := inferInstance

instance : Modal.K4Point2Z ⪯ Modal.GLPoint2 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.K4Point2Z ⪯ Modal.GLPoint2 := inferInstance


protected abbrev K4Point3Z.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}
namespace K4Point3Z.axioms
instance : K4Point3Z.axioms.HasK where p := 0; q := 1;
instance : K4Point3Z.axioms.HasFour where p := 0
instance : K4Point3Z.axioms.HasZ where p := 0
instance : K4Point3Z.axioms.HasWeakPoint3 where p := 0; q := 1;
end K4Point3Z.axioms
protected abbrev K4Point3Z := Hilbert.Normal K4Point3Z.axioms
instance : Entailment.K4Point3Z (Modal.K4Point3Z) where

instance : Modal.K4Point3 ⪯ Modal.K4Point3Z := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.K4Point3 ⪯ Modal.K4Point3Z := inferInstance

instance : Modal.K4Z ⪯ Modal.K4Point3Z := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.K4Z ⪯ Modal.K4Point3Z := inferInstance

instance : Modal.K4Point3Z ⪯ Modal.GLPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.K4Point3Z ⪯ Modal.GLPoint3 := inferInstance


protected abbrev KHen.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Hen (.atom 0)}
namespace KHen.axioms
instance : KHen.axioms.HasK where p := 0; q := 1;
instance : KHen.axioms.HasHen where p := 0;
end KHen.axioms
protected abbrev KHen := Hilbert.Normal KHen.axioms


protected abbrev K4Hen.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Hen (.atom 0)}
namespace K4Hen.axioms
instance : K4Hen.axioms.HasK where p := 0; q := 1;
instance : K4Hen.axioms.HasFour where p := 0
instance : K4Hen.axioms.HasHen where p := 0
end K4Hen.axioms
protected abbrev K4Hen := Hilbert.Normal K4Hen.axioms
instance : Entailment.K4Hen (Modal.K4Hen) where


protected abbrev Grz.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}
namespace Grz.axioms
instance : Grz.axioms.HasK where p := 0; q := 1;
instance : Grz.axioms.HasGrz where p := 0
end Grz.axioms
protected abbrev Grz := Hilbert.Normal Grz.axioms
instance : Entailment.Grz (Modal.Grz) where
instance : Modal.KT ⪯ Modal.Grz := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl) <;> simp;


protected abbrev GrzPoint2.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point2 (.atom 0)}
namespace GrzPoint2.axioms
instance : GrzPoint2.axioms.HasK where p := 0; q := 1;
instance : GrzPoint2.axioms.HasGrz where p := 0
instance : GrzPoint2.axioms.HasPoint2 where p := 0
end GrzPoint2.axioms
protected abbrev GrzPoint2 := Hilbert.Normal GrzPoint2.axioms
instance : Entailment.GrzPoint2 (Modal.GrzPoint2) where


protected abbrev GrzPoint3.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}
namespace GrzPoint3.axioms
instance : GrzPoint3.axioms.HasK where p := 0; q := 1;
instance : GrzPoint3.axioms.HasGrz where p := 0
instance : GrzPoint3.axioms.HasPoint3 where p := 0; q := 1;
end GrzPoint3.axioms
protected abbrev GrzPoint3 := Hilbert.Normal GrzPoint3.axioms
instance : Entailment.GrzPoint3 (Modal.GrzPoint3) where


protected abbrev Dum.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0)}
namespace Dum.axioms
instance : Dum.axioms.HasK where p := 0; q := 1;
instance : Dum.axioms.HasT where p := 0
instance : Dum.axioms.HasFour where p := 0
instance : Dum.axioms.HasDum where p := 0
end Dum.axioms
protected abbrev Dum := Hilbert.Normal Dum.axioms
instance : Entailment.Dum (Modal.Dum) where

instance : Modal.S4 ⪯ Modal.Dum := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.S4 ⪯ Modal.Dum := inferInstance

instance : Modal.Dum ⪯ Modal.Grz := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.Dum ⪯ Modal.Grz := inferInstance


protected abbrev DumPoint2.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0), Axioms.Point2 (.atom 0)}
namespace DumPoint2.axioms
instance : DumPoint2.axioms.HasK where p := 0; q := 1;
instance : DumPoint2.axioms.HasT where p := 0
instance : DumPoint2.axioms.HasFour where p := 0
instance : DumPoint2.axioms.HasDum where p := 0
instance : DumPoint2.axioms.HasPoint2 where p := 0
end DumPoint2.axioms
protected abbrev DumPoint2 := Hilbert.Normal DumPoint2.axioms
instance : Entailment.DumPoint2 (Modal.DumPoint2) where

instance : Modal.Dum ⪯ Modal.DumPoint2 := weakerThan_of_subset_axioms $ by grind
instance : Modal.Dum ⪯ Modal.DumPoint2 := inferInstance

instance : Modal.S4Point2 ⪯ Modal.DumPoint2 := weakerThan_of_subset_axioms $ by grind
instance : Modal.S4Point2 ⪯ Modal.DumPoint2 := inferInstance

instance : Modal.DumPoint2 ⪯ Modal.GrzPoint2 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.DumPoint2 ⪯ Modal.GrzPoint2 := inferInstance


protected abbrev DumPoint3.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}
namespace DumPoint3.axioms
instance : DumPoint3.axioms.HasK where p := 0; q := 1;
instance : DumPoint3.axioms.HasT where p := 0
instance : DumPoint3.axioms.HasFour where p := 0
instance : DumPoint3.axioms.HasDum where p := 0
instance : DumPoint3.axioms.HasPoint3 where p := 0; q := 1;
end DumPoint3.axioms
protected abbrev DumPoint3 := Hilbert.Normal DumPoint3.axioms
instance : Entailment.DumPoint3 (Modal.DumPoint3) where

instance : Modal.Dum ⪯ Modal.DumPoint3 := weakerThan_of_subset_axioms $ by grind
instance : Modal.Dum ⪯ Modal.DumPoint3 := inferInstance

instance : Modal.S4Point3 ⪯ Modal.DumPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.S4Point3 ⪯ Modal.DumPoint3 := inferInstance

instance : Modal.DumPoint3 ⪯ Modal.GrzPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.DumPoint3 ⪯ Modal.GrzPoint3 := inferInstance


protected abbrev KTc.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Tc (.atom 0)}
namespace KTc.axioms
instance : KTc.axioms.HasK where p := 0; q := 1;
instance : KTc.axioms.HasTc where p := 0
end KTc.axioms
protected abbrev KTc := Hilbert.Normal KTc.axioms
instance : Entailment.KTc (Modal.KTc) where


protected abbrev KD4Point3Z.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1), Axioms.Z (.atom 0)}
namespace KD4Point3Z.axioms
instance : KD4Point3Z.axioms.HasK where p := 0; q := 1;
instance : KD4Point3Z.axioms.HasD where p := 0
instance : KD4Point3Z.axioms.HasFour where p := 0
instance : KD4Point3Z.axioms.HasWeakPoint3 where p := 0; q := 1;
instance : KD4Point3Z.axioms.HasZ where p := 0
end KD4Point3Z.axioms
protected abbrev KD4Point3Z := Hilbert.Normal KD4Point3Z.axioms
instance : Entailment.KD4Point3Z (Modal.KD4Point3Z) where


protected abbrev KTMk.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Mk (.atom 0) (.atom 1)}
namespace KTMk.axioms
instance : KTMk.axioms.HasK where p := 0; q := 1;
instance : KTMk.axioms.HasT where p := 0
instance : KTMk.axioms.HasMk where p := 0; q := 1
end KTMk.axioms
protected abbrev KTMk := Hilbert.Normal KTMk.axioms
instance : Entailment.KTMk (Modal.KTMk) where


protected abbrev S4H.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.H (.atom 0)}
namespace S4H.axioms
instance : S4H.axioms.HasK where p := 0; q := 1;
instance : S4H.axioms.HasT where p := 0
instance : S4H.axioms.HasFour where p := 0
instance : S4H.axioms.HasH1 where p := 0
end S4H.axioms
/--
  - `S4H` in Segerberg 1971.
  - `K1.2` in Sobocinski 1964, "Family $K$ of the non-Lewis modal systems"
-/
protected abbrev S4H := Hilbert.Normal S4H.axioms
instance : Entailment.S4H (Modal.S4H) where


protected abbrev Ver.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}
namespace Ver.axioms
instance : Ver.axioms.HasK where p := 0; q := 1;
instance : Ver.axioms.HasVer where p := 0
end Ver.axioms
protected abbrev Ver := Hilbert.Normal Ver.axioms
instance : Entailment.Ver (Modal.Ver) where


protected abbrev Triv.axioms : Axiom ℕ := { Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}
namespace Triv.axioms
instance : Triv.axioms.HasK where p := 0; q := 1;
instance : Triv.axioms.HasT where p := 0
instance : Triv.axioms.HasTc where p := 0
end Triv.axioms
protected abbrev Triv := Hilbert.Normal Triv.axioms
instance : Entailment.Triv (Modal.Triv) where
instance : Modal.K4 ⪯ Modal.Triv := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl) <;> simp;


protected abbrev S5Grz.axioms : Axiom ℕ := {Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0), Axioms.Grz (.atom 0)}
protected abbrev S5Grz := Hilbert.Normal S5Grz.axioms
namespace S5Grz.axioms
instance : S5Grz.axioms.HasK where p := 0; q := 1;
instance : S5Grz.axioms.HasT where p := 0
instance : S5Grz.axioms.HasFive where p := 0
instance : S5Grz.axioms.HasGrz where p := 0
end S5Grz.axioms
instance : Entailment.S5Grz (Modal.S5Grz) where

instance : Modal.S5Grz ≊ Modal.Triv := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_provable_axioms; rintro φ (rfl | rfl | rfl | rfl) <;> simp;
  . apply weakerThan_of_provable_axioms; rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev N.axioms : Axiom ℕ := ∅
protected abbrev N := Hilbert.Normal N.axioms

protected abbrev NP.axioms : Axiom ℕ := {Axioms.P}
namespace NP.axioms
instance : NP.axioms.HasP where
end NP.axioms
protected abbrev NP := Hilbert.Normal NP.axioms
instance : Entailment.HasAxiomP (Modal.NP) := inferInstance

end

end LO.Modal
end
