import Foundation.Modal.Entailment.GL
import Foundation.Modal.Entailment.Grz
import Foundation.Modal.Entailment.S5Grz
import Foundation.Modal.Entailment.K4Hen
import Foundation.Modal.Logic.Basic


namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

namespace Hilbert

protected structure Normal (α) where
  axioms : Set (Formula α)

namespace Normal

variable {H H₁ H₂ : Hilbert.Normal α} {φ ψ : Formula α}

abbrev axiomInstances (H : Hilbert.Normal α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  . assumption;
  . use Substitution.id;
    simp;

inductive Deduction (H : Hilbert.Normal α) : (Formula α) → Type u
  | axm {φ} (s : Substitution _) : φ ∈ H.axioms → Deduction H (φ⟦s⟧)
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

instance : Entailment (Formula α) (Hilbert.Normal α) := ⟨Deduction⟩

def Deduction.axm' {H : Hilbert.Normal α} {φ} (h : φ ∈ H.axioms) : Deduction H φ := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply Deduction.axm _ h;

section

variable {H : Hilbert.Normal α}

instance : Entailment.Lukasiewicz H where
  mdp := .mdp
  imply₁ := .imply₁
  imply₂ := .imply₂
  elimContra := .ec
instance : Entailment.Necessitation H where
  nec := .nec

instance : Entailment.DeductiveExplosion (Hilbert.Normal α) where
  dexp := fun h _ ↦ of_O h

protected lemma rec!
  {motive   : (φ : Formula α) → (H ⊢! φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ H.axioms) → motive (φ⟦s⟧) ⟨.axm s h⟩)
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : H ⊢! φ ➝ ψ} → {hφ : H ⊢! φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : H ⊢! φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (imply₁   : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  rintro φ ⟨d⟩;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
  | nec hφψ ihφ => apply nec ihφ
  | imply₁ φ ψ => apply imply₁
  | imply₂ φ ψ χ => apply imply₂
  | ec φ ψ => apply ec;

lemma axm! {φ} (s) (h : φ ∈ H.axioms) : H ⊢! (φ⟦s⟧) := ⟨.axm s h⟩

lemma axm'! {φ} (h : φ ∈ H.axioms) : H ⊢! φ := by simpa using axm! Substitution.id h

lemma subst! {φ} (s) (h : H ⊢! φ) : H ⊢! (φ⟦s⟧) := by
  induction h using Normal.rec! with
  | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
  | @axm φ s' h => rw [(show φ⟦s'⟧⟦s⟧ = φ⟦s' ∘ s⟧ by simp)]; apply axm!; exact h;
  | @nec φ h => apply nec!; simpa;
  | _ => simp;

lemma weakerThan_of_provable_axioms (hs : H₂ ⊢!* H₁.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_iff.mpr;
  intro φ h;
  induction h using Normal.rec! with
  | @axm φ s h => apply subst!; apply @hs φ h;
  | @nec φ h => apply nec!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

lemma weakerThan_of_subset_axioms (hs : H₁.axioms ⊆ H₂.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_of_provable_axioms;
  intro φ h;
  apply axm'!;
  exact hs h;

end


section

abbrev logic (H : Hilbert.Normal α) : Logic α := Entailment.theory H

@[grind]
lemma iff_logic_provable_provable : H.logic ⊢! φ ↔ H ⊢! φ := by simp [Entailment.theory, Logic.iff_provable];

instance : Entailment.Lukasiewicz H.logic where
  mdp hφψ hφ := by
    replace hφψ := hφψ.1;
    replace hφ := hφ.1;
    simp_all only [theory, Set.mem_setOf_eq];
    constructor;
    exact hφψ ⨀ hφ;
  imply₁ _ _ := by constructor; simp [Entailment.theory];
  imply₂ _ _ _ := by constructor; simp [Entailment.theory];
  elimContra _ _ := by constructor; simp [Entailment.theory];

instance : Entailment.Necessitation H.logic where
  nec hφ := by
    replace hφ := hφ.1;
    simp only [theory, Set.mem_setOf_eq];
    constructor;
    exact nec! hφ;

@[grind]
lemma iff_weakerThan_hilbert_weakerThan_logic : H₁ ⪯ H₂ ↔ H₁.logic ⪯ H₂.logic := by
  constructor;
  . intro h;
    apply weakerThan_iff.mpr;
    simp only [theory, Logic.iff_provable, Set.mem_setOf_eq];
    apply WeakerThan.wk;
    assumption;
  . intro h;
    apply weakerThan_iff.mpr;
    intro φ;
    simpa [iff_logic_provable_provable] using h.pbl;

@[grind]
lemma iff_equiv_hilbert_equiv_logic : H₁ ≊ H₂ ↔ H₁.logic ≊ H₂.logic := by grind;

@[grind]
lemma iff_strictlyWeakerThan_hilbert_strictlyWeakerThan_logic : H₁ ⪱ H₂ ↔ H₁.logic ⪱ H₂.logic := by grind;

instance [H₁ ⪯ H₂] : H₁.logic ⪯ H₂.logic := iff_weakerThan_hilbert_weakerThan_logic.mp inferInstance
instance [H₁ ⪱ H₂] : H₁.logic ⪱ H₂.logic := iff_strictlyWeakerThan_hilbert_strictlyWeakerThan_logic.mp inferInstance
instance [H₁ ≊ H₂] : H₁.logic ≊ H₂.logic := iff_equiv_hilbert_equiv_logic.mp inferInstance
instance [H₁.logic ⪯ H₂.logic] : H₁ ⪯ H₂ := iff_weakerThan_hilbert_weakerThan_logic.mpr inferInstance
instance [H₁.logic ⪱ H₂.logic] : H₁ ⪱ H₂ := iff_strictlyWeakerThan_hilbert_strictlyWeakerThan_logic.mpr inferInstance
instance [H₁.logic ≊ H₂.logic] : H₁ ≊ H₂ := iff_equiv_hilbert_equiv_logic.mpr inferInstance

instance [Entailment.Consistent H] : Entailment.Consistent H.logic where
  not_inconsistent := by
    simp only [Inconsistent, iff_logic_provable_provable, not_forall]
    use ⊥;
    apply Entailment.Consistent.not_bot;
    infer_instance;

end


section

variable [DecidableEq α]

class HasK (H : Hilbert.Normal α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasK] : Entailment.HasAxiomK H where
  K φ ψ := by
    simpa [HasK.ne_pq] using Deduction.axm
      (φ := Axioms.K (.atom (HasK.p H)) (.atom (HasK.q H)))
      (s := λ b =>
        if (HasK.p H) = b then φ
        else if (HasK.q H) = b then ψ
        else (.atom b))
      HasK.mem_K;

instance [H.HasK] : H.logic.IsNormal where
  K φ ψ := by constructor; simp [Entailment.theory];
  subst s hφ := by
    replace hφ := hφ.1;
    constructor;
    simp_all only [theory, Set.mem_setOf_eq];
    apply subst! s hφ;


class HasT (H : Hilbert.Normal α) where
  p : α
  mem_T : Axioms.T (.atom p) ∈ H.axioms := by tauto;

instance [H.HasT] : Entailment.HasAxiomT H where
  T φ := by
    simpa using Deduction.axm
      (φ := Axioms.T (.atom (HasT.p H)))
      (s := λ b => if (HasT.p H) = b then φ else (.atom b))
      HasT.mem_T;

instance [H.HasT] : Entailment.HasAxiomT H.logic where
  T := by intros; constructor; simp [Entailment.theory];


class HasB (H : Hilbert.Normal α) where
  p : α
  mem_B : Axioms.B (.atom p) ∈ H.axioms := by tauto;

instance [H.HasB] : Entailment.HasAxiomB H where
  B φ := by
    simpa using Deduction.axm
      (φ := Axioms.B (.atom (HasB.p H)))
      (s := λ b => if (HasB.p H) = b then φ else (.atom b))
      HasB.mem_B;


class HasD (H : Hilbert.Normal α) where
  p : α
  mem_D : Axioms.D (.atom p) ∈ H.axioms := by tauto;

instance [H.HasD] : Entailment.HasAxiomD H where
  D φ := by
    simpa using Deduction.axm
      (φ := Axioms.D (.atom (HasD.p H)))
      (s := λ b => if (HasD.p H) = b then φ else (.atom b))
      HasD.mem_D;

instance [H.HasD] : Entailment.HasAxiomD H.logic where
  D := by intros; constructor; simp [Entailment.theory];


class HasP (H : Hilbert.Normal α) where
  mem_P : Axioms.P ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasP] : Entailment.HasAxiomP H where
  P := by
    simpa using Deduction.axm
      (φ := Axioms.P)
      (s := .id)
      HasP.mem_P;


class HasFour (H : Hilbert.Normal α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFour] : Entailment.HasAxiomFour H where
  Four φ := by
    simpa using Deduction.axm
      (φ := Axioms.Four (.atom (HasFour.p H)))
      (s := λ b => if (HasFour.p H) = b then φ else (.atom b))
      HasFour.mem_Four;
instance [H.HasFour] : Entailment.HasAxiomFour H.logic where
  Four := by intros; constructor; simp [Entailment.theory];

class HasFourN (H : Hilbert.Normal α) (n : ℕ) where
  p : α
  mem_FourN : Axioms.FourN n (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFourN n] : Entailment.HasAxiomFourN n H where
  FourN φ := by
    simpa [Axioms.FourN] using Deduction.axm
      (φ := Axioms.FourN n (.atom (HasFourN.p H n)))
      (s := λ b => if (HasFourN.p H n) = b then φ else (.atom b))
      HasFourN.mem_FourN;


class HasFive (H : Hilbert.Normal α) where
  p : α
  mem_Five : Axioms.Five (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFive] : Entailment.HasAxiomFive H where
  Five φ := by
    simpa using Deduction.axm
      (φ := Axioms.Five (.atom (HasFive.p H)))
      (s := λ b => if (HasFive.p H) = b then φ else (.atom b))
      HasFive.mem_Five;

instance [H.HasFive] : Entailment.HasAxiomFive H.logic where
  Five := by intros; constructor; simp [Entailment.theory];


class HasPoint2 (H : Hilbert.Normal α) where
  p : α
  mem_Point2 : Axioms.Point2 (.atom p) ∈ H.axioms := by tauto;

instance [H.HasPoint2] : Entailment.HasAxiomPoint2 H where
  Point2 φ := by
    simpa using Deduction.axm
      (φ := Axioms.Point2 (.atom (HasPoint2.p H)))
      (s := λ b => if (HasPoint2.p H) = b then φ else (.atom b))
      HasPoint2.mem_Point2;

instance [H.HasPoint2] : Entailment.HasAxiomPoint2 H.logic where
  Point2 := by intros; constructor; simp [Entailment.theory];


class HasWeakPoint2 (H : Hilbert.Normal α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_WeakPoint2 : Axioms.WeakPoint2 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasWeakPoint2] : Entailment.HasAxiomWeakPoint2 H where
  WeakPoint2 φ ψ := by
    simpa [HasWeakPoint2.ne_pq] using Deduction.axm
      (φ := Axioms.WeakPoint2 (.atom (HasWeakPoint2.p H)) (.atom (HasWeakPoint2.q H)))
      (s := λ b =>
        if (HasWeakPoint2.p H) = b then φ
        else if (HasWeakPoint2.q H) = b then ψ
        else (.atom b))
      HasWeakPoint2.mem_WeakPoint2;
instance [H.HasWeakPoint2] : Entailment.HasAxiomWeakPoint2 H.logic where
  WeakPoint2 := by intros; constructor; simp [Entailment.theory];


class HasPoint3 (H : Hilbert.Normal α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Point3 : Axioms.Point3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasPoint3] : Entailment.HasAxiomPoint3 H where
  Point3 φ ψ := by
    simpa [HasPoint3.ne_pq] using Deduction.axm
      (φ := Axioms.Point3 (.atom (HasPoint3.p H)) (.atom (HasPoint3.q H)))
      (s := λ b =>
        if (HasPoint3.p H) = b then φ
        else if (HasPoint3.q H) = b then ψ
        else (.atom b))
      HasPoint3.mem_Point3;
instance [H.HasPoint3] : Entailment.HasAxiomPoint3 H.logic where
  Point3 := by intros; constructor; simp [Entailment.theory];


class HasWeakPoint3 (H : Hilbert.Normal α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_WeakPoint3 : Axioms.WeakPoint3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasWeakPoint3] : Entailment.HasAxiomWeakPoint3 H where
  WeakPoint3 φ ψ := by
    simpa [HasWeakPoint3.ne_pq] using Deduction.axm
      (φ := Axioms.WeakPoint3 (.atom (HasWeakPoint3.p H)) (.atom (HasWeakPoint3.q H)))
      (s := λ b =>
        if (HasWeakPoint3.p H) = b then φ
        else if (HasWeakPoint3.q H) = b then ψ
        else (.atom b))
      HasWeakPoint3.mem_WeakPoint3;

instance [H.HasWeakPoint3] : Entailment.HasAxiomWeakPoint3 H.logic where
  WeakPoint3 := by intros; constructor; simp [Entailment.theory];


class HasPoint4 (H : Hilbert.Normal α) where
  p : α
  mem_Point4 : Axioms.Point4 (.atom p) ∈ H.axioms := by tauto;

instance [H.HasPoint4] : Entailment.HasAxiomPoint4 H where
  Point4 φ := by
    simpa using Deduction.axm
      (φ := Axioms.Point4 (.atom (HasPoint4.p H)))
      (s := λ b => if (HasPoint4.p H) = b then φ else (.atom b))
      HasPoint4.mem_Point4;


class HasL (H : Hilbert.Normal α) where
  p : α
  mem_L : Axioms.L (.atom p) ∈ H.axioms := by tauto;

instance [H.HasL] : Entailment.HasAxiomL H where
  L φ := by
    simpa using Deduction.axm
      (φ := Axioms.L (.atom (HasL.p H)))
      (s := λ b => if (HasL.p H) = b then φ else (.atom b))
      HasL.mem_L;

instance [H.HasL] : Entailment.HasAxiomL H.logic where
  L := by intros; constructor; simp [Entailment.theory];


class HasZ (H : Hilbert.Normal α) where
  p : α
  mem_Z : Axioms.Z (.atom p) ∈ H.axioms := by tauto;

instance [H.HasZ] : Entailment.HasAxiomZ H where
  Z φ := by
    simpa using Deduction.axm
      (φ := Axioms.Z (.atom (HasZ.p H)))
      (s := λ b => if (HasZ.p H) = b then φ else (.atom b))
      HasZ.mem_Z;


class HasGrz (H : Hilbert.Normal α) where
  p : α
  mem_Grz : Axioms.Grz (.atom p) ∈ H.axioms := by tauto;

instance [H.HasGrz] : Entailment.HasAxiomGrz H where
  Grz φ := by
    simpa using Deduction.axm
      (φ := Axioms.Grz (.atom (HasGrz.p H)))
      (s := λ b => if (HasGrz.p H) = b then φ else (.atom b))
      HasGrz.mem_Grz;
instance [H.HasGrz] : Entailment.HasAxiomGrz H.logic where
  Grz := by intros; constructor; simp [Entailment.theory];


class HasDum (H : Hilbert.Normal α) where
  p : α
  mem_Dum : Axioms.Dum (.atom p) ∈ H.axioms := by tauto;

instance [H.HasDum] : Entailment.HasAxiomDum H where
  Dum φ := by
    simpa using Deduction.axm
      (φ := Axioms.Dum (.atom (HasDum.p H)))
      (s := λ b => if (HasDum.p H) = b then φ else (.atom b))
      HasDum.mem_Dum;


class HasTc (H : Hilbert.Normal α) where
  p : α
  mem_Tc : Axioms.Tc (.atom p) ∈ H.axioms := by tauto;

instance [H.HasTc] : Entailment.HasAxiomTc H where
  Tc φ := by
    simpa using Deduction.axm
      (φ := Axioms.Tc (.atom (HasTc.p H)))
      (s := λ b => if (HasTc.p H) = b then φ else (.atom b))
      HasTc.mem_Tc;


class HasVer (H : Hilbert.Normal α) where
  p : α
  mem_Ver : Axioms.Ver (.atom p) ∈ H.axioms := by tauto;

instance [H.HasVer] : Entailment.HasAxiomVer H where
  Ver φ := by
    simpa using Deduction.axm
      (φ := Axioms.Ver (.atom (HasVer.p H)))
      (s := λ b => if (HasVer.p H) = b then φ else (.atom b))
      HasVer.mem_Ver;
instance [H.HasVer] : Entailment.HasAxiomVer H.logic where
  Ver := by intros; constructor; simp [Entailment.theory];


class HasHen (H : Hilbert.Normal α) where
  p : α
  mem_Hen : Axioms.Hen (.atom p) ∈ H.axioms := by tauto;

instance [H.HasHen] : Entailment.HasAxiomHen H where
  Hen φ := by
    simpa using Deduction.axm
      (φ := Axioms.Hen (.atom (HasHen.p H)))
      (s := λ b => if (HasHen.p H) = b then φ else (.atom b))
      HasHen.mem_Hen;



class HasMcK (H : Hilbert.Normal α) where
  p : α
  mem_M : Axioms.McK (.atom p) ∈ H.axioms := by tauto;

instance [H.HasMcK] : Entailment.HasAxiomMcK H where
  McK φ := by
    simpa using Deduction.axm
      (φ := Axioms.McK (.atom (HasMcK.p H)))
      (s := λ b => if (HasMcK.p H) = b then φ else (.atom b))
      HasMcK.mem_M;


class HasMk (H : Hilbert.Normal α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Mk : Axioms.Mk (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasMk] : Entailment.HasAxiomMk H where
  Mk φ ψ := by
    simpa [HasMk.ne_pq] using Deduction.axm
      (φ := Axioms.Mk (.atom (HasMk.p H)) (.atom (HasMk.q H)))
      (s := λ b =>
        if (HasMk.p H) = b then φ
        else if (HasMk.q H) = b then ψ
        else (.atom b))
      HasMk.mem_Mk;


class HasH1 (H : Hilbert.Normal α) where
  p : α
  mem_H1 : Axioms.H (.atom p) ∈ H.axioms := by tauto;

instance [H.HasH1] : Entailment.HasAxiomH H where
  H1 φ := by
    simpa using Deduction.axm
      (φ := Axioms.H (.atom (HasH1.p H)))
      (s := λ b => if (HasH1.p H) = b then φ else (.atom b))
      HasH1.mem_H1;


class HasGeach (g) (H : Hilbert.Normal α) where
  p : α
  mem_Geach : Axioms.Geach g (.atom p) ∈ H.axioms := by tauto;

instance [H.HasGeach g] : Entailment.HasAxiomGeach g H where
  Geach φ := by
    simpa using Deduction.axm
      (φ := Axioms.Geach g (.atom (HasGeach.p g H)))
      (s := λ b => if (HasGeach.p g H) = b then φ else (.atom b))
      HasGeach.mem_Geach;

end

end Normal

end Hilbert


section

variable {H : Hilbert.Normal ℕ} {L : Logic ℕ}

open Formula (atom)
open Hilbert.Normal (weakerThan_of_subset_axioms weakerThan_of_provable_axioms)

protected abbrev Hilbert.K : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1)}⟩
protected abbrev K := Hilbert.K.logic
instance : Hilbert.K.HasK where p := 0; q := 1
instance : Entailment.K (Hilbert.K) where

instance [L.IsNormal] : Modal.K ⪯ L := by
  constructor;
  intro φ;
  suffices Hilbert.K ⊢! φ → L ⊢! φ by simpa [Logic.iff_provable, theory];
  intro hφ;
  induction hφ using Hilbert.Normal.rec! with
  | axm s h => rcases h with rfl; simp;
  | nec hφ => apply nec! hφ;
  | mdp hφψ hφ => exact mdp! hφψ hφ
  | imply₁ | imply₂ | ec => simp;


protected abbrev Hilbert.KT : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0)}⟩
protected abbrev KT := Hilbert.KT.logic
instance : (Hilbert.KT).HasK where p := 0; q := 1;
instance : (Hilbert.KT).HasT where p := 0
instance : Entailment.KT (Hilbert.KT) where
instance : Entailment.KT Modal.KT where


protected abbrev Hilbert.KD : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0)}⟩
protected abbrev KD := Hilbert.KD.logic
instance : (Hilbert.KD).HasK where p := 0; q := 1;
instance : (Hilbert.KD).HasD where p := 0
instance : Entailment.KD (Hilbert.KD) where
instance : Entailment.KD Modal.KD where

protected abbrev Hilbert.KP : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.P}⟩
protected abbrev KP : Logic ℕ := Hilbert.KP.logic
instance : Hilbert.KP.HasK where p := 0; q := 1
instance : Hilbert.KP.HasP where
instance : Entailment.KP (Hilbert.KP) where


instance : Hilbert.KP ≊ Hilbert.KD := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_provable_axioms; rintro φ (rfl | rfl) <;> simp;
  . apply weakerThan_of_provable_axioms; rintro φ (rfl | rfl) <;> simp;

instance : Modal.KP ≊ Modal.KD := inferInstance


protected abbrev Hilbert.KB : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0)}⟩
protected abbrev KB := Hilbert.KB.logic
instance : (Hilbert.KB).HasK where p := 0; q := 1;
instance : (Hilbert.KB).HasB where p := 0
instance : Entailment.KB (Hilbert.KB) where


protected abbrev Hilbert.KDB : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev KDB := Hilbert.KDB.logic
instance : (Hilbert.KDB).HasK where p := 0; q := 1;
instance : (Hilbert.KDB).HasD where p := 0
instance : (Hilbert.KDB).HasB where p := 0
instance : Entailment.KDB (Hilbert.KDB) where


protected abbrev Hilbert.KTB : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev KTB := Hilbert.KTB.logic
instance : (Hilbert.KTB).HasK where p := 0; q := 1;
instance : (Hilbert.KTB).HasT where p := 0
instance : (Hilbert.KTB).HasB where p := 0
instance : Entailment.KTB (Hilbert.KTB) where


protected abbrev Hilbert.KMcK : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.McK (.atom 0)}⟩
protected abbrev KMcK := Hilbert.KMcK.logic
instance : (Hilbert.KMcK).HasK where p := 0; q := 1;
instance : (Hilbert.KMcK).HasMcK where p := 0
instance : Entailment.KMcK (Hilbert.KMcK) where
instance : Hilbert.K ⪯ Hilbert.KMcK := weakerThan_of_subset_axioms $ by simp;


protected abbrev Hilbert.K4 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
protected abbrev K4 := Hilbert.K4.logic
instance : (Hilbert.K4).HasK where p := 0; q := 1;
instance : (Hilbert.K4).HasFour where p := 0
instance : Entailment.K4 (Hilbert.K4) where


protected abbrev Hilbert.K4n (n : ℕ) : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.FourN n (.atom 0)}⟩
protected abbrev K4n (n : ℕ) := Hilbert.K4n n |>.logic
instance : (Hilbert.K4n n).HasK where p := 0; q := 1;
instance : (Hilbert.K4n n).HasFourN n where p := 0;
instance : Entailment.K4n n (Hilbert.K4n n) where


protected abbrev Hilbert.K4McK : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.McK (.atom 0)}⟩
protected abbrev K4McK := Hilbert.K4McK.logic
instance : (Hilbert.K4McK).HasK where p := 0; q := 1;
instance : (Hilbert.K4McK).HasFour where p := 0
instance : (Hilbert.K4McK).HasMcK where p := 0
instance : Entailment.K4McK (Hilbert.K4McK) where

instance : Hilbert.K ⪯ Hilbert.K4McK := weakerThan_of_subset_axioms $ by simp;

noncomputable instance [Entailment.K H] [Hilbert.K4McK ⪯ H] : Entailment.K4McK H where
  Four _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4McK) (by simp) |>.some
  McK _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4McK) (by simp) |>.some



protected abbrev Hilbert.K4Point2 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev K4Point2 := Hilbert.K4Point2.logic
instance : (Hilbert.K4Point2).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point2).HasFour where p := 0
instance : (Hilbert.K4Point2).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.K4Point2 (Hilbert.K4Point2) where

protected abbrev Hilbert.K4Point3 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev K4Point3 := Hilbert.K4Point3.logic
instance : (Hilbert.K4Point3).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point3).HasFour where p := 0
instance : (Hilbert.K4Point3).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.K4Point3 (Hilbert.K4Point3) where


protected abbrev Hilbert.KT4B : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev KT4B := Hilbert.KT4B.logic
instance : (Hilbert.KT4B).HasK where p := 0; q := 1;
instance : (Hilbert.KT4B).HasT where p := 0
instance : (Hilbert.KT4B).HasFour where p := 0
instance : (Hilbert.KT4B).HasB where p := 0
instance : Entailment.KT4B (Hilbert.KT4B) where


protected abbrev Hilbert.K45 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev K45 := Hilbert.K45.logic
instance : (Hilbert.K45).HasK where p := 0; q := 1;
instance : (Hilbert.K45).HasFour where p := 0
instance : (Hilbert.K45).HasFive where p := 0
instance : Entailment.K45 (Hilbert.K45) where


protected abbrev Hilbert.KD4 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev KD4 := Hilbert.KD4.logic
instance : (Hilbert.KD4).HasK where p := 0; q := 1;
instance : (Hilbert.KD4).HasD where p := 0
instance : (Hilbert.KD4).HasFour where p := 0
instance : Entailment.KD4 (Hilbert.KD4) where


protected abbrev Hilbert.KD5 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev KD5 := Hilbert.KD5.logic
instance : (Hilbert.KD5).HasK where p := 0; q := 1;
instance : (Hilbert.KD5).HasD where p := 0
instance : (Hilbert.KD5).HasFive where p := 0
instance : Entailment.KD5 (Hilbert.KD5) where


protected abbrev Hilbert.KD45 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev KD45 := Hilbert.KD45.logic
instance : (Hilbert.KD45).HasK where p := 0; q := 1;
instance : (Hilbert.KD45).HasD where p := 0
instance : (Hilbert.KD45).HasFour where p := 0
instance : (Hilbert.KD45).HasFive where p := 0
instance : Entailment.KD45 (Hilbert.KD45) where


protected abbrev Hilbert.KB4 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev KB4 := Hilbert.KB4.logic
instance : (Hilbert.KB4).HasK where p := 0; q := 1;
instance : (Hilbert.KB4).HasB where p := 0
instance : (Hilbert.KB4).HasFour where p := 0
instance : Entailment.KB4 (Hilbert.KB4) where


protected abbrev Hilbert.KB5 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev KB5 := Hilbert.KB5.logic
instance : (Hilbert.KB5).HasK where p := 0; q := 1;
instance : (Hilbert.KB5).HasB where p := 0
instance : (Hilbert.KB5).HasFive where p := 0
instance : Entailment.KB5 (Hilbert.KB5) where


protected abbrev Modal.S4 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev S4 := Modal.S4.logic
instance : (Modal.S4).HasK where p := 0; q := 1;
instance : (Modal.S4).HasT where p := 0
instance : (Modal.S4).HasFour where p := 0
instance : Entailment.S4 (Modal.S4) where
instance : Hilbert.K4 ⪯ Modal.S4 := weakerThan_of_subset_axioms $ by simp;


protected abbrev Modal.S4McK : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0)}⟩
protected abbrev S4McK := Modal.S4McK.logic
instance : (Modal.S4McK).HasK where p := 0; q := 1;
instance : (Modal.S4McK).HasT where p := 0
instance : (Modal.S4McK).HasFour where p := 0
instance : (Modal.S4McK).HasMcK where p := 0
instance : Entailment.S4McK (Modal.S4McK) where
instance : Hilbert.K4McK ⪯ Modal.S4McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Modal.S4Point2McK : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev S4Point2McK := Modal.S4Point2McK.logic
instance : (Modal.S4Point2McK).HasK where p := 0; q := 1;
instance : (Modal.S4Point2McK).HasT where p := 0
instance : (Modal.S4Point2McK).HasFour where p := 0
instance : (Modal.S4Point2McK).HasMcK where p := 0
instance : (Modal.S4Point2McK).HasPoint2 where p := 0
instance : Entailment.S4Point2McK (Modal.S4Point2McK) where
instance : Hilbert.K4McK ⪯ Modal.S4Point2McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Modal.S4Point3McK : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev S4Point3McK := Modal.S4Point3McK.logic
instance : (Modal.S4Point3McK).HasK where p := 0; q := 1;
instance : (Modal.S4Point3McK).HasT where p := 0
instance : (Modal.S4Point3McK).HasFour where p := 0
instance : (Modal.S4Point3McK).HasMcK where p := 0
instance : (Modal.S4Point3McK).HasPoint3 where p := 0; q := 1;
instance : Entailment.S4Point3McK (Modal.S4Point3McK) where
instance : Hilbert.K4McK ⪯ Modal.S4Point3McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Modal.S4Point4McK : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point4 (.atom 0)}⟩
protected abbrev S4Point4McK := Modal.S4Point4McK.logic
instance : (Modal.S4Point4McK).HasK where p := 0; q := 1;
instance : (Modal.S4Point4McK).HasT where p := 0
instance : (Modal.S4Point4McK).HasFour where p := 0
instance : (Modal.S4Point4McK).HasMcK where p := 0
instance : (Modal.S4Point4McK).HasPoint4 where p := 0
instance : Entailment.S4Point4McK (Modal.S4Point4McK) where
instance : Hilbert.K4McK ⪯ Modal.S4Point4McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Modal.S4Point2 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev S4Point2 := Modal.S4Point2.logic
instance : (Modal.S4Point2).HasK where p := 0; q := 1;
instance : (Modal.S4Point2).HasT where p := 0
instance : (Modal.S4Point2).HasFour where p := 0
instance : (Modal.S4Point2).HasPoint2 where p := 0
instance : Entailment.S4Point2 (Modal.S4Point2) where


protected abbrev Modal.S4Point3 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev S4Point3 := Modal.S4Point3.logic
instance : (Modal.S4Point3).HasK where p := 0; q := 1;
instance : (Modal.S4Point3).HasT where p := 0
instance : (Modal.S4Point3).HasFour where p := 0
instance : (Modal.S4Point3).HasPoint3 where p := 0; q := 1;
instance : Entailment.S4Point3 (Modal.S4Point3) where


protected abbrev Modal.S4Point4 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point4 (.atom 0)}⟩
protected abbrev S4Point4 := Modal.S4Point4.logic
instance : (Modal.S4Point4).HasK where p := 0; q := 1;
instance : (Modal.S4Point4).HasT where p := 0
instance : (Modal.S4Point4).HasFour where p := 0
instance : (Modal.S4Point4).HasPoint4 where p := 0
instance : Entailment.S4Point4 (Modal.S4Point4) where


protected abbrev Hilbert.K5 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Five (.atom 0)}⟩
protected abbrev K5 := Hilbert.K5.logic
instance : (Hilbert.K5).HasK where p := 0; q := 1;
instance : (Hilbert.K5).HasFive where p := 0
instance : Entailment.K5 (Hilbert.K5) where


protected abbrev Modal.S5 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev S5 := Modal.S5.logic
instance : (Modal.S5).HasK where p := 0; q := 1;
instance : (Modal.S5).HasT where p := 0
instance : (Modal.S5).HasFive where p := 0
instance : Entailment.S5 (Modal.S5) where


protected abbrev Modal.GL : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}⟩
protected abbrev GL := Modal.GL.logic
instance : (Modal.GL).HasK where p := 0; q := 1;
instance : (Modal.GL).HasL where p := 0;
instance : Entailment.GL (Modal.GL) where
instance : Entailment.GL Modal.GL where

protected abbrev Modal.GLPoint2 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev GLPoint2 := Modal.GLPoint2.logic
instance : (Modal.GLPoint2).HasK where p := 0; q := 1;
instance : (Modal.GLPoint2).HasL where p := 0
instance : (Modal.GLPoint2).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.GLPoint2 (Modal.GLPoint2) where
instance : Entailment.GLPoint2 Modal.GLPoint2 where
instance : Modal.GL ⪯ Modal.GLPoint2 := weakerThan_of_subset_axioms $ by simp


protected abbrev Modal.GLPoint3 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev GLPoint3 := Modal.GLPoint3.logic
instance : (Modal.GLPoint3).HasK where p := 0; q := 1;
instance : (Modal.GLPoint3).HasL where p := 0
instance : (Modal.GLPoint3).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.GLPoint3 (Modal.GLPoint3) where


protected abbrev Hilbert.K4Z : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0)}⟩
protected abbrev K4Z := Hilbert.K4Z.logic
instance : (Hilbert.K4Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Z).HasFour where p := 0
instance : (Hilbert.K4Z).HasZ where p := 0
instance : Entailment.K4Z (Hilbert.K4Z) where

instance : Hilbert.K4 ⪯ Hilbert.K4Z := weakerThan_of_subset_axioms $ by simp
instance : Modal.K4 ⪯ Modal.K4Z := inferInstance

instance : Hilbert.K4Z ⪯ Modal.GL := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.K4Z ⪯ Modal.GL := inferInstance


protected abbrev Hilbert.K4Point2Z : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev K4Point2Z := Hilbert.K4Point2Z.logic
instance : (Hilbert.K4Point2Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point2Z).HasFour where p := 0
instance : (Hilbert.K4Point2Z).HasZ where p := 0
instance : (Hilbert.K4Point2Z).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.K4Point2Z (Hilbert.K4Point2Z) where

instance : Hilbert.K4Point2 ⪯ Hilbert.K4Point2Z := weakerThan_of_subset_axioms (by simp)
instance : Modal.K4Point2 ⪯ Modal.K4Point2Z := inferInstance

instance : Hilbert.K4Z ⪯ Hilbert.K4Point2Z := weakerThan_of_subset_axioms (by simp)
instance : Modal.K4Z ⪯ Modal.K4Point2Z := inferInstance

instance : Hilbert.K4Point2Z ⪯ Modal.GLPoint2 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.K4Point2Z ⪯ Modal.GLPoint2 := inferInstance


protected abbrev Hilbert.K4Point3Z : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev K4Point3Z := Hilbert.K4Point3Z.logic
instance : (Hilbert.K4Point3Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point3Z).HasFour where p := 0
instance : (Hilbert.K4Point3Z).HasZ where p := 0
instance : (Hilbert.K4Point3Z).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.K4Point3Z (Hilbert.K4Point3Z) where

instance : Hilbert.K4Point3 ⪯ Hilbert.K4Point3Z := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.K4Point3 ⪯ Modal.K4Point3Z := inferInstance

instance : Hilbert.K4Z ⪯ Hilbert.K4Point3Z := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.K4Z ⪯ Modal.K4Point3Z := inferInstance

instance : Hilbert.K4Point3Z ⪯ Modal.GLPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.K4Point3Z ⪯ Modal.GLPoint3 := inferInstance


protected abbrev Hilbert.KHen : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Hen (.atom 0)}⟩
protected abbrev KHen := Hilbert.KHen.logic
instance : (Hilbert.KHen).HasK where p := 0; q := 1;
instance : (Hilbert.KHen).HasHen where p := 0;


protected abbrev Hilbert.K4Hen : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Hen (.atom 0)}⟩
protected abbrev K4Hen := Hilbert.K4Hen.logic
instance : (Hilbert.K4Hen).HasK where p := 0; q := 1;
instance : (Hilbert.K4Hen).HasFour where p := 0
instance : (Hilbert.K4Hen).HasHen where p := 0
instance : Entailment.K4Hen (Hilbert.K4Hen) where


protected abbrev Modal.Grz : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}⟩
protected abbrev Grz := Modal.Grz.logic
instance : (Modal.Grz).HasK where p := 0; q := 1;
instance : (Modal.Grz).HasGrz where p := 0
instance : Entailment.Grz (Modal.Grz) where
instance : Hilbert.KT ⪯ Modal.Grz := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl) <;> simp;


protected abbrev Modal.GrzPoint2 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev GrzPoint2 := Modal.GrzPoint2.logic
instance : (Modal.GrzPoint2).HasK where p := 0; q := 1;
instance : (Modal.GrzPoint2).HasGrz where p := 0
instance : (Modal.GrzPoint2).HasPoint2 where p := 0
instance : Entailment.GrzPoint2 (Modal.GrzPoint2) where


protected abbrev Modal.GrzPoint3 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev GrzPoint3 := Modal.GrzPoint3.logic
instance : (Modal.GrzPoint3).HasK where p := 0; q := 1;
instance : (Modal.GrzPoint3).HasGrz where p := 0
instance : (Modal.GrzPoint3).HasPoint3 where p := 0; q := 1;
instance : Entailment.GrzPoint3 (Modal.GrzPoint3) where


protected abbrev Hilbert.Dum : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0)}⟩
protected abbrev Dum := Hilbert.Dum.logic
instance : (Hilbert.Dum).HasK where p := 0; q := 1;
instance : (Hilbert.Dum).HasT where p := 0
instance : (Hilbert.Dum).HasFour where p := 0
instance : (Hilbert.Dum).HasDum where p := 0
instance : Entailment.Dum (Hilbert.Dum) where

instance : Modal.S4 ⪯ Hilbert.Dum := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.S4 ⪯ Modal.Dum := inferInstance

instance : Hilbert.Dum ⪯ Modal.Grz := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.Dum ⪯ Modal.Grz := inferInstance


protected abbrev Hilbert.DumPoint2 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev DumPoint2 := Hilbert.DumPoint2.logic
instance : (Hilbert.DumPoint2).HasK where p := 0; q := 1;
instance : (Hilbert.DumPoint2).HasT where p := 0
instance : (Hilbert.DumPoint2).HasFour where p := 0
instance : (Hilbert.DumPoint2).HasDum where p := 0
instance : (Hilbert.DumPoint2).HasPoint2 where p := 0
instance : Entailment.DumPoint2 (Hilbert.DumPoint2) where

instance : Hilbert.Dum ⪯ Hilbert.DumPoint2 := weakerThan_of_subset_axioms (by simp)
instance : Modal.Dum ⪯ Modal.DumPoint2 := inferInstance

instance : Modal.S4Point2 ⪯ Hilbert.DumPoint2 := weakerThan_of_subset_axioms (by simp)
instance : Modal.S4Point2 ⪯ Modal.DumPoint2 := inferInstance

instance : Hilbert.DumPoint2 ⪯ Modal.GrzPoint2 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.DumPoint2 ⪯ Modal.GrzPoint2 := inferInstance


protected abbrev Hilbert.DumPoint3 : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev DumPoint3 := Hilbert.DumPoint3.logic
instance : (Hilbert.DumPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.DumPoint3).HasT where p := 0
instance : (Hilbert.DumPoint3).HasFour where p := 0
instance : (Hilbert.DumPoint3).HasDum where p := 0
instance : (Hilbert.DumPoint3).HasPoint3 where p := 0; q := 1;
instance : Entailment.DumPoint3 (Hilbert.DumPoint3) where

instance : Hilbert.Dum ⪯ Hilbert.DumPoint3 := weakerThan_of_subset_axioms (by simp)
instance : Modal.Dum ⪯ Modal.DumPoint3 := inferInstance

instance : Modal.S4Point3 ⪯ Hilbert.DumPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.S4Point3 ⪯ Modal.DumPoint3 := inferInstance

instance : Hilbert.DumPoint3 ⪯ Modal.GrzPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;
instance : Modal.DumPoint3 ⪯ Modal.GrzPoint3 := inferInstance


protected abbrev Hilbert.KTc : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Tc (.atom 0)}⟩
protected abbrev KTc := Hilbert.KTc.logic
instance : (Hilbert.KTc).HasK where p := 0; q := 1;
instance : (Hilbert.KTc).HasTc where p := 0
instance : Entailment.KTc (Hilbert.KTc) where


protected abbrev Hilbert.KD4Point3Z : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1), Axioms.Z (.atom 0)}⟩
protected abbrev KD4Point3Z := Hilbert.KD4Point3Z.logic
instance : (Hilbert.KD4Point3Z).HasK where p := 0; q := 1;
instance : (Hilbert.KD4Point3Z).HasD where p := 0
instance : (Hilbert.KD4Point3Z).HasFour where p := 0
instance : (Hilbert.KD4Point3Z).HasWeakPoint3 where p := 0; q := 1;
instance : (Hilbert.KD4Point3Z).HasZ where p := 0
instance : Entailment.KD4Point3Z (Hilbert.KD4Point3Z) where


protected abbrev Hilbert.KTMk : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Mk (.atom 0) (.atom 1)}⟩
protected abbrev KTMk := Hilbert.KTMk.logic
instance : (Hilbert.KTMk).HasK where p := 0; q := 1;
instance : (Hilbert.KTMk).HasT where p := 0
instance : (Hilbert.KTMk).HasMk where p := 0; q := 1
instance : Entailment.KTMk (Hilbert.KTMk) where


protected abbrev Modal.S4H : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.H (.atom 0)}⟩
/--
  - `S4H` in Segerberg 1971.
  - `K1.2` in Sobocinski 1964, "Family $K$ of the non-Lewis modal systems"
-/
protected abbrev S4H := Modal.S4H.logic

instance : (Modal.S4H).HasK where p := 0; q := 1;
instance : (Modal.S4H).HasT where p := 0
instance : (Modal.S4H).HasFour where p := 0
instance : (Modal.S4H).HasH1 where p := 0
instance : Entailment.S4H (Modal.S4H) where


protected abbrev Hilbert.N : Hilbert.Normal ℕ := ⟨{}⟩
protected abbrev N := Hilbert.N.logic


protected abbrev Modal.Ver : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}⟩
protected abbrev Ver := Modal.Ver.logic
instance : (Modal.Ver).HasK where p := 0; q := 1;
instance : (Modal.Ver).HasVer where p := 0
instance : Entailment.Ver (Modal.Ver) where


protected abbrev Modal.Triv : Hilbert.Normal ℕ := ⟨{ Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}⟩
protected abbrev Triv := Modal.Triv.logic
instance : (Modal.Triv).HasK where p := 0; q := 1;
instance : (Modal.Triv).HasT where p := 0
instance : (Modal.Triv).HasTc where p := 0
instance : Entailment.Triv (Modal.Triv) where
instance : Hilbert.K4 ⪯ Modal.Triv := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl) <;> simp;


protected abbrev Modal.S5Grz : Hilbert.Normal ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0), Axioms.Grz (.atom 0)}⟩
protected abbrev S5Grz : Logic ℕ := Modal.S5Grz.logic
instance : (Modal.S5Grz).HasK where p := 0; q := 1;
instance : (Modal.S5Grz).HasT where p := 0
instance : (Modal.S5Grz).HasFive where p := 0
instance : (Modal.S5Grz).HasGrz where p := 0
instance : Entailment.S5Grz (Modal.S5Grz) where

instance : Modal.S5Grz ≊ Modal.Triv := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_provable_axioms; rintro φ (rfl | rfl | rfl | rfl) <;> simp;
  . apply weakerThan_of_provable_axioms; rintro φ (rfl | rfl | rfl) <;> simp;
instance : Modal.S5Grz ≊ Modal.Triv := inferInstance


end

end LO.Modal
