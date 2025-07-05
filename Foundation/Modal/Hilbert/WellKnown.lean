import Foundation.Modal.Hilbert.K
import Foundation.Modal.Entailment.GL
import Foundation.Modal.Entailment.Grz

namespace LO.Modal


namespace Hilbert

open Entailment
open Deduction

variable {H : Hilbert α}
variable [DecidableEq α]


class HasT (H : Hilbert α) where
  p : α
  mem_T : Axioms.T (.atom p) ∈ H.axioms := by tauto;

instance [H.HasT] : Entailment.HasAxiomT H.logic where
  T φ := by
    constructor;
    apply maxm;
    use Axioms.T (.atom (HasT.p H));
    constructor;
    . exact HasT.mem_T;
    . use (λ b => if (HasT.p H) = b then φ else (.atom b));
      simp;

class HasB (H : Hilbert α) where
  p : α
  mem_B : Axioms.B (.atom p) ∈ H.axioms := by tauto;

instance [H.HasB] : Entailment.HasAxiomB H.logic where
  B φ := by
    constructor;
    apply maxm;
    use Axioms.B (.atom (HasB.p H));
    constructor;
    . exact HasB.mem_B;
    . use (λ b => if (HasB.p H) = b then φ else (.atom b));
      simp;

class HasD (H : Hilbert α) where
  p : α
  mem_D : Axioms.D (.atom p) ∈ H.axioms := by tauto;

instance [H.HasD] : Entailment.HasAxiomD H.logic where
  D φ := by
    constructor;
    apply maxm;
    use Axioms.D (.atom (HasD.p H));
    constructor;
    . exact HasD.mem_D;
    . use (λ b => if (HasD.p H) = b then φ else (.atom b));
      simp;

class HasFour (H : Hilbert α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFour] : Entailment.HasAxiomFour H.logic where
  Four φ := by
    constructor;
    apply maxm;
    use Axioms.Four (.atom (HasFour.p H));
    constructor;
    . exact HasFour.mem_Four;
    . use (λ b => if (HasFour.p H) = b then φ else (.atom b));
      simp;

class HasFourN (H : Hilbert α) (n : ℕ+) where
  p : α
  mem_FourN : Axioms.FourN n (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFourN n] : Entailment.HasAxiomFourN n H.logic where
  FourN φ := by
    constructor;
    apply maxm;
    use Axioms.FourN n (.atom (HasFourN.p H n));
    constructor;
    . exact HasFourN.mem_FourN;
    . use (λ b => if (HasFourN.p H n) = b then φ else (.atom b));
      simp;


class HasFive (H : Hilbert α) where
  p : α
  mem_Five : Axioms.Five (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFive] : Entailment.HasAxiomFive H.logic where
  Five φ := by
    constructor;
    apply maxm;
    use Axioms.Five (.atom (HasFive.p H));
    constructor;
    . exact HasFive.mem_Five;
    . use (λ b => if (HasFive.p H) = b then φ else (.atom b));
      simp;

class HasPoint2 (H : Hilbert α) where
  p : α
  mem_Point2 : Axioms.Point2 (.atom p) ∈ H.axioms := by tauto;

instance [H.HasPoint2] : Entailment.HasAxiomPoint2 H.logic where
  Point2 φ := by
    constructor;
    apply maxm;
    use Axioms.Point2 (.atom (HasPoint2.p H));
    constructor;
    . exact HasPoint2.mem_Point2;
    . use (λ b => if (HasPoint2.p H) = b then φ else (.atom b));
      simp;

class HasWeakPoint2 (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_WeakPoint2 : Axioms.WeakPoint2 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasWeakPoint2] : Entailment.HasAxiomWeakPoint2 H.logic where
  WeakPoint2 φ ψ := by
    constructor;
    apply maxm;
    use Axioms.WeakPoint2 (.atom (HasWeakPoint2.p H)) (.atom (HasWeakPoint2.q H));
    constructor;
    . exact HasWeakPoint2.mem_WeakPoint2;
    . use (λ b => if (HasWeakPoint2.p H) = b then φ else if (HasWeakPoint2.q H) = b then ψ else (.atom b));
      simp [HasWeakPoint2.ne_pq];

class HasPoint3 (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Point3 : Axioms.Point3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasPoint3] : Entailment.HasAxiomPoint3 H.logic where
  Point3 φ ψ := by
    constructor;
    apply maxm;
    use Axioms.Point3 (.atom (HasPoint3.p H)) (.atom (HasPoint3.q H));
    constructor;
    . exact HasPoint3.mem_Point3;
    . use (λ b => if (HasPoint3.p H) = b then φ else if (HasPoint3.q H) = b then ψ else (.atom b));
      simp [HasPoint3.ne_pq];


class HasWeakPoint3 (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_WeakPoint3 : Axioms.WeakPoint3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasWeakPoint3] : Entailment.HasAxiomWeakPoint3 H.logic where
  WeakPoint3 φ ψ := by
    constructor;
    apply maxm;
    use Axioms.WeakPoint3 (.atom (HasWeakPoint3.p H)) (.atom (HasWeakPoint3.q H));
    constructor;
    . exact HasWeakPoint3.mem_WeakPoint3;
    . use (λ b => if (HasWeakPoint3.p H) = b then φ else if (HasWeakPoint3.q H) = b then ψ else (.atom b));
      simp [HasWeakPoint3.ne_pq];


class HasPoint4 (H : Hilbert α) where
  p : α
  mem_Point4 : Axioms.Point4 (.atom p) ∈ H.axioms := by tauto;

instance [H.HasPoint4] : Entailment.HasAxiomPoint4 H.logic where
  Point4 φ := by
    constructor;
    apply maxm;
    use Axioms.Point4 (.atom $ HasPoint4.p H);
    constructor;
    . exact HasPoint4.mem_Point4;
    . use (λ b => if b = (HasPoint4.p H) then φ else (.atom b));
      simp;


class HasL (H : Hilbert α) where
  p : α
  mem_L : Axioms.L (.atom p) ∈ H.axioms := by tauto;

instance [H.HasL] : Entailment.HasAxiomL H.logic where
  L φ := by
    constructor;
    apply maxm;
    use Axioms.L (.atom (HasL.p H));
    constructor;
    . exact HasL.mem_L;
    . use (λ b => if (HasL.p H) = b then φ else (.atom b));
      simp;


class HasGrz (H : Hilbert α) where
  p : α
  mem_Grz : Axioms.Grz (.atom p) ∈ H.axioms := by tauto;

instance [H.HasGrz] : Entailment.HasAxiomGrz H.logic where
  Grz φ := by
    constructor;
    apply maxm;
    use Axioms.Grz (.atom (HasGrz.p H));
    constructor;
    . exact HasGrz.mem_Grz;
    . use (λ b => if (HasGrz.p H) = b then φ else (.atom b));
      simp;


class HasDum (H : Hilbert α) where
  p : α
  mem_Dum : Axioms.Dum (.atom p) ∈ H.axioms := by tauto;

instance [H.HasDum] : Entailment.HasAxiomDum H.logic where
  Dum φ := by
    constructor;
    apply maxm;
    use Axioms.Dum (.atom $ HasDum.p H);
    constructor;
    . exact HasDum.mem_Dum;
    . use (λ b => if b = (HasDum.p H) then φ else (.atom b));
      simp;


class HasTc (H : Hilbert α) where
  p : α
  mem_Tc : Axioms.Tc (.atom p) ∈ H.axioms := by tauto;

instance [H.HasTc] : Entailment.HasAxiomTc H.logic where
  Tc φ := by
    constructor;
    apply maxm;
    use Axioms.Tc (.atom (HasTc.p H));
    constructor;
    . exact HasTc.mem_Tc;
    . use (λ b => if (HasTc.p H) = b then φ else (.atom b));
      simp;


class HasVer (H : Hilbert α) where
  p : α
  mem_Ver : Axioms.Ver (.atom p) ∈ H.axioms := by tauto;

instance [H.HasVer] : Entailment.HasAxiomVer H.logic where
  Ver φ := by
    constructor;
    apply maxm;
    use Axioms.Ver (.atom (HasVer.p H));
    constructor;
    . exact HasVer.mem_Ver;
    . use (λ b => if (HasVer.p H) = b then φ else (.atom b));
      simp;


class HasHen (H : Hilbert α) where
  p : α
  mem_Hen : Axioms.Hen (.atom p) ∈ H.axioms := by tauto;

instance [H.HasHen] : Entailment.HasAxiomHen H.logic where
  Hen φ := by
    constructor;
    apply maxm;
    use Axioms.Hen (.atom (HasHen.p H));
    constructor;
    . exact HasHen.mem_Hen;
    . use (λ b => if (HasHen.p H) = b then φ else (.atom b));
      simp;


class HasZ (H : Hilbert α) where
  p : α
  mem_Z : Axioms.Z (.atom p) ∈ H.axioms := by tauto;

instance [H.HasZ] : Entailment.HasAxiomZ H.logic where
  Z φ := by
    constructor;
    apply maxm;
    use Axioms.Z (.atom (HasZ.p H));
    constructor;
    . exact HasZ.mem_Z;
    . use (λ b => if (HasZ.p H) = b then φ else (.atom b));
      simp;

class HasMcK (H : Hilbert α) where
  p : α
  mem_M : Axioms.McK (.atom p) ∈ H.axioms := by tauto;

instance [H.HasMcK] : Entailment.HasAxiomMcK H.logic where
  McK φ := by
    constructor;
    apply maxm;
    use Axioms.McK (.atom (HasMcK.p H));
    constructor;
    . exact HasMcK.mem_M;
    . use (λ b => if (HasMcK.p H) = b then φ else (.atom b));
      simp;


class HasMk (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Mk : Axioms.Mk (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasMk] : Entailment.HasAxiomMk H.logic where
  Mk φ ψ := by
    constructor;
    apply maxm;
    use Axioms.Mk (.atom $ HasMk.p H) (.atom $ HasMk.q H);
    constructor;
    . exact HasMk.mem_Mk;
    . use (λ b => if b = (HasMk.q H) then ψ else if b = (HasMk.p H) then φ else (.atom b));
      simp [HasMk.ne_pq];


class HasGeach (g) (H : Hilbert α) where
  p : α
  mem_Geach : Axioms.Geach g (.atom p) ∈ H.axioms := by tauto;

instance [H.HasGeach g] : Entailment.HasAxiomGeach g H.logic where
  Geach φ := by
    constructor;
    apply maxm;
    use Axioms.Geach g (.atom (HasGeach.p g H));
    constructor;
    . exact HasGeach.mem_Geach;
    . use (λ b => if HasGeach.p g H = b then φ else (.atom b));
      simp;


end Hilbert


variable {L : Logic _}

open Formula (atom)
open Hilbert (weakerThan_of_subset_axioms)
open Hilbert (weakerThan_of_provable_axioms)


protected abbrev Hilbert.KT : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0)}⟩
protected abbrev Logic.KT := Hilbert.KT.logic
instance : (Hilbert.KT).HasK where p := 0; q := 1;
instance : (Hilbert.KT).HasT where p := 0
instance : Entailment.KT (Logic.KT) where


protected abbrev Hilbert.KD : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0)}⟩
protected abbrev Logic.KD := Hilbert.KD.logic
instance : (Hilbert.KD).HasK where p := 0; q := 1;
instance : (Hilbert.KD).HasD where p := 0
instance : Entailment.KD (Logic.KD) where


protected abbrev Hilbert.KB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0)}⟩
protected abbrev Logic.KB := Hilbert.KB.logic
instance : (Hilbert.KB).HasK where p := 0; q := 1;
instance : (Hilbert.KB).HasB where p := 0
instance : Entailment.KB (Logic.KB) where


protected abbrev Hilbert.KDB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev Logic.KDB := Hilbert.KDB.logic
instance : (Hilbert.KDB).HasK where p := 0; q := 1;
instance : (Hilbert.KDB).HasD where p := 0
instance : (Hilbert.KDB).HasB where p := 0
instance : Entailment.KDB (Logic.KDB) where


protected abbrev Hilbert.KTB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev Logic.KTB := Hilbert.KTB.logic
instance : (Hilbert.KTB).HasK where p := 0; q := 1;
instance : (Hilbert.KTB).HasT where p := 0
instance : (Hilbert.KTB).HasB where p := 0
instance : Entailment.KTB (Logic.KTB) where


protected abbrev Hilbert.KMcK : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.McK (.atom 0)}⟩
protected abbrev Logic.KMcK := Hilbert.KMcK.logic
instance : (Hilbert.KMcK).HasK where p := 0; q := 1;
instance : (Hilbert.KMcK).HasMcK where p := 0
instance : Entailment.KMcK (Logic.KMcK) where
instance : Logic.K ⪯ Logic.KMcK := weakerThan_of_subset_axioms $ by simp;


protected abbrev Hilbert.K4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.K4 := Hilbert.K4.logic
instance : (Hilbert.K4).HasK where p := 0; q := 1;
instance : (Hilbert.K4).HasFour where p := 0
instance : Entailment.K4 (Logic.K4) where

protected abbrev Hilbert.K4n (n : ℕ+) : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.FourN n (.atom 0)}⟩
protected abbrev Logic.K4n (n : ℕ+) := Hilbert.K4n n |>.logic
instance : (Hilbert.K4n n).HasK where p := 0; q := 1;
instance : (Hilbert.K4n n).HasFourN n where p := 0;


protected abbrev Hilbert.K4McK : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.McK (.atom 0)}⟩
protected abbrev Logic.K4McK := Hilbert.K4McK.logic
instance : (Hilbert.K4McK).HasK where p := 0; q := 1;
instance : (Hilbert.K4McK).HasFour where p := 0
instance : (Hilbert.K4McK).HasMcK where p := 0
instance : Entailment.K4McK (Logic.K4McK) where

instance : Logic.K ⪯ Logic.K4McK := weakerThan_of_subset_axioms $ by simp;

noncomputable instance [Entailment.K L] [Logic.K4McK ⪯ L] : Entailment.K4McK L where
  Four _ := Entailment.WeakerThan.pbl (𝓢 := Logic.K4McK) (by simp) |>.some
  McK _ := Entailment.WeakerThan.pbl (𝓢 := Logic.K4McK) (by simp) |>.some



protected abbrev Hilbert.K4Point2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K4Point2 := Hilbert.K4Point2.logic
instance : (Hilbert.K4Point2).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point2).HasFour where p := 0
instance : (Hilbert.K4Point2).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.K4Point2 (Logic.K4Point2) where

protected abbrev Hilbert.K4Point3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K4Point3 := Hilbert.K4Point3.logic
instance : (Hilbert.K4Point3).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point3).HasFour where p := 0
instance : (Hilbert.K4Point3).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.K4Point3 (Logic.K4Point3) where


protected abbrev Hilbert.KT4B : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev Logic.KT4B := Hilbert.KT4B.logic
instance : (Hilbert.KT4B).HasK where p := 0; q := 1;
instance : (Hilbert.KT4B).HasT where p := 0
instance : (Hilbert.KT4B).HasFour where p := 0
instance : (Hilbert.KT4B).HasB where p := 0
instance : Entailment.KT4B (Logic.KT4B) where


protected abbrev Hilbert.K45 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.K45 := Hilbert.K45.logic
instance : (Hilbert.K45).HasK where p := 0; q := 1;
instance : (Hilbert.K45).HasFour where p := 0
instance : (Hilbert.K45).HasFive where p := 0
instance : Entailment.K45 (Logic.K45) where


protected abbrev Hilbert.KD4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.KD4 := Hilbert.KD4.logic
instance : (Hilbert.KD4).HasK where p := 0; q := 1;
instance : (Hilbert.KD4).HasD where p := 0
instance : (Hilbert.KD4).HasFour where p := 0
instance : Entailment.KD4 (Logic.KD4) where


protected abbrev Hilbert.KD5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.KD5 := Hilbert.KD5.logic
instance : (Hilbert.KD5).HasK where p := 0; q := 1;
instance : (Hilbert.KD5).HasD where p := 0
instance : (Hilbert.KD5).HasFive where p := 0
instance : Entailment.KD5 (Logic.KD5) where


protected abbrev Hilbert.KD45 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.KD45 := Hilbert.KD45.logic
instance : (Hilbert.KD45).HasK where p := 0; q := 1;
instance : (Hilbert.KD45).HasD where p := 0
instance : (Hilbert.KD45).HasFour where p := 0
instance : (Hilbert.KD45).HasFive where p := 0
instance : Entailment.KD45 (Logic.KD45) where


protected abbrev Hilbert.KB4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.KB4 := Hilbert.KB4.logic
instance : (Hilbert.KB4).HasK where p := 0; q := 1;
instance : (Hilbert.KB4).HasB where p := 0
instance : (Hilbert.KB4).HasFour where p := 0
instance : Entailment.KB4 (Logic.KB4) where


protected abbrev Hilbert.KB5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.KB5 := Hilbert.KB5.logic
instance : (Hilbert.KB5).HasK where p := 0; q := 1;
instance : (Hilbert.KB5).HasB where p := 0
instance : (Hilbert.KB5).HasFive where p := 0
instance : Entailment.KB5 (Logic.KB5) where


protected abbrev Hilbert.S4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.S4 := Hilbert.S4.logic
instance : (Hilbert.S4).HasK where p := 0; q := 1;
instance : (Hilbert.S4).HasT where p := 0
instance : (Hilbert.S4).HasFour where p := 0
instance : Entailment.S4 (Logic.S4) where
instance : Logic.K4 ⪯ Logic.S4 := weakerThan_of_subset_axioms $ by simp;


protected abbrev Hilbert.S4McK : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0)}⟩
protected abbrev Logic.S4McK := Hilbert.S4McK.logic
instance : (Hilbert.S4McK).HasK where p := 0; q := 1;
instance : (Hilbert.S4McK).HasT where p := 0
instance : (Hilbert.S4McK).HasFour where p := 0
instance : (Hilbert.S4McK).HasMcK where p := 0
instance : Entailment.S4McK (Logic.S4McK) where
instance : Logic.K4McK ⪯ Logic.S4McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.S4Point2McK : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev Logic.S4Point2McK := Hilbert.S4Point2McK.logic
instance : (Hilbert.S4Point2McK).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point2McK).HasT where p := 0
instance : (Hilbert.S4Point2McK).HasFour where p := 0
instance : (Hilbert.S4Point2McK).HasMcK where p := 0
instance : (Hilbert.S4Point2McK).HasPoint2 where p := 0
instance : Entailment.S4Point2McK (Logic.S4Point2McK) where
instance : Logic.K4McK ⪯ Logic.S4Point2McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.S4Point3McK : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.S4Point3McK := Hilbert.S4Point3McK.logic
instance : (Hilbert.S4Point3McK).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point3McK).HasT where p := 0
instance : (Hilbert.S4Point3McK).HasFour where p := 0
instance : (Hilbert.S4Point3McK).HasMcK where p := 0
instance : (Hilbert.S4Point3McK).HasPoint3 where p := 0; q := 1;
instance : Entailment.S4Point3McK (Logic.S4Point3McK) where
instance : Logic.K4McK ⪯ Logic.S4Point3McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.S4Point4McK : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.McK (.atom 0), Axioms.Point4 (.atom 0)}⟩
protected abbrev Logic.S4Point4McK := Hilbert.S4Point4McK.logic
instance : (Hilbert.S4Point4McK).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point4McK).HasT where p := 0
instance : (Hilbert.S4Point4McK).HasFour where p := 0
instance : (Hilbert.S4Point4McK).HasMcK where p := 0
instance : (Hilbert.S4Point4McK).HasPoint4 where p := 0
instance : Entailment.S4Point4McK (Logic.S4Point4McK) where
instance : Logic.K4McK ⪯ Logic.S4Point4McK := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.S4Point2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev Logic.S4Point2 := Hilbert.S4Point2.logic
instance : (Hilbert.S4Point2).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point2).HasT where p := 0
instance : (Hilbert.S4Point2).HasFour where p := 0
instance : (Hilbert.S4Point2).HasPoint2 where p := 0
instance : Entailment.S4Point2 (Logic.S4Point2) where


protected abbrev Hilbert.S4Point3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.S4Point3 := Hilbert.S4Point3.logic
instance : (Hilbert.S4Point3).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point3).HasT where p := 0
instance : (Hilbert.S4Point3).HasFour where p := 0
instance : (Hilbert.S4Point3).HasPoint3 where p := 0; q := 1;
instance : Entailment.S4Point3 (Logic.S4Point3) where


protected abbrev Hilbert.S4Point4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point4 (.atom 0)}⟩
protected abbrev Logic.S4Point4 := Hilbert.S4Point4.logic
instance : (Hilbert.S4Point4).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point4).HasT where p := 0
instance : (Hilbert.S4Point4).HasFour where p := 0
instance : (Hilbert.S4Point4).HasPoint4 where p := 0
instance : Entailment.S4Point4 (Logic.S4Point4) where


protected abbrev Hilbert.K5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.K5 := Hilbert.K5.logic
instance : (Hilbert.K5).HasK where p := 0; q := 1;
instance : (Hilbert.K5).HasFive where p := 0
instance : Entailment.K5 (Logic.K5) where


protected abbrev Hilbert.S5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.S5 := Hilbert.S5.logic
instance : (Hilbert.S5).HasK where p := 0; q := 1;
instance : (Hilbert.S5).HasT where p := 0
instance : (Hilbert.S5).HasFive where p := 0
instance : Entailment.S5 (Logic.S5) where


protected abbrev Hilbert.GL : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}⟩
protected abbrev Logic.GL := Hilbert.GL.logic
instance : (Hilbert.GL).HasK where p := 0; q := 1;
instance : (Hilbert.GL).HasL where p := 0;
instance : Entailment.GL (Logic.GL) where


protected abbrev Hilbert.GLPoint2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.GLPoint2 := Hilbert.GLPoint2.logic
instance : (Hilbert.GLPoint2).HasK where p := 0; q := 1;
instance : (Hilbert.GLPoint2).HasL where p := 0
instance : (Hilbert.GLPoint2).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.GLPoint2 (Logic.GLPoint2) where
instance : Logic.GL ⪯ Logic.GLPoint2 := weakerThan_of_subset_axioms $ by simp


protected abbrev Hilbert.GLPoint3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.GLPoint3 := Hilbert.GLPoint3.logic
instance : (Hilbert.GLPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.GLPoint3).HasL where p := 0
instance : (Hilbert.GLPoint3).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.GLPoint3 (Logic.GLPoint3) where


protected abbrev Hilbert.K4Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0)}⟩
protected abbrev Logic.K4Z := Hilbert.K4Z.logic
instance : (Hilbert.K4Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Z).HasFour where p := 0
instance : (Hilbert.K4Z).HasZ where p := 0
instance : Entailment.K4Z (Logic.K4Z) where
instance : Logic.K4 ⪯ Logic.K4Z := weakerThan_of_subset_axioms $ by simp
instance : Logic.K4Z ⪯ Logic.GL := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.K4Point2Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K4Point2Z := Hilbert.K4Point2Z.logic
instance : (Hilbert.K4Point2Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point2Z).HasFour where p := 0
instance : (Hilbert.K4Point2Z).HasZ where p := 0
instance : (Hilbert.K4Point2Z).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.K4Point2Z (Logic.K4Point2Z) where
instance : Logic.K4Point2 ⪯ Logic.K4Point2Z := weakerThan_of_subset_axioms (by simp)
instance : Logic.K4Z ⪯ Logic.K4Point2Z := weakerThan_of_subset_axioms (by simp)
instance : Logic.K4Point2Z ⪯ Logic.GLPoint2 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.K4Point3Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K4Point3Z := Hilbert.K4Point3Z.logic
instance : (Hilbert.K4Point3Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point3Z).HasFour where p := 0
instance : (Hilbert.K4Point3Z).HasZ where p := 0
instance : (Hilbert.K4Point3Z).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.K4Point3Z (Logic.K4Point3Z) where
instance : Logic.K4Point3 ⪯ Logic.K4Point3Z := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Logic.K4Z ⪯ Logic.K4Point3Z := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Logic.K4Point3Z ⪯ Logic.GLPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.KHen : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Hen (.atom 0)}⟩
protected abbrev Logic.KHen := Hilbert.KHen.logic
instance : (Hilbert.KHen).HasK where p := 0; q := 1;
instance : (Hilbert.KHen).HasHen where p := 0;


protected abbrev Hilbert.Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}⟩
protected abbrev Logic.Grz := Hilbert.Grz.logic
instance : (Hilbert.Grz).HasK where p := 0; q := 1;
instance : (Hilbert.Grz).HasGrz where p := 0
instance : Entailment.Grz (Logic.Grz) where
instance : Logic.KT ⪯ Logic.Grz := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl) <;> simp;


protected abbrev Hilbert.GrzPoint2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev Logic.GrzPoint2 := Hilbert.GrzPoint2.logic
instance : (Hilbert.GrzPoint2).HasK where p := 0; q := 1;
instance : (Hilbert.GrzPoint2).HasGrz where p := 0
instance : (Hilbert.GrzPoint2).HasPoint2 where p := 0
instance : Entailment.GrzPoint2 (Logic.GrzPoint2) where


protected abbrev Hilbert.GrzPoint3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.GrzPoint3 := Hilbert.GrzPoint3.logic
instance : (Hilbert.GrzPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.GrzPoint3).HasGrz where p := 0
instance : (Hilbert.GrzPoint3).HasPoint3 where p := 0; q := 1;
instance : Entailment.GrzPoint3 (Logic.GrzPoint3) where


protected abbrev Hilbert.Dum : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0)}⟩
protected abbrev Logic.Dum := Hilbert.Dum.logic
instance : (Hilbert.Dum).HasK where p := 0; q := 1;
instance : (Hilbert.Dum).HasT where p := 0
instance : (Hilbert.Dum).HasFour where p := 0
instance : (Hilbert.Dum).HasDum where p := 0
instance : Entailment.Dum (Logic.Dum) where
instance : Logic.S4 ⪯ Logic.Dum := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl) <;> simp;
instance : Logic.Dum ⪯ Logic.Grz := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.DumPoint2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev Logic.DumPoint2 := Hilbert.DumPoint2.logic
instance : (Hilbert.DumPoint2).HasK where p := 0; q := 1;
instance : (Hilbert.DumPoint2).HasT where p := 0
instance : (Hilbert.DumPoint2).HasFour where p := 0
instance : (Hilbert.DumPoint2).HasDum where p := 0
instance : (Hilbert.DumPoint2).HasPoint2 where p := 0
instance : Entailment.DumPoint2 (Logic.DumPoint2) where
instance : Logic.Dum ⪯ Logic.DumPoint2 := weakerThan_of_subset_axioms (by simp)
instance : Logic.S4Point2 ⪯ Logic.DumPoint2 := weakerThan_of_subset_axioms (by simp)
instance : Logic.DumPoint2 ⪯ Logic.GrzPoint2 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.DumPoint3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.DumPoint3 := Hilbert.DumPoint3.logic
instance : (Hilbert.DumPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.DumPoint3).HasT where p := 0
instance : (Hilbert.DumPoint3).HasFour where p := 0
instance : (Hilbert.DumPoint3).HasDum where p := 0
instance : (Hilbert.DumPoint3).HasPoint3 where p := 0; q := 1;
instance : Entailment.DumPoint3 (Logic.DumPoint3) where
instance : Logic.Dum ⪯ Logic.DumPoint3 := weakerThan_of_subset_axioms (by simp)
instance : Logic.S4Point3 ⪯ Logic.DumPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;
instance : Logic.DumPoint3 ⪯ Logic.GrzPoint3 := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl | rfl | rfl | rfl) <;> simp;


protected abbrev Hilbert.KTc : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Tc (.atom 0)}⟩
protected abbrev Logic.KTc := Hilbert.KTc.logic
instance : (Hilbert.KTc).HasK where p := 0; q := 1;
instance : (Hilbert.KTc).HasTc where p := 0
instance : Entailment.KTc (Logic.KTc) where


protected abbrev Hilbert.KD4Point3Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1), Axioms.Z (.atom 0)}⟩
protected abbrev Logic.KD4Point3Z := Hilbert.KD4Point3Z.logic
instance : (Hilbert.KD4Point3Z).HasK where p := 0; q := 1;
instance : (Hilbert.KD4Point3Z).HasD where p := 0
instance : (Hilbert.KD4Point3Z).HasFour where p := 0
instance : (Hilbert.KD4Point3Z).HasWeakPoint3 where p := 0; q := 1;
instance : (Hilbert.KD4Point3Z).HasZ where p := 0
instance : Entailment.KD4Point3Z (Logic.KD4Point3Z) where


protected abbrev Hilbert.KTMk : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Mk (.atom 0) (.atom 1)}⟩
protected abbrev Logic.KTMk := Hilbert.KTMk.logic
instance : (Hilbert.KTMk).HasK where p := 0; q := 1;
instance : (Hilbert.KTMk).HasT where p := 0
instance : (Hilbert.KTMk).HasMk where p := 0; q := 1
instance : Entailment.KTMk (Logic.KTMk) where


protected abbrev Hilbert.N : Hilbert ℕ := ⟨{}⟩
protected abbrev Logic.N := Hilbert.N.logic


protected abbrev Hilbert.Ver : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}⟩
protected abbrev Logic.Ver := Hilbert.Ver.logic
instance : (Hilbert.Ver).HasK where p := 0; q := 1;
instance : (Hilbert.Ver).HasVer where p := 0
instance : Entailment.Ver (Logic.Ver) where



protected abbrev Hilbert.Triv : Hilbert ℕ := ⟨{ Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}⟩
protected abbrev Logic.Triv := Hilbert.Triv.logic
instance : (Hilbert.Triv).HasK where p := 0; q := 1;
instance : (Hilbert.Triv).HasT where p := 0
instance : (Hilbert.Triv).HasTc where p := 0
instance : Entailment.Triv (Logic.Triv) where
instance : Logic.K4 ⪯ Logic.Triv := weakerThan_of_provable_axioms $ by rintro φ (rfl | rfl) <;> simp;


end LO.Modal
