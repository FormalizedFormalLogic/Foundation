import Foundation.Modal.Hilbert.K
import Foundation.Modal.Entailment.Grz

namespace LO.Modal

open Entailment

namespace Hilbert

section

open Deduction

variable {H : Hilbert α}
variable [DecidableEq α]


class HasT (H : Hilbert α) where
  p : α
  mem_T : Axioms.T (.atom p) ∈ H.axioms := by tauto;

instance [hT : H.HasT] : Entailment.HasAxiomT H where
  T φ := by
    apply maxm;
    use Axioms.T (.atom hT.p);
    constructor;
    . exact hT.mem_T;
    . use (λ b => if hT.p = b then φ else (.atom b));
      simp;

class HasB (H : Hilbert α) where
  p : α
  mem_B : Axioms.B (.atom p) ∈ H.axioms := by tauto;

instance [hB : H.HasB] : Entailment.HasAxiomB H where
  B φ := by
    apply maxm;
    use Axioms.B (.atom hB.p);
    constructor;
    . exact hB.mem_B;
    . use (λ b => if hB.p = b then φ else (.atom b));
      simp;

class HasD (H : Hilbert α) where
  p : α
  mem_D : Axioms.D (.atom p) ∈ H.axioms := by tauto;

instance [hD : H.HasD] : Entailment.HasAxiomD H where
  D φ := by
    apply maxm;
    use Axioms.D (.atom hD.p);
    constructor;
    . exact hD.mem_D;
    . use (λ b => if hD.p = b then φ else (.atom b));
      simp;


class HasFour (H : Hilbert α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [hFour : H.HasFour] : Entailment.HasAxiomFour H where
  Four φ := by
    apply maxm;
    use Axioms.Four (.atom hFour.p);
    constructor;
    . exact hFour.mem_Four;
    . use (λ b => if hFour.p = b then φ else (.atom b));
      simp;


class HasFive (H : Hilbert α) where
  p : α
  mem_Five : Axioms.Five (.atom p) ∈ H.axioms := by tauto;

instance [hFive : H.HasFive] : Entailment.HasAxiomFive H where
  Five φ := by
    apply maxm;
    use Axioms.Five (.atom hFive.p);
    constructor;
    . exact hFive.mem_Five;
    . use (λ b => if hFive.p = b then φ else (.atom b));
      simp;


class HasPoint2 (H : Hilbert α) where
  p : α
  mem_Point2 : Axioms.Point2 (.atom p) ∈ H.axioms := by tauto;

instance [hPoint2 : H.HasPoint2] : Entailment.HasAxiomPoint2 H where
  Point2 φ := by
    apply maxm;
    use Axioms.Point2 (.atom hPoint2.p);
    constructor;
    . exact hPoint2.mem_Point2;
    . use (λ b => if hPoint2.p = b then φ else (.atom b));
      simp;


class HasWeakPoint2 (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_WeakPoint2 : Axioms.WeakPoint2 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [hDotWeak2 : H.HasWeakPoint2] : Entailment.HasAxiomWeakPoint2 H where
  WeakPoint2 φ ψ := by
    apply maxm;
    use Axioms.WeakPoint2 (.atom hDotWeak2.p) (.atom hDotWeak2.q);
    constructor;
    . exact hDotWeak2.mem_WeakPoint2;
    . use (λ b => if hDotWeak2.p = b then φ else if hDotWeak2.q = b then ψ else (.atom b));
      simp [hDotWeak2.ne_pq];


class HasPoint3 (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Point3 : Axioms.Point3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [hPoint3 : H.HasPoint3] : Entailment.HasAxiomPoint3 H where
  Point3 φ ψ := by
    apply maxm;
    use Axioms.Point3 (.atom hPoint3.p) (.atom hPoint3.q);
    constructor;
    . exact hPoint3.mem_Point3;
    . use (λ b => if hPoint3.p = b then φ else if hPoint3.q = b then ψ else (.atom b));
      simp [hPoint3.ne_pq];


class HasWeakPoint3 (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_WeakPoint3 : Axioms.WeakPoint3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [hDotWeak3 : H.HasWeakPoint3] : Entailment.HasAxiomWeakPoint3 H where
  WeakPoint3 φ ψ := by
    apply maxm;
    use Axioms.WeakPoint3 (.atom hDotWeak3.p) (.atom hDotWeak3.q);
    constructor;
    . exact hDotWeak3.mem_WeakPoint3;
    . use (λ b => if hDotWeak3.p = b then φ else if hDotWeak3.q = b then ψ else (.atom b));
      simp [hDotWeak3.ne_pq];


class HasL (H : Hilbert α) where
  p : α
  mem_L : Axioms.L (.atom p) ∈ H.axioms := by tauto;

instance [hL : H.HasL] : Entailment.HasAxiomL H where
  L φ := by
    apply maxm;
    use Axioms.L (.atom hL.p);
    constructor;
    . exact hL.mem_L;
    . use (λ b => if hL.p = b then φ else (.atom b));
      simp;


class HasGrz (H : Hilbert α) where
  p : α
  mem_Grz : Axioms.Grz (.atom p) ∈ H.axioms := by tauto;

instance [hGrz : H.HasGrz] : Entailment.HasAxiomGrz H where
  Grz φ := by
    apply maxm;
    use Axioms.Grz (.atom hGrz.p);
    constructor;
    . exact hGrz.mem_Grz;
    . use (λ b => if hGrz.p = b then φ else (.atom b));
      simp;


class HasTc (H : Hilbert α) where
  p : α
  mem_Tc : Axioms.Tc (.atom p) ∈ H.axioms := by tauto;

instance [hTc : H.HasTc] : Entailment.HasAxiomTc H where
  Tc φ := by
    apply maxm;
    use Axioms.Tc (.atom hTc.p);
    constructor;
    . exact hTc.mem_Tc;
    . use (λ b => if hTc.p = b then φ else (.atom b));
      simp;


class HasVer (H : Hilbert α) where
  p : α
  mem_Ver : Axioms.Ver (.atom p) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hVer : H.HasVer] : Entailment.HasAxiomVer H where
  Ver φ := by
    apply maxm;
    use Axioms.Ver (.atom hVer.p);
    constructor;
    . exact hVer.mem_Ver;
    . use (λ b => if hVer.p = b then φ else (.atom b));
      simp;


class HasH (H : Hilbert α) where
  p : α
  mem_H : Axioms.H (.atom p) ∈ H.axioms := by tauto;

instance [hH : H.HasH] : Entailment.HasAxiomH H where
  H φ := by
    apply maxm;
    use Axioms.H (.atom hH.p);
    constructor;
    . exact hH.mem_H;
    . use (λ b => if hH.p = b then φ else (.atom b));
      simp;


class HasZ (H : Hilbert α) where
  p : α
  mem_Z : Axioms.Z (.atom p) ∈ H.axioms := by tauto;

instance [hZ : H.HasZ] : Entailment.HasAxiomZ H where
  Z φ := by
    apply maxm;
    use Axioms.Z (.atom hZ.p);
    constructor;
    . exact hZ.mem_Z;
    . use (λ b => if hZ.p = b then φ else (.atom b));
      simp;

class HasM (H : Hilbert α) where
  p : α
  mem_M : Axioms.M (.atom p) ∈ H.axioms := by tauto;

instance [hM : H.HasM] : Entailment.HasAxiomM H where
  M φ := by
    apply maxm;
    use Axioms.M (.atom hM.p);
    constructor;
    . exact hM.mem_M;
    . use (λ b => if hM.p = b then φ else (.atom b));
      simp;

class HasMk (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Mk : Axioms.Modal.Mk (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasMk] : Entailment.Modal.HasAxiomMk H where
  Mk φ ψ := by
    apply maxm;
    use Axioms.Modal.Mk (.atom $ HasMk.p H) (.atom $ HasMk.q H);
    constructor;
    . exact HasMk.mem_Mk;
    . use (λ b => if b = (HasMk.q H) then ψ else if b = (HasMk.p H) then φ else (.atom b));
      simp [HasMk.ne_pq];

end

protected abbrev KT : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0)}⟩
instance : (Hilbert.KT).HasK where p := 0; q := 1;
instance : (Hilbert.KT).HasT where p := 0
instance : Entailment.Modal.KT (Hilbert.KT) where


protected abbrev KD : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0)}⟩
instance : (Hilbert.KD).HasK where p := 0; q := 1;
instance : (Hilbert.KD).HasD where p := 0
instance : Entailment.Modal.KD (Hilbert.KD) where


protected abbrev KB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0)}⟩
instance : (Hilbert.KB).HasK where p := 0; q := 1;
instance : (Hilbert.KB).HasB where p := 0
instance : Entailment.Modal.KB (Hilbert.KB) where


protected abbrev KDB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.B (.atom 0)}⟩
instance : (Hilbert.KDB).HasK where p := 0; q := 1;
instance : (Hilbert.KDB).HasD where p := 0
instance : (Hilbert.KDB).HasB where p := 0
instance : Entailment.Modal.KDB (Hilbert.KDB) where


protected abbrev KTB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.B (.atom 0)}⟩
instance : (Hilbert.KTB).HasK where p := 0; q := 1;
instance : (Hilbert.KTB).HasT where p := 0
instance : (Hilbert.KTB).HasB where p := 0
instance : Entailment.Modal.KTB (Hilbert.KTB) where

protected abbrev KM : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.M (.atom 0)}⟩
instance : (Hilbert.KM).HasK where p := 0; q := 1;
instance : (Hilbert.KM).HasM where p := 0
instance : Entailment.Modal.KM (Hilbert.KM) where

instance K_weakerThan_KM : Hilbert.K ⪯ Hilbert.KM := weakerThan_of_dominate_axioms $ by simp;

protected abbrev K4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.K4).HasK where p := 0; q := 1;
instance : (Hilbert.K4).HasFour where p := 0
instance : Entailment.Modal.K4 (Hilbert.K4) where

protected abbrev K4Point1 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.M (.atom 0)}⟩
instance : (Hilbert.K4Point1).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point1).HasFour where p := 0
instance : (Hilbert.K4Point1).HasM where p := 0
instance : Entailment.Modal.K4Point1 (Hilbert.K4Point1) where

instance K_weakerThan_K4Point1 : Hilbert.K ⪯ Hilbert.K4Point1 := weakerThan_of_dominate_axioms $ by simp;

noncomputable instance {H : Hilbert _} [Hilbert.K4Point1 ⪯ H] : Entailment.Modal.K4Point1 H where
  K _ _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4Point1) (by simp) |>.some
  Four _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4Point1) (by simp) |>.some
  M _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4Point1) (by simp) |>.some

protected abbrev K4Point2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
instance : (Hilbert.K4Point2).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point2).HasFour where p := 0
instance : (Hilbert.K4Point2).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.Modal.K4Point2 (Hilbert.K4Point2) where

protected abbrev K4Point3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
instance : (Hilbert.K4Point3).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point3).HasFour where p := 0
instance : (Hilbert.K4Point3).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.Modal.K4Point3 (Hilbert.K4Point3) where

protected abbrev KT4B : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.B (.atom 0)}⟩
instance : (Hilbert.KT4B).HasK where p := 0; q := 1;
instance : (Hilbert.KT4B).HasT where p := 0
instance : (Hilbert.KT4B).HasFour where p := 0
instance : (Hilbert.KT4B).HasB where p := 0
instance : Entailment.Modal.KT4B (Hilbert.KT4B) where

protected abbrev K45 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.K45).HasK where p := 0; q := 1;
instance : (Hilbert.K45).HasFour where p := 0
instance : (Hilbert.K45).HasFive where p := 0
instance : Entailment.Modal.K45 (Hilbert.K45) where


protected abbrev KD4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.KD4).HasK where p := 0; q := 1;
instance : (Hilbert.KD4).HasD where p := 0
instance : (Hilbert.KD4).HasFour where p := 0
instance : Entailment.Modal.KD4 (Hilbert.KD4) where


protected abbrev KD5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.KD5).HasK where p := 0; q := 1;
instance : (Hilbert.KD5).HasD where p := 0
instance : (Hilbert.KD5).HasFive where p := 0
instance : Entailment.Modal.KD5 (Hilbert.KD5) where


protected abbrev KD45 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.KD45).HasK where p := 0; q := 1;
instance : (Hilbert.KD45).HasD where p := 0
instance : (Hilbert.KD45).HasFour where p := 0
instance : (Hilbert.KD45).HasFive where p := 0
instance : Entailment.Modal.KD45 (Hilbert.KD45) where


protected abbrev KB4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.KB4).HasK where p := 0; q := 1;
instance : (Hilbert.KB4).HasB where p := 0
instance : (Hilbert.KB4).HasFour where p := 0
instance : Entailment.Modal.KB4 (Hilbert.KB4) where


protected abbrev KB5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.KB5).HasK where p := 0; q := 1;
instance : (Hilbert.KB5).HasB where p := 0
instance : (Hilbert.KB5).HasFive where p := 0
instance : Entailment.Modal.KB5 (Hilbert.KB5) where


protected abbrev S4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.S4).HasK where p := 0; q := 1;
instance : (Hilbert.S4).HasT where p := 0
instance : (Hilbert.S4).HasFour where p := 0
instance : Entailment.Modal.S4 (Hilbert.S4) where

instance K4_weakerThan_S4 : Hilbert.K4 ⪯ Hilbert.S4 := weakerThan_of_dominate_axioms $ by simp;

protected abbrev S4Point1 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.M (.atom 0)}⟩
instance : (Hilbert.S4Point1).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point1).HasT where p := 0
instance : (Hilbert.S4Point1).HasFour where p := 0
instance : (Hilbert.S4Point1).HasM where p := 0
instance : Entailment.Modal.S4Point1 (Hilbert.S4Point1) where

instance K4Point1_weakerThan_S4Point1 : Hilbert.K4Point1 ⪯ Hilbert.S4Point1 := weakerThan_of_dominate_axioms $ by simp;

protected abbrev S4Point2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point2 (.atom 0)}⟩
instance : (Hilbert.S4Point2).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point2).HasT where p := 0
instance : (Hilbert.S4Point2).HasFour where p := 0
instance : (Hilbert.S4Point2).HasPoint2 where p := 0
instance : Entailment.Modal.S4Point2 (Hilbert.S4Point2) where


protected abbrev S4Point3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
instance : (Hilbert.S4Point3).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point3).HasT where p := 0
instance : (Hilbert.S4Point3).HasFour where p := 0
instance : (Hilbert.S4Point3).HasPoint3 where p := 0; q := 1;
instance : Entailment.Modal.S4Point3 (Hilbert.S4Point3) where


protected abbrev K5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.K5).HasK where p := 0; q := 1;
instance : (Hilbert.K5).HasFive where p := 0
instance : Entailment.Modal.K5 (Hilbert.K5) where


protected abbrev S5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.S5).HasK where p := 0; q := 1;
instance : (Hilbert.S5).HasT where p := 0
instance : (Hilbert.S5).HasFive where p := 0
instance : Entailment.Modal.S5 (Hilbert.S5) where


protected abbrev GL : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}⟩
instance : (Hilbert.GL).HasK where p := 0; q := 1;
instance : (Hilbert.GL).HasL where p := 0
instance : Entailment.Modal.GL (Hilbert.GL) where

protected abbrev GLPoint3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
instance : (Hilbert.GLPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.GLPoint3).HasL where p := 0
instance : (Hilbert.GLPoint3).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.Modal.GLPoint3 (Hilbert.GLPoint3) where

protected abbrev KH : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.H (.atom 0)}⟩
instance : (Hilbert.KH).HasK where p := 0; q := 1;
instance : (Hilbert.KH).HasH where p := 0

protected abbrev Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}⟩
instance : (Hilbert.Grz).HasK where p := 0; q := 1;
instance : (Hilbert.Grz).HasGrz where p := 0
instance : Entailment.Modal.Grz (Hilbert.Grz) where

protected abbrev GrzPoint2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point2 (.atom 0)}⟩
instance : (Hilbert.GrzPoint2).HasK where p := 0; q := 1;
instance : (Hilbert.GrzPoint2).HasGrz where p := 0
instance : (Hilbert.GrzPoint2).HasPoint2 where p := 0
instance : Entailment.Modal.Grz (Hilbert.GrzPoint2) where

protected abbrev GrzPoint3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
instance : (Hilbert.GrzPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.GrzPoint3).HasGrz where p := 0
instance : (Hilbert.GrzPoint3).HasPoint3 where p := 0; q := 1;
instance : Entailment.Modal.Grz (Hilbert.GrzPoint3) where

lemma KT_weakerThan_Grz : Hilbert.KT ⪯ Hilbert.Grz := weakerThan_of_dominate_axioms $ by simp;


protected abbrev Ver : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}⟩
instance : (Hilbert.Ver).HasK where p := 0; q := 1;
instance : (Hilbert.Ver).HasVer where p := 0
instance : Entailment.Modal.Ver (Hilbert.Ver) where


protected abbrev Triv : Hilbert ℕ := ⟨{ Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}⟩
instance : (Hilbert.Triv).HasK where p := 0; q := 1;
instance : (Hilbert.Triv).HasT where p := 0
instance : (Hilbert.Triv).HasTc where p := 0
instance : Entailment.Modal.Triv (Hilbert.Triv) where

lemma K4_weakerThan_Triv : Hilbert.K4 ⪯ Hilbert.Triv := weakerThan_of_dominate_axioms $ by simp;


protected abbrev KTc : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Tc (.atom 0)}⟩
instance : (Hilbert.KTc).HasK where p := 0; q := 1;
instance : (Hilbert.KTc).HasTc where p := 0
instance : Entailment.Modal.KTc (Hilbert.KTc) where

protected abbrev KD4Point3Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1), Axioms.Z (.atom 0)}⟩
instance : (Hilbert.KD4Point3Z).HasK where p := 0; q := 1;
instance : (Hilbert.KD4Point3Z).HasD where p := 0
instance : (Hilbert.KD4Point3Z).HasFour where p := 0
instance : (Hilbert.KD4Point3Z).HasWeakPoint3 where p := 0; q := 1;
instance : (Hilbert.KD4Point3Z).HasZ where p := 0
instance : Entailment.Modal.KD4Point3Z (Hilbert.KD4Point3Z) where

protected abbrev KTMk : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Modal.Mk (.atom 0) (.atom 1)}⟩
instance : (Hilbert.KTMk).HasK where p := 0; q := 1;
instance : (Hilbert.KTMk).HasT where p := 0
instance : (Hilbert.KTMk).HasMk where p := 0; q := 1
instance : Entailment.Modal.KTMk (Hilbert.KTMk) where

protected abbrev N : Hilbert ℕ := ⟨{}⟩

end Hilbert

end LO.Modal
