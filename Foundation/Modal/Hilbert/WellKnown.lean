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


class HasPoint4 (H : Hilbert α) where
  p : α
  mem_Point4 : Axioms.Point4 (.atom p) ∈ H.axioms := by tauto;

instance [H.HasPoint4] : Entailment.HasAxiomPoint4 H where
  Point4 φ := by
    apply maxm;
    use Axioms.Point4 (.atom $ HasPoint4.p H);
    constructor;
    . exact HasPoint4.mem_Point4;
    . use (λ b => if b = (HasPoint4.p H) then φ else (.atom b));
      simp;


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


class HasDum (H : Hilbert α) where
  p : α
  mem_Dum : Axioms.Dum (.atom p) ∈ H.axioms := by tauto;

instance [H.HasDum] : Entailment.HasAxiomDum H where
  Dum φ := by
    apply maxm;
    use Axioms.Dum (.atom $ HasDum.p H);
    constructor;
    . exact HasDum.mem_Dum;
    . use (λ b => if b = (HasDum.p H) then φ else (.atom b));
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
  mem_Mk : Axioms.Mk (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasMk] : Entailment.HasAxiomMk H where
  Mk φ ψ := by
    apply maxm;
    use Axioms.Mk (.atom $ HasMk.p H) (.atom $ HasMk.q H);
    constructor;
    . exact HasMk.mem_Mk;
    . use (λ b => if b = (HasMk.q H) then ψ else if b = (HasMk.p H) then φ else (.atom b));
      simp [HasMk.ne_pq];

class HasGeach (g) (H : Hilbert α) where
  p : α
  mem_Geach : Axioms.Geach g (.atom p) ∈ H.axioms := by tauto;

instance [H.HasGeach g] : Entailment.HasAxiomGeach g H where
  Geach φ := by
    apply maxm;
    use Axioms.Geach g (.atom (HasGeach.p g H));
    constructor;
    . exact HasGeach.mem_Geach;
    . use (λ b => if HasGeach.p g H = b then φ else (.atom b));
      simp;

end Hilbert


protected abbrev Hilbert.KT : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0)}⟩
protected abbrev Logic.KT := Hilbert.KT.logic

namespace Hilbert.KT

instance : (Hilbert.KT).HasK where p := 0; q := 1;
instance : (Hilbert.KT).HasT where p := 0
instance : Entailment.KT (Hilbert.KT) where

end Hilbert.KT


protected abbrev Hilbert.KD : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0)}⟩
protected abbrev Logic.KD := Hilbert.KD.logic

namespace Hilbert.KD

instance : (Hilbert.KD).HasK where p := 0; q := 1;
instance : (Hilbert.KD).HasD where p := 0
instance : Entailment.KD (Hilbert.KD) where

end Hilbert.KD


protected abbrev Hilbert.KB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0)}⟩
protected abbrev Logic.KB := Hilbert.KB.logic

namespace Hilbert.KB

instance : (Hilbert.KB).HasK where p := 0; q := 1;
instance : (Hilbert.KB).HasB where p := 0
instance : Entailment.KB (Hilbert.KB) where

end Hilbert.KB


protected abbrev Hilbert.KDB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev Logic.KDB := Hilbert.KDB.logic

namespace Hilbert.KDB

instance : (Hilbert.KDB).HasK where p := 0; q := 1;
instance : (Hilbert.KDB).HasD where p := 0
instance : (Hilbert.KDB).HasB where p := 0
instance : Entailment.KDB (Hilbert.KDB) where

end Hilbert.KDB


protected abbrev Hilbert.KTB : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev Logic.KTB := Hilbert.KTB.logic

namespace Hilbert.KTB

instance : (Hilbert.KTB).HasK where p := 0; q := 1;
instance : (Hilbert.KTB).HasT where p := 0
instance : (Hilbert.KTB).HasB where p := 0
instance : Entailment.KTB (Hilbert.KTB) where

end Hilbert.KTB


protected abbrev Hilbert.KM : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.M (.atom 0)}⟩
protected abbrev Logic.KM := Hilbert.KM.logic

namespace Hilbert.KM

instance : (Hilbert.KM).HasK where p := 0; q := 1;
instance : (Hilbert.KM).HasM where p := 0
instance : Entailment.KM (Hilbert.KM) where

end Hilbert.KM

instance Hilbert.K_weakerThan_KM : Hilbert.K ⪯ Hilbert.KM := weakerThan_of_dominate_axioms $ by simp;


protected abbrev Hilbert.K4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.K4 := Hilbert.K4.logic

namespace Hilbert.K4

instance : (Hilbert.K4).HasK where p := 0; q := 1;
instance : (Hilbert.K4).HasFour where p := 0
instance : Entailment.K4 (Hilbert.K4) where

end Hilbert.K4



protected abbrev Hilbert.K4M : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.M (.atom 0)}⟩
protected abbrev Logic.K4M := Hilbert.K4M.logic

namespace Hilbert.K4M

instance : (Hilbert.K4M).HasK where p := 0; q := 1;
instance : (Hilbert.K4M).HasFour where p := 0
instance : (Hilbert.K4M).HasM where p := 0
instance : Entailment.K4M (Hilbert.K4M) where

noncomputable instance {H : Hilbert _} [Hilbert.K4M ⪯ H] : Entailment.K4M H where
  K _ _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4M) (by simp) |>.some
  Four _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4M) (by simp) |>.some
  M _ := Entailment.WeakerThan.pbl (𝓢 := Hilbert.K4M) (by simp) |>.some

end Hilbert.K4M

instance Hilbert.K_weakerThan_K4M : Hilbert.K ⪯ Hilbert.K4M := weakerThan_of_dominate_axioms $ by simp;


protected abbrev Hilbert.K4Point2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K4Point2 := Hilbert.K4Point2.logic

namespace Hilbert.K4Point2

instance : (Hilbert.K4Point2).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point2).HasFour where p := 0
instance : (Hilbert.K4Point2).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.K4Point2 (Hilbert.K4Point2) where

end Hilbert.K4Point2


protected abbrev Hilbert.K4Point3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K4Point3 := Hilbert.K4Point3.logic

namespace Hilbert.K4Point3

instance : (Hilbert.K4Point3).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point3).HasFour where p := 0
instance : (Hilbert.K4Point3).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.K4Point3 (Hilbert.K4Point3) where

end Hilbert.K4Point3


protected abbrev Hilbert.KT4B : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.B (.atom 0)}⟩
protected abbrev Logic.KT4B := Hilbert.KT4B.logic

namespace Hilbert.KT4B

instance : (Hilbert.KT4B).HasK where p := 0; q := 1;
instance : (Hilbert.KT4B).HasT where p := 0
instance : (Hilbert.KT4B).HasFour where p := 0
instance : (Hilbert.KT4B).HasB where p := 0
instance : Entailment.KT4B (Hilbert.KT4B) where

end Hilbert.KT4B


protected abbrev Hilbert.K45 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.K45 := Hilbert.K45.logic

namespace Hilbert.K45

instance : (Hilbert.K45).HasK where p := 0; q := 1;
instance : (Hilbert.K45).HasFour where p := 0
instance : (Hilbert.K45).HasFive where p := 0
instance : Entailment.K45 (Hilbert.K45) where

end Hilbert.K45


protected abbrev Hilbert.KD4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.KD4 := Hilbert.KD4.logic

namespace Hilbert.KD4

instance : (Hilbert.KD4).HasK where p := 0; q := 1;
instance : (Hilbert.KD4).HasD where p := 0
instance : (Hilbert.KD4).HasFour where p := 0
instance : Entailment.KD4 (Hilbert.KD4) where

end Hilbert.KD4


protected abbrev Hilbert.KD5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.KD5 := Hilbert.KD5.logic

namespace Hilbert.KD5

instance : (Hilbert.KD5).HasK where p := 0; q := 1;
instance : (Hilbert.KD5).HasD where p := 0
instance : (Hilbert.KD5).HasFive where p := 0
instance : Entailment.KD5 (Hilbert.KD5) where

end Hilbert.KD5


protected abbrev Hilbert.KD45 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.KD45 := Hilbert.KD45.logic

namespace Hilbert.KD45

instance : (Hilbert.KD45).HasK where p := 0; q := 1;
instance : (Hilbert.KD45).HasD where p := 0
instance : (Hilbert.KD45).HasFour where p := 0
instance : (Hilbert.KD45).HasFive where p := 0
instance : Entailment.KD45 (Hilbert.KD45) where

end Hilbert.KD45



protected abbrev Hilbert.KB4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.KB4 := Hilbert.KB4.logic

namespace Hilbert.KB4

instance : (Hilbert.KB4).HasK where p := 0; q := 1;
instance : (Hilbert.KB4).HasB where p := 0
instance : (Hilbert.KB4).HasFour where p := 0
instance : Entailment.KB4 (Hilbert.KB4) where

end Hilbert.KB4


protected abbrev Hilbert.KB5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.B (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.KB5 := Hilbert.KB5.logic

namespace Hilbert.KB5

instance : (Hilbert.KB5).HasK where p := 0; q := 1;
instance : (Hilbert.KB5).HasB where p := 0
instance : (Hilbert.KB5).HasFive where p := 0
instance : Entailment.KB5 (Hilbert.KB5) where

end Hilbert.KB5


protected abbrev Hilbert.S4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}⟩
protected abbrev Logic.S4 := Hilbert.S4.logic

namespace Hilbert.S4

instance : (Hilbert.S4).HasK where p := 0; q := 1;
instance : (Hilbert.S4).HasT where p := 0
instance : (Hilbert.S4).HasFour where p := 0
instance : Entailment.S4 (Hilbert.S4) where

end Hilbert.S4


instance Hilbert.K4_weakerThan_S4 : Hilbert.K4 ⪯ Hilbert.S4 := weakerThan_of_dominate_axioms $ by simp;


protected abbrev Hilbert.SobK1 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.M (.atom 0)}⟩
protected abbrev Logic.SobK1 := Hilbert.SobK1.logic

namespace Hilbert.SobK1

instance : (Hilbert.SobK1).HasK where p := 0; q := 1;
instance : (Hilbert.SobK1).HasT where p := 0
instance : (Hilbert.SobK1).HasFour where p := 0
instance : (Hilbert.SobK1).HasM where p := 0
instance : Entailment.SobK1 (Hilbert.SobK1) where

instance : Hilbert.K4M ⪯ Hilbert.SobK1 := weakerThan_of_dominate_axioms $ by simp;

end Hilbert.SobK1


protected abbrev Hilbert.SobK2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.M (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev Logic.SobK2 := Hilbert.SobK2.logic

namespace Hilbert.SobK2

instance : (Hilbert.SobK2).HasK where p := 0; q := 1;
instance : (Hilbert.SobK2).HasT where p := 0
instance : (Hilbert.SobK2).HasFour where p := 0
instance : (Hilbert.SobK2).HasM where p := 0
instance : (Hilbert.SobK2).HasPoint2 where p := 0
instance : Entailment.SobK2 (Hilbert.SobK2) where

instance : Hilbert.K4M ⪯ Hilbert.SobK2 := weakerThan_of_dominate_axioms $ by simp;

end Hilbert.SobK2


protected abbrev Hilbert.SobK3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.M (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.SobK3 := Hilbert.SobK3.logic

namespace Hilbert.SobK3

instance : (Hilbert.SobK3).HasK where p := 0; q := 1;
instance : (Hilbert.SobK3).HasT where p := 0
instance : (Hilbert.SobK3).HasFour where p := 0
instance : (Hilbert.SobK3).HasM where p := 0
instance : (Hilbert.SobK3).HasPoint3 where p := 0; q := 1;
instance : Entailment.SobK3 (Hilbert.SobK3) where

instance : Hilbert.K4M ⪯ Hilbert.SobK3 := weakerThan_of_dominate_axioms $ by simp;

end Hilbert.SobK3


protected abbrev Hilbert.SobK4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.M (.atom 0), Axioms.Point4 (.atom 0)}⟩
protected abbrev Logic.SobK4 := Hilbert.SobK4.logic

namespace Hilbert.SobK4

instance : (Hilbert.SobK4).HasK where p := 0; q := 1;
instance : (Hilbert.SobK4).HasT where p := 0
instance : (Hilbert.SobK4).HasFour where p := 0
instance : (Hilbert.SobK4).HasM where p := 0
instance : (Hilbert.SobK4).HasPoint4 where p := 0
instance : Entailment.SobK4 (Hilbert.SobK4) where

instance : Hilbert.K4M ⪯ Hilbert.SobK4 := weakerThan_of_dominate_axioms $ by simp;

end Hilbert.SobK4


protected abbrev Hilbert.S4Point2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev Logic.S4Point2 := Hilbert.S4Point2.logic

namespace Hilbert.S4Point2

instance : (Hilbert.S4Point2).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point2).HasT where p := 0
instance : (Hilbert.S4Point2).HasFour where p := 0
instance : (Hilbert.S4Point2).HasPoint2 where p := 0
instance : Entailment.S4Point2 (Hilbert.S4Point2) where

end Hilbert.S4Point2



protected abbrev Hilbert.S4Point3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.S4Point3 := Hilbert.S4Point3.logic

namespace Hilbert.S4Point3

instance : (Hilbert.S4Point3).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point3).HasT where p := 0
instance : (Hilbert.S4Point3).HasFour where p := 0
instance : (Hilbert.S4Point3).HasPoint3 where p := 0; q := 1;
instance : Entailment.S4Point3 (Hilbert.S4Point3) where

end Hilbert.S4Point3


protected abbrev Hilbert.S4Point4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Point4 (.atom 0)}⟩
protected abbrev Logic.S4Point4 := Hilbert.S4Point4.logic

namespace Hilbert.S4Point4

instance : (Hilbert.S4Point4).HasK where p := 0; q := 1;
instance : (Hilbert.S4Point4).HasT where p := 0
instance : (Hilbert.S4Point4).HasFour where p := 0
instance : (Hilbert.S4Point4).HasPoint4 where p := 0
instance : Entailment.S4Point4 (Hilbert.S4Point4) where

end Hilbert.S4Point4


protected abbrev Hilbert.K5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.K5 := Hilbert.K5.logic

namespace Hilbert.K5

instance : (Hilbert.K5).HasK where p := 0; q := 1;
instance : (Hilbert.K5).HasFive where p := 0
instance : Entailment.K5 (Hilbert.K5) where

end Hilbert.K5


protected abbrev Hilbert.S5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}⟩
protected abbrev Logic.S5 := Hilbert.S5.logic
namespace Hilbert.S5

instance : (Hilbert.S5).HasK where p := 0; q := 1;
instance : (Hilbert.S5).HasT where p := 0
instance : (Hilbert.S5).HasFive where p := 0
instance : Entailment.S5 (Hilbert.S5) where

end Hilbert.S5


protected abbrev Hilbert.GL : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}⟩
protected abbrev Logic.GL := Hilbert.GL.logic

namespace Hilbert.GL

instance : (Hilbert.GL).HasK where p := 0; q := 1;
instance : (Hilbert.GL).HasL where p := 0
instance : Entailment.GL (Hilbert.GL) where

end Hilbert.GL


protected abbrev Hilbert.GLPoint2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.GLPoint2 := Hilbert.GLPoint2.logic

namespace Hilbert.GLPoint2

instance : (Hilbert.GLPoint2).HasK where p := 0; q := 1;
instance : (Hilbert.GLPoint2).HasL where p := 0
instance : (Hilbert.GLPoint2).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.GLPoint2 (Hilbert.GLPoint2) where

end Hilbert.GLPoint2

-- TODO: show it is proper
lemma Logic.GLPoint2.is_extension_of_GL : Logic.GL ⊆ Logic.GLPoint2 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset


protected abbrev Hilbert.GLPoint3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.GLPoint3 := Hilbert.GLPoint3.logic

namespace Hilbert.GLPoint3

instance : (Hilbert.GLPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.GLPoint3).HasL where p := 0
instance : (Hilbert.GLPoint3).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.GLPoint3 (Hilbert.GLPoint3) where

end Hilbert.GLPoint3


protected abbrev Hilbert.K4Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0)}⟩
protected abbrev Logic.K4Z := Hilbert.K4Z.logic

namespace Hilbert.K4Z

instance : (Hilbert.K4Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Z).HasFour where p := 0
instance : (Hilbert.K4Z).HasZ where p := 0
instance : Entailment.K4Z (Hilbert.K4Z) where

end Hilbert.K4Z

-- TODO: show it is proper
lemma Logic.K4Z.is_extension_of_K4 : Logic.K4 ⊆ Logic.K4Z := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.GL.is_extension_of_K4Z : Logic.K4Z ⊆ Logic.GL := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset


protected abbrev Hilbert.K4Point2Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0), Axioms.WeakPoint2 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K4Point2Z := Hilbert.K4Point2Z.logic

namespace Hilbert.K4Point2Z

instance : (Hilbert.K4Point2Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point2Z).HasFour where p := 0
instance : (Hilbert.K4Point2Z).HasZ where p := 0
instance : (Hilbert.K4Point2Z).HasWeakPoint2 where p := 0; q := 1;
instance : Entailment.K4Point2Z (Hilbert.K4Point2Z) where

end Hilbert.K4Point2Z

-- TODO: show it is proper
lemma Logic.K4Point2Z.is_extension_of_K4Point2 : Logic.K4Point2 ⊆ Logic.K4Point2Z := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.K4Point2Z.is_extension_of_K4Z : Logic.K4Z ⊆ Logic.K4Point2Z := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.GLPoint2.is_extension_of_K4Point2Z : Logic.K4Point2Z ⊆ Logic.GLPoint2 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset


protected abbrev Hilbert.K4Point3Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.Z (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.K4Point3Z := Hilbert.K4Point3Z.logic

namespace Hilbert.K4Point3Z

instance : (Hilbert.K4Point3Z).HasK where p := 0; q := 1;
instance : (Hilbert.K4Point3Z).HasFour where p := 0
instance : (Hilbert.K4Point3Z).HasZ where p := 0
instance : (Hilbert.K4Point3Z).HasWeakPoint3 where p := 0; q := 1;
instance : Entailment.K4Point3Z (Hilbert.K4Point3Z) where

end Hilbert.K4Point3Z

-- TODO: show it is proper
lemma Logic.K4Point3Z.is_extension_of_K4Point3 : Logic.K4Point3 ⊆ Logic.K4Point3Z := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.K4Point3Z.is_extension_of_K4Z : Logic.K4Z ⊆ Logic.K4Point3Z := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.GLPoint3.is_extension_of_K4Point3Z : Logic.K4Point3Z ⊆ Logic.GLPoint3 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset


protected abbrev Hilbert.KH : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.H (.atom 0)}⟩
protected abbrev Logic.KH := Hilbert.KH.logic

namespace Hilbert.KH

instance : (Hilbert.KH).HasK where p := 0; q := 1;
instance : (Hilbert.KH).HasH where p := 0

end Hilbert.KH


protected abbrev Hilbert.Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}⟩
protected abbrev Logic.Grz := Hilbert.Grz.logic

namespace Hilbert.Grz

instance : (Hilbert.Grz).HasK where p := 0; q := 1;
instance : (Hilbert.Grz).HasGrz where p := 0
instance : Entailment.Grz (Hilbert.Grz) where

instance : Hilbert.KT ⪯ Hilbert.Grz := weakerThan_of_dominate_axioms $ by simp;

end Hilbert.Grz


protected abbrev Hilbert.GrzPoint2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev Logic.GrzPoint2 := Hilbert.GrzPoint2.logic

namespace Hilbert.GrzPoint2

instance : (Hilbert.GrzPoint2).HasK where p := 0; q := 1;
instance : (Hilbert.GrzPoint2).HasGrz where p := 0
instance : (Hilbert.GrzPoint2).HasPoint2 where p := 0
instance : Entailment.GrzPoint2 (Hilbert.GrzPoint2) where

end Hilbert.GrzPoint2


protected abbrev Hilbert.GrzPoint3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.GrzPoint3 := Hilbert.GrzPoint3.logic

namespace Hilbert.GrzPoint3

instance : (Hilbert.GrzPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.GrzPoint3).HasGrz where p := 0
instance : (Hilbert.GrzPoint3).HasPoint3 where p := 0; q := 1;
instance : Entailment.GrzPoint3 (Hilbert.GrzPoint3) where

end Hilbert.GrzPoint3


protected abbrev Hilbert.Dum : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0)}⟩
protected abbrev Logic.Dum := Hilbert.Dum.logic

namespace Hilbert.Dum

instance : (Hilbert.Dum).HasK where p := 0; q := 1;
instance : (Hilbert.Dum).HasT where p := 0
instance : (Hilbert.Dum).HasFour where p := 0
instance : (Hilbert.Dum).HasDum where p := 0
instance : Entailment.Dum (Hilbert.Dum) where

end Hilbert.Dum

-- TODO: show it is proper
lemma Logic.Dum.is_extension_of_S4 : Logic.S4 ⊆ Logic.Dum := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.Grz.is_extension_of_Dum : Logic.Dum ⊆ Logic.Grz := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset


protected abbrev Hilbert.DumPoint2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0), Axioms.Point2 (.atom 0)}⟩
protected abbrev Logic.DumPoint2 := Hilbert.DumPoint2.logic

namespace Hilbert.DumPoint2

instance : (Hilbert.DumPoint2).HasK where p := 0; q := 1;
instance : (Hilbert.DumPoint2).HasT where p := 0
instance : (Hilbert.DumPoint2).HasFour where p := 0
instance : (Hilbert.DumPoint2).HasDum where p := 0
instance : (Hilbert.DumPoint2).HasPoint2 where p := 0
instance : Entailment.DumPoint2 (Hilbert.DumPoint2) where

end Hilbert.DumPoint2

-- TODO: show it is proper
lemma Logic.DumPoint2.is_extension_of_Dum : Logic.Dum ⊆ Logic.DumPoint2 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.DumPoint2.is_extension_of_S4Point2 : Logic.S4Point2 ⊆ Logic.DumPoint2 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.GrzPoint2.is_extension_of_DumPoint2 : Logic.DumPoint2 ⊆ Logic.GrzPoint2 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset


protected abbrev Hilbert.DumPoint3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dum (.atom 0), Axioms.Point3 (.atom 0) (.atom 1)}⟩
protected abbrev Logic.DumPoint3 := Hilbert.DumPoint3.logic

namespace Hilbert.DumPoint3

instance : (Hilbert.DumPoint3).HasK where p := 0; q := 1;
instance : (Hilbert.DumPoint3).HasT where p := 0
instance : (Hilbert.DumPoint3).HasFour where p := 0
instance : (Hilbert.DumPoint3).HasDum where p := 0
instance : (Hilbert.DumPoint3).HasPoint3 where p := 0; q := 1;
instance : Entailment.DumPoint3 (Hilbert.DumPoint3) where

end Hilbert.DumPoint3

-- TODO: show it is proper
lemma Logic.DumPoint3.is_extension_of_Dum : Logic.Dum ⊆ Logic.DumPoint3 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.DumPoint3.is_extension_of_S4Point3 : Logic.S4Point3 ⊆ Logic.DumPoint3 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset
lemma Logic.GrzPoint3.is_extension_of_DumPoint3 : Logic.DumPoint3 ⊆ Logic.GrzPoint3 := Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset



protected abbrev Hilbert.Ver : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}⟩
protected abbrev Logic.Ver := Hilbert.Ver.logic

namespace Hilbert.Ver

instance : (Hilbert.Ver).HasK where p := 0; q := 1;
instance : (Hilbert.Ver).HasVer where p := 0
instance : Entailment.Ver (Hilbert.Ver) where

end Hilbert.Ver




protected abbrev Hilbert.Triv : Hilbert ℕ := ⟨{ Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}⟩
protected abbrev Logic.Triv := Hilbert.Triv.logic

namespace Hilbert.Triv

instance : (Hilbert.Triv).HasK where p := 0; q := 1;
instance : (Hilbert.Triv).HasT where p := 0
instance : (Hilbert.Triv).HasTc where p := 0
instance : Entailment.Triv (Hilbert.Triv) where

end Hilbert.Triv

lemma Hilbert.K4_weakerThan_Triv : Hilbert.K4 ⪯ Hilbert.Triv := weakerThan_of_dominate_axioms $ by simp;


protected abbrev Hilbert.KTc : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Tc (.atom 0)}⟩
protected abbrev Logic.KTc := Hilbert.KTc.logic

namespace Hilbert.KTc

instance : (Hilbert.KTc).HasK where p := 0; q := 1;
instance : (Hilbert.KTc).HasTc where p := 0
instance : Entailment.KTc (Hilbert.KTc) where

end Hilbert.KTc


protected abbrev Hilbert.KD4Point3Z : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.D (.atom 0), Axioms.Four (.atom 0), Axioms.WeakPoint3 (.atom 0) (.atom 1), Axioms.Z (.atom 0)}⟩
protected abbrev Logic.KD4Point3Z := Hilbert.KD4Point3Z.logic

namespace Hilbert.KD4Point3Z

instance : (Hilbert.KD4Point3Z).HasK where p := 0; q := 1;
instance : (Hilbert.KD4Point3Z).HasD where p := 0
instance : (Hilbert.KD4Point3Z).HasFour where p := 0
instance : (Hilbert.KD4Point3Z).HasWeakPoint3 where p := 0; q := 1;
instance : (Hilbert.KD4Point3Z).HasZ where p := 0
instance : Entailment.KD4Point3Z (Hilbert.KD4Point3Z) where

end Hilbert.KD4Point3Z


protected abbrev Hilbert.KTMk : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Mk (.atom 0) (.atom 1)}⟩
protected abbrev Logic.KTMk := Hilbert.KTMk.logic

namespace Hilbert.KTMk

instance : (Hilbert.KTMk).HasK where p := 0; q := 1;
instance : (Hilbert.KTMk).HasT where p := 0
instance : (Hilbert.KTMk).HasMk where p := 0; q := 1
instance : Entailment.KTMk (Hilbert.KTMk) where

end Hilbert.KTMk


protected abbrev Hilbert.N : Hilbert ℕ := ⟨{}⟩
protected abbrev Logic.N := Hilbert.N.logic


end LO.Modal
