import Foundation.Modal.Hilbert2.K

namespace LO.Modal

namespace Hilbert

section

open Deduction

variable {H : Hilbert α}
variable [DecidableEq α]


class HasT (H : Hilbert α) where
  p : α
  mem_T : Axioms.T (.atom p) ∈ H.axioms := by tauto;

instance [hT : H.HasT] : System.HasAxiomT H where
  T φ := by simpa using subst (s := λ b => if hT.p = b then φ else (.atom b)) $ maxm hT.mem_T;


class HasB (H : Hilbert α) where
  p : α
  mem_B : Axioms.B (.atom p) ∈ H.axioms := by tauto;

instance [hB : H.HasB] : System.HasAxiomB H where
  B φ := by simpa using subst (s := λ b => if hB.p = b then φ else (.atom b)) $ maxm hB.mem_B;


class HasD (H : Hilbert α) where
  p : α
  mem_D : Axioms.D (.atom p) ∈ H.axioms := by tauto;

instance [hD : H.HasD] : System.HasAxiomD H where
  D φ := by simpa using subst (s := λ b => if hD.p = b then φ else (.atom b)) $ maxm hD.mem_D;


class HasFour (H : Hilbert α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [hFour : H.HasFour] : System.HasAxiomFour H where
  Four φ := by simpa using subst (s := λ b => if hFour.p = b then φ else (.atom b)) $ maxm hFour.mem_Four;


class HasFive (H : Hilbert α) where
  p : α
  mem_Five : Axioms.Five (.atom p) ∈ H.axioms := by tauto;

instance [hFive : H.HasFive] : System.HasAxiomFive H where
  Five φ := by simpa using subst (s := λ b => if hFive.p = b then φ else (.atom b)) $ maxm hFive.mem_Five;


class HasDot2 (H : Hilbert α) where
  p : α
  mem_Dot2 : Axioms.Dot2 (.atom p) ∈ H.axioms := by tauto;

instance [hDot2 : H.HasDot2] : System.HasAxiomDot2 H where
  Dot2 φ := by simpa using subst (s := λ b => if hDot2.p = b then φ else (.atom b)) $ maxm hDot2.mem_Dot2;


class HasDot3 (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q
  mem_Dot3 : Axioms.Dot3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [hDot3 : H.HasDot3] : System.HasAxiomDot3 H where
  Dot3 φ ψ := by
    simpa [hDot3.ne_pq] using
      subst (s := λ b => if hDot3.p = b then φ else if hDot3.q = b then ψ else (.atom b)) $
      maxm hDot3.mem_Dot3;


class HasL (H : Hilbert α) where
  p : α
  mem_L : Axioms.L (.atom p) ∈ H.axioms := by tauto;

instance [hL : H.HasL] : System.HasAxiomL H where
  L φ := by simpa using subst (s := λ b => if hL.p = b then φ else (.atom b)) $ maxm hL.mem_L;


class HasGrz (H : Hilbert α) where
  p : α
  mem_Grz : Axioms.Grz (.atom p) ∈ H.axioms := by tauto;

instance [hGrz : H.HasGrz] : System.HasAxiomGrz H where
  Grz φ := by simpa using subst (s := λ b => if hGrz.p = b then φ else (.atom b)) $ maxm hGrz.mem_Grz;


class HasTc (H : Hilbert α) where
  p : α
  mem_Tc : Axioms.Tc (.atom p) ∈ H.axioms := by tauto;

instance [hTc : H.HasTc] : System.HasAxiomTc H where
  Tc φ := by simpa using subst (s := λ b => if hTc.p = b then φ else (.atom b)) $ maxm hTc.mem_Tc;


class HasVer (H : Hilbert α) where
  p : α
  mem_Ver : Axioms.Ver (.atom p) ∈ H.axioms := by tauto;

instance [DecidableEq α] [hVer : H.HasVer] : System.HasAxiomVer H where
  Ver φ := by simpa using subst (s := λ b => if hVer.p = b then φ else (.atom b)) $ maxm hVer.mem_Ver;

end


protected abbrev Ver : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}⟩
instance : (Hilbert.Ver).HasK where p := 0; q := 1; ne_pq := by trivial
instance : (Hilbert.Ver).HasVer where p := 0


protected abbrev Triv : Hilbert ℕ := ⟨{ Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}⟩
instance : (Hilbert.Triv).HasK where p := 0; q := 1; ne_pq := by trivial;
instance : (Hilbert.Triv).HasT where p := 0
instance : (Hilbert.Triv).HasTc where p := 0


protected abbrev K4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.K4).HasK where p := 0; q := 1; ne_pq := by trivial
instance : (Hilbert.K4).HasFour where p := 0


protected abbrev S4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.S4).HasK where p := 0; q := 1; ne_pq := by trivial
instance : (Hilbert.S4).HasT where p := 0
instance : (Hilbert.S4).HasFour where p := 0


protected abbrev S4Dot2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dot2 (.atom 0)}⟩
instance : (Hilbert.S4Dot2).HasK where p := 0; q := 1; ne_pq := by trivial
instance : (Hilbert.S4Dot2).HasT where p := 0
instance : (Hilbert.S4Dot2).HasFour where p := 0
instance : (Hilbert.S4Dot2).HasDot2 where p := 0


protected abbrev S4Dot3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dot3 (.atom 0) (.atom 1)}⟩
instance : (Hilbert.S4Dot3).HasK where p := 0; q := 1; ne_pq := by trivial
instance : (Hilbert.S4Dot3).HasT where p := 0
instance : (Hilbert.S4Dot3).HasFour where p := 0
instance : (Hilbert.S4Dot3).HasDot3 where p := 0; q := 1; ne_pq := by trivial


protected abbrev S5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.S5).HasK where p := 0; q := 1; ne_pq := by trivial
instance : (Hilbert.S5).HasT where p := 0
instance : (Hilbert.S5).HasFive where p := 0


protected abbrev GL : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}⟩
instance : (Hilbert.GL).HasK where p := 0; q := 1; ne_pq := by trivial
instance : (Hilbert.GL).HasL where p := 0


protected abbrev Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}⟩
instance : (Hilbert.Grz).HasK where p := 0; q := 1; ne_pq := by trivial
instance : (Hilbert.Grz).HasGrz where p := 0


@[simp] lemma K4_weakerThan_Triv : Hilbert.K4 ≤ₛ Hilbert.Triv := weakerThan_of_dominate_axioms $ by simp;


end Hilbert

end LO.Modal
