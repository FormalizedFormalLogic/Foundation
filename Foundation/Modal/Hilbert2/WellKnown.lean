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

instance [hB : H.HasB] : System.HasAxiomB H where
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

instance [hD : H.HasD] : System.HasAxiomD H where
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

instance [hFour : H.HasFour] : System.HasAxiomFour H where
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

instance [hFive : H.HasFive] : System.HasAxiomFive H where
  Five φ := by
    apply maxm;
    use Axioms.Five (.atom hFive.p);
    constructor;
    . exact hFive.mem_Five;
    . use (λ b => if hFive.p = b then φ else (.atom b));
      simp;


class HasDot2 (H : Hilbert α) where
  p : α
  mem_Dot2 : Axioms.Dot2 (.atom p) ∈ H.axioms := by tauto;

instance [hDot2 : H.HasDot2] : System.HasAxiomDot2 H where
  Dot2 φ := by
    apply maxm;
    use Axioms.Dot2 (.atom hDot2.p);
    constructor;
    . exact hDot2.mem_Dot2;
    . use (λ b => if hDot2.p = b then φ else (.atom b));
      simp;


class HasDot3 (H : Hilbert α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_Dot3 : Axioms.Dot3 (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [hDot3 : H.HasDot3] : System.HasAxiomDot3 H where
  Dot3 φ ψ := by
    apply maxm;
    use Axioms.Dot3 (.atom hDot3.p) (.atom hDot3.q);
    constructor;
    . exact hDot3.mem_Dot3;
    . use (λ b => if hDot3.p = b then φ else if hDot3.q = b then ψ else (.atom b));
      simp [hDot3.ne_pq];


class HasL (H : Hilbert α) where
  p : α
  mem_L : Axioms.L (.atom p) ∈ H.axioms := by tauto;

instance [hL : H.HasL] : System.HasAxiomL H where
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

instance [hGrz : H.HasGrz] : System.HasAxiomGrz H where
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

instance [hTc : H.HasTc] : System.HasAxiomTc H where
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

instance [DecidableEq α] [hVer : H.HasVer] : System.HasAxiomVer H where
  Ver φ := by
    apply maxm;
    use Axioms.Ver (.atom hVer.p);
    constructor;
    . exact hVer.mem_Ver;
    . use (λ b => if hVer.p = b then φ else (.atom b));
      simp;

end


protected abbrev Ver : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Ver (.atom 0)}⟩
instance : (Hilbert.Ver).HasK where p := 0; q := 1;
instance : (Hilbert.Ver).HasVer where p := 0


protected abbrev Triv : Hilbert ℕ := ⟨{ Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Tc (.atom 0)}⟩
instance : (Hilbert.Triv).HasK where p := 0; q := 1;
instance : (Hilbert.Triv).HasT where p := 0
instance : (Hilbert.Triv).HasTc where p := 0


protected abbrev K4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.K4).HasK where p := 0; q := 1;
instance : (Hilbert.K4).HasFour where p := 0


protected abbrev S4 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0)}⟩
instance : (Hilbert.S4).HasK where p := 0; q := 1;
instance : (Hilbert.S4).HasT where p := 0
instance : (Hilbert.S4).HasFour where p := 0


protected abbrev S4Dot2 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dot2 (.atom 0)}⟩
instance : (Hilbert.S4Dot2).HasK where p := 0; q := 1;
instance : (Hilbert.S4Dot2).HasT where p := 0
instance : (Hilbert.S4Dot2).HasFour where p := 0
instance : (Hilbert.S4Dot2).HasDot2 where p := 0


protected abbrev S4Dot3 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Four (.atom 0), Axioms.Dot3 (.atom 0) (.atom 1)}⟩
instance : (Hilbert.S4Dot3).HasK where p := 0; q := 1;
instance : (Hilbert.S4Dot3).HasT where p := 0
instance : (Hilbert.S4Dot3).HasFour where p := 0
instance : (Hilbert.S4Dot3).HasDot3 where p := 0; q := 1;


protected abbrev S5 : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0)}⟩
instance : (Hilbert.S5).HasK where p := 0; q := 1;
instance : (Hilbert.S5).HasT where p := 0
instance : (Hilbert.S5).HasFive where p := 0


protected abbrev GL : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.L (.atom 0)}⟩
instance : (Hilbert.GL).HasK where p := 0; q := 1;
instance : (Hilbert.GL).HasL where p := 0


protected abbrev Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Grz (.atom 0)}⟩
instance : (Hilbert.Grz).HasK where p := 0; q := 1;
instance : (Hilbert.Grz).HasGrz where p := 0


@[simp] lemma K4_weakerThan_Triv : Hilbert.K4 ≤ₛ Hilbert.Triv := weakerThan_of_dominate_axioms $ by simp;


end Hilbert

end LO.Modal
