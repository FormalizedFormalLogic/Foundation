import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.System.S5
import Foundation.Modal.System.KTc
import Foundation.Modal.System.Triv

namespace LO.System

variable {S F : Type*} [BasicModalLogicalConnective F] [System F S]
variable {𝓢 : S}


section S5

variable [DecidableEq F]
variable [System.S5 𝓢]

def lem₁_diaT_of_S5Grz : 𝓢 ⊢ (∼□(∼φ) ➝ ∼□(∼□φ)) ➝ (◇φ ➝ ◇□φ) := impTrans'' (rev_dhyp_imp' diaDuality_mp) (dhyp_imp' diaDuality_mpr)

def lem₂_diaT_of_S5Grz : 𝓢 ⊢ (◇φ ➝ ◇□φ) ➝ (◇φ ➝ φ) := dhyp_imp' rm_diabox

end S5


protected class S5Grz (𝓢 : S) extends System.S5 𝓢, HasAxiomGrz 𝓢

namespace S5Grz

variable [DecidableEq F]
variable [System.S5Grz 𝓢]

protected def diaT : 𝓢 ⊢ ◇φ ➝ φ := by
  have : 𝓢 ⊢ (φ ➝ □φ) ➝ (∼□φ ➝ ∼φ) := contra₀;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ □(∼□φ ➝ ∼φ) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (□(∼□φ) ➝ □(∼φ)) := impTrans'' this axiomK;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (∼□(∼φ) ➝ ∼□(∼□φ)) := impTrans'' this contra₀;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (◇φ ➝ ◇□φ) := impTrans'' this lem₁_diaT_of_S5Grz;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (◇φ ➝ □φ) := impTrans'' this $ dhyp_imp' diabox_box;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (◇φ ➝ φ) := impTrans'' this $ dhyp_imp' axiomT;
  have : 𝓢 ⊢ ◇φ ➝ □(φ ➝ □φ) ➝ φ := impSwap' this;
  have : 𝓢 ⊢ □◇φ ➝ □(□(φ ➝ □φ) ➝ φ) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □◇φ ➝ φ := impTrans'' this axiomGrz;
  exact impTrans'' axiomFive this;

instance : HasAxiomDiaT 𝓢 := ⟨fun _ ↦ S5Grz.diaT⟩
instance : System.KTc' 𝓢 where

end S5Grz

end LO.System


namespace LO.Modal.Hilbert

open System

protected abbrev S5Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0), Axioms.Grz (.atom 0)}⟩
instance : (Hilbert.S5Grz).HasK where p := 0; q := 1;
instance : (Hilbert.S5Grz).HasT where p := 0
instance : (Hilbert.S5Grz).HasFive where p := 0
instance : (Hilbert.S5Grz).HasGrz where p := 0
instance : System.S5Grz (Hilbert.S5Grz) where
instance : System.KTc' (Hilbert.S5Grz) where

theorem iff_provable_S5Grz_provable_Triv : (Hilbert.S5Grz ⊢! φ) ↔ (Hilbert.Triv ⊢! φ) := by
  constructor;
  . apply weakerThan_of_dominate_axioms;
    simp;
  . apply weakerThan_of_dominate_axioms;
    rintro φ (⟨_, _, rfl⟩ | (⟨_, rfl⟩ | ⟨_, rfl⟩)) <;> simp;

end LO.Modal.Hilbert
