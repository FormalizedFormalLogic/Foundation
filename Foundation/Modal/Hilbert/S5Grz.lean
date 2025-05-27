import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Entailment.S5
import Foundation.Modal.Entailment.KTc
import Foundation.Modal.Entailment.Triv

namespace LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S}


section S5

variable [DecidableEq F]
variable [Entailment.Modal.S5 𝓢]

def lem₁_diaT_of_S5Grz : 𝓢 ⊢ (∼□(∼φ) ➝ ∼□(∼□φ)) ➝ (◇φ ➝ ◇□φ) := C_trans (CCC_of_C_left diaDuality_mp) (CCC_of_C_right diaDuality_mpr)

def lem₂_diaT_of_S5Grz : 𝓢 ⊢ (◇φ ➝ ◇□φ) ➝ (◇φ ➝ φ) := CCC_of_C_right rm_diabox

end S5


protected class Modal.S5Grz (𝓢 : S) extends Entailment.Modal.S5 𝓢, HasAxiomGrz 𝓢

namespace S5Grz

variable [DecidableEq F]
variable [Entailment.Modal.S5Grz 𝓢]

protected def diaT : 𝓢 ⊢ ◇φ ➝ φ := by
  have : 𝓢 ⊢ (φ ➝ □φ) ➝ (∼□φ ➝ ∼φ) := CCCNN;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ □(∼□φ ➝ ∼φ) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (□(∼□φ) ➝ □(∼φ)) := C_trans this axiomK;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (∼□(∼φ) ➝ ∼□(∼□φ)) := C_trans this CCCNN;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (◇φ ➝ ◇□φ) := C_trans this lem₁_diaT_of_S5Grz;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (◇φ ➝ □φ) := C_trans this $ CCC_of_C_right diabox_box;
  have : 𝓢 ⊢ □(φ ➝ □φ) ➝ (◇φ ➝ φ) := C_trans this $ CCC_of_C_right axiomT;
  have : 𝓢 ⊢ ◇φ ➝ □(φ ➝ □φ) ➝ φ := C_swap this;
  have : 𝓢 ⊢ □◇φ ➝ □(□(φ ➝ □φ) ➝ φ) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □◇φ ➝ φ := C_trans this axiomGrz;
  exact C_trans axiomFive this;

instance : HasAxiomDiaT 𝓢 := ⟨fun _ ↦ S5Grz.diaT⟩
instance : Entailment.Modal.KTc' 𝓢 where

end S5Grz

end LO.Entailment


namespace LO.Modal

open Entailment

protected abbrev Hilbert.S5Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0), Axioms.Grz (.atom 0)}⟩

namespace Hilbert.S5Grz
instance : (Hilbert.S5Grz).HasK where p := 0; q := 1;
instance : (Hilbert.S5Grz).HasT where p := 0
instance : (Hilbert.S5Grz).HasFive where p := 0
instance : (Hilbert.S5Grz).HasGrz where p := 0
instance : Entailment.Modal.S5Grz (Hilbert.S5Grz) where
instance : Entailment.Modal.KTc' (Hilbert.S5Grz) where

end Hilbert.S5Grz

protected abbrev Logic.S5Grz := Hilbert.S5Grz.logic

theorem Hilbert.iff_provable_S5Grz_provable_Triv : (Hilbert.S5Grz ⊢! φ) ↔ (Hilbert.Triv ⊢! φ) := by
  constructor;
  . apply fun h ↦ (weakerThan_of_dominate_axioms @h).subset;
    simp;
  . apply fun h ↦ (weakerThan_of_dominate_axioms @h).subset;
    rintro φ (⟨_, _, rfl⟩ | (⟨_, rfl⟩ | ⟨_, rfl⟩)) <;> simp;

lemma Logic.eq_S5Grz_Triv : Logic.S5Grz = Logic.Triv := by
  ext φ;
  exact Hilbert.iff_provable_S5Grz_provable_Triv;

end LO.Modal
