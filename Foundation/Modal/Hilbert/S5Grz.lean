import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Entailment.S5
import Foundation.Modal.Entailment.KTc
import Foundation.Modal.Entailment.Triv

namespace LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S}

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

section S5

variable [DecidableEq F]
variable [Entailment.S5 𝓢]

def lem₁_diaT_of_S5Grz : 𝓢 ⊢ (∼□(∼φ) ➝ ∼□(∼□φ)) ➝ (◇φ ➝ ◇□φ) := C_trans (CCC_of_C_left diaDuality_mp) (CCC_of_C_right diaDuality_mpr)

def lem₂_diaT_of_S5Grz : 𝓢 ⊢ (◇φ ➝ ◇□φ) ➝ (◇φ ➝ φ) := CCC_of_C_right rm_diabox

end S5


protected class S5Grz (𝓢 : S) extends Entailment.S5 𝓢, HasAxiomGrz 𝓢

namespace S5Grz

variable [DecidableEq F]
variable [Entailment.S5Grz 𝓢]

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
instance : Entailment.KTc' 𝓢 where

end S5Grz

end LO.Modal.Entailment


namespace LO.Modal

open Entailment

protected abbrev Hilbert.S5Grz : Hilbert ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.T (.atom 0), Axioms.Five (.atom 0), Axioms.Grz (.atom 0)}⟩
protected abbrev Logic.S5Grz : Logic ℕ := Hilbert.S5Grz.logic
instance : (Hilbert.S5Grz).HasK where p := 0; q := 1;
instance : (Hilbert.S5Grz).HasT where p := 0
instance : (Hilbert.S5Grz).HasFive where p := 0
instance : (Hilbert.S5Grz).HasGrz where p := 0
instance : Entailment.S5Grz (Logic.S5Grz) where
instance : Entailment.KTc' (Logic.S5Grz) where

instance : Logic.S5Grz ≊ Logic.Triv := by
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms; rintro φ (rfl | rfl | rfl | rfl) <;> simp;
  . apply Hilbert.weakerThan_of_provable_axioms; rintro φ (rfl | rfl | rfl) <;> simp;

end LO.Modal
