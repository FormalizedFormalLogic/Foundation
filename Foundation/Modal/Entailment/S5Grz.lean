module

public import Foundation.Modal.Entailment.S5
public import Foundation.Modal.Entailment.Triv

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment S F]
variable {𝓢 : S} [DecidableEq F] [Entailment.S5Grz 𝓢]

protected noncomputable def S5Grz.diaT : 𝓢 ⊢! ◇φ ➝ φ := by
  have : 𝓢 ⊢! (φ ➝ □φ) ➝ (∼□φ ➝ ∼φ) := CCCNN;
  have : 𝓢 ⊢! □(φ ➝ □φ) ➝ □(∼□φ ➝ ∼φ) := implyBoxDistribute' this;
  have : 𝓢 ⊢! □(φ ➝ □φ) ➝ (□(∼□φ) ➝ □(∼φ)) := C_trans this axiomK;
  have : 𝓢 ⊢! □(φ ➝ □φ) ➝ (∼□(∼φ) ➝ ∼□(∼□φ)) := C_trans this CCCNN;
  have : 𝓢 ⊢! □(φ ➝ □φ) ➝ (◇φ ➝ ◇□φ) := C_trans this lem₁_diaT_of_S5Grz;
  have : 𝓢 ⊢! □(φ ➝ □φ) ➝ (◇φ ➝ □φ) := C_trans this $ CCC_of_C_right diabox_box;
  have : 𝓢 ⊢! □(φ ➝ □φ) ➝ (◇φ ➝ φ) := C_trans this $ CCC_of_C_right axiomT;
  have : 𝓢 ⊢! ◇φ ➝ □(φ ➝ □φ) ➝ φ := C_swap this;
  have : 𝓢 ⊢! □◇φ ➝ □(□(φ ➝ □φ) ➝ φ) := implyBoxDistribute' this;
  have : 𝓢 ⊢! □◇φ ➝ φ := C_trans this axiomGrz;
  exact C_trans axiomFive this;

noncomputable instance : HasAxiomDiaT 𝓢 := ⟨S5Grz.diaT⟩
noncomputable instance : Entailment.KTc' 𝓢 where

end LO.Modal.Entailment
end
