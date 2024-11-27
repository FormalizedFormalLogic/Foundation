import Foundation.Modal.Hilbert.Systems
import Foundation.Modal.System.S5
import Foundation.Modal.System.Triv

namespace LO.System

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S}

def lem₁_diaT_of_S5Grz [System.S5 𝓢] : 𝓢 ⊢ (∼□(∼φ) ➝ ∼□(∼□φ)) ➝ (◇φ ➝ ◇□φ) := impTrans'' (rev_dhyp_imp' diaDuality_mp) (dhyp_imp' diaDuality_mpr)

def lem₂_diaT_of_S5Grz [System.S5 𝓢] : 𝓢 ⊢ (◇φ ➝ ◇□φ) ➝ (◇φ ➝ φ) := dhyp_imp' rm_diabox


protected class S5Grz (𝓢 : S) extends System.S5 𝓢, HasAxiomGrz 𝓢

namespace S5Grz

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

protected def Tc : 𝓢 ⊢ φ ➝ □φ := impTrans'' (contra₃' (impTrans'' (and₂' diaDuality) S5Grz.diaT)) box_dne
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ S5Grz.Tc⟩

end S5Grz

end LO.System


namespace LO.Modal.Hilbert

open System

section

protected abbrev S5Grz (α) : Hilbert α := Hilbert.ExtK $ 𝗧 ∪ 𝟱 ∪ 𝗚𝗿𝘇
instance : System.S5Grz (Hilbert.S5Grz α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Five _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Grz _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

end

variable [DecidableEq α]

lemma S5Grz_weakerThan_Triv : (Hilbert.S5Grz α) ≤ₛ (Hilbert.Triv α) := normal_weakerThan_of_maxm $ by
  rintro φ (⟨_, _, rfl⟩ | (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;> simp [axiomK!, axiomT, axiomTc!, axiomGrz!];

lemma Triv_weakerThan_S5Grz : (Hilbert.Triv α) ≤ₛ (Hilbert.S5Grz α) := normal_weakerThan_of_maxm $ by
  rintro φ (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp [axiomK!, axiomT, axiomTc!];

theorem S5Grz_equiv_Triv : (Hilbert.S5Grz α) =ₛ (Hilbert.Triv α)
  := Equiv.antisymm_iff.mpr ⟨S5Grz_weakerThan_Triv, Triv_weakerThan_S5Grz⟩

end LO.Modal.Hilbert
