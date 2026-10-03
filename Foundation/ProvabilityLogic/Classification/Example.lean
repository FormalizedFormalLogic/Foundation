module

public import Foundation.ProvabilityLogic.Classification.General

/-!
# Examples of provability logics
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open FirstOrder FirstOrder.Arithmetic

variable {α : Type*}

lemma provabilityLogic_turingOmega_equiv_A_ISigma1 :
    𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗜𝚺₁.Conω) (α := α) ≊ 𝐀 :=
  Logic.equiv_of_eq provabilityLogic_turingOmega_eq_A_of_sigma1Sound

lemma provabilityLogic_turingOmega_equiv_A_peano :
    𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗣𝗔.Conω) (α := α) ≊ 𝐀 :=
  Logic.equiv_of_eq provabilityLogic_turingOmega_eq_A_of_sigma1Sound

lemma provabilityLogic_add_localReflectionOn_Sigma1_equiv_D_ISigma1 :
    𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗜𝚺₁) (α := α) ≊ 𝐃 :=
  Logic.equiv_of_eq provabilityLogic_add_localReflectionOn_Sigma_eq_D_of_sigma1Sound

lemma provabilityLogic_add_localReflectionOn_Sigma_equiv_D_peano {n : ℕ} [NeZero n] :
    𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] 𝗣𝗔) (α := α) ≊ 𝐃 :=
  have : 𝗕𝚺n ⪯ 𝗣𝗔 := BSigma_weakerThan_ISigma_succ.trans inferInstance;
  Logic.equiv_of_eq provabilityLogic_add_localReflectionOn_Sigma_eq_D_of_sigma1Sound

lemma provabilityLogic_add_localReflectionOn_Sigma1_equiv_D_peano :
    𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗣𝗔) (α := α) ≊ 𝐃 :=
  provabilityLogic_add_localReflectionOn_Sigma_equiv_D_peano

end FFL.ProvabilityLogic
