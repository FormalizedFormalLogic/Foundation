module

public import Foundation.ProvabilityLogic.Classification.General
public import Foundation.ProvabilityLogic.GL.Arithmetic
public import Foundation.ProvabilityLogic.S.Arithmetic

/-!
# Examples of provability logics
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open FirstOrder FirstOrder.Arithmetic

variable {α : Type*} {n : ℕ}

namespace Logic.GL

theorem equiv_provabilityLogic_peano : 𝐆𝐋 ≊ 𝗣𝗔.provabilityLogic (α := α) :=
  equiv_provabilityLogic

end Logic.GL

namespace Logic.S

theorem equiv_provabilityLogicRelativeTo_peano_TA :
    𝐒 ≊ 𝗣𝗔.provabilityLogicRelativeTo 𝗧𝗔 (α := α) :=
  equiv_provabilityLogicRelativeTo_TA

end Logic.S

theorem provabilityLogic_turingOmega_equiv_A_ISigma1 :
    𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗜𝚺₁.Conω) (α := α) ≊ 𝐀 :=
  Logic.equiv_of_eq provabilityLogic_turingOmega_eq_A_of_sigma1Sound

theorem provabilityLogic_turingOmega_equiv_A_peano :
    𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗣𝗔.Conω) (α := α) ≊ 𝐀 :=
  Logic.equiv_of_eq provabilityLogic_turingOmega_eq_A_of_sigma1Sound

theorem provabilityLogic_add_localReflectionOn_Sigma1_equiv_D_ISigma1 :
    𝗜𝚺₁.provabilityLogicRelativeTo (𝗜𝚺₁ ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗜𝚺₁) (α := α) ≊ 𝐃 :=
  Logic.equiv_of_eq provabilityLogic_add_localReflectionOn_Sigma_eq_D_of_sigma1Sound

theorem provabilityLogic_add_localReflectionOn_Sigma_equiv_D_peano [NeZero n] :
    𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] 𝗣𝗔) (α := α) ≊ 𝐃 :=
  have : 𝗕𝚺n ⪯ 𝗣𝗔 := BSigma_weakerThan_ISigma_succ.trans inferInstance;
  Logic.equiv_of_eq provabilityLogic_add_localReflectionOn_Sigma_eq_D_of_sigma1Sound

theorem provabilityLogic_add_localReflectionOn_Sigma1_equiv_D_peano :
    𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗣𝗔) (α := α) ≊ 𝐃 :=
  provabilityLogic_add_localReflectionOn_Sigma_equiv_D_peano

end FFL.ProvabilityLogic
