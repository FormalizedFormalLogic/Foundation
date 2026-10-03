module

public import Foundation.ProvabilityLogic.Classification.General
public import Foundation.ProvabilityLogic.GL.Arithmetic
public import Foundation.ProvabilityLogic.GLPlusBoxBot.Arithmetic
public import Foundation.ProvabilityLogic.S.Arithmetic

/-!
# Examples of provability logics
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open FirstOrder FirstOrder.Arithmetic

variable {α : Type*} {n : ℕ}

set_option hygiene false in
local notation "PL(" T ")" => ArithmeticTheory.provabilityLogic T (α := α)

set_option hygiene false in
local notation "PL(" T ", " U ")" => ArithmeticTheory.provabilityLogicRelativeTo T U (α := α)

theorem provabilityLogic_equiv_GL_peano : PL(𝗣𝗔) ≊ 𝐆𝐋 :=
  Logic.equiv_of_eq Logic.GL.eq_provabilityLogic.symm

instance : (𝐆𝐋 : Logic α) ⪱ Logic.GLPlusBoxBot 1 :=
  inferInstanceAs (𝐆𝐋 ⪱ Logic.GLPlusBoxBot (1 : ℕ))

theorem provabilityLogic_add_incon_equiv_GLPlusBoxBot_one_peano :
    PL(𝗣𝗔 ∪ 𝗣𝗔.Incon) ≊ Logic.GLPlusBoxBot 1 := by
  simpa [height_union_incon_eq_one] using
    (Logic.GLPlusBoxBot.equiv_provabilityLogic (T := 𝗣𝗔 ∪ 𝗣𝗔.Incon)).symm

theorem provabilityLogic_TA_equiv_S_peano : PL(𝗣𝗔, 𝗧𝗔) ≊ 𝐒 :=
  Logic.equiv_of_eq Logic.S.eq_provabilityLogicRelativeTo_TA.symm

theorem provabilityLogic_turingOmega_equiv_A_ISigma1 : PL(𝗜𝚺₁, 𝗜𝚺₁ ∪ 𝗜𝚺₁.Conω) ≊ 𝐀 :=
  Logic.equiv_of_eq provabilityLogic_turingOmega_eq_A_of_sigma1Sound

theorem provabilityLogic_turingOmega_equiv_A_peano : PL(𝗣𝗔, 𝗣𝗔 ∪ 𝗣𝗔.Conω) ≊ 𝐀 :=
  Logic.equiv_of_eq provabilityLogic_turingOmega_eq_A_of_sigma1Sound

theorem provabilityLogic_add_localReflectionOn_Sigma1_equiv_D_ISigma1 :
    PL(𝗜𝚺₁, 𝗜𝚺₁ ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗜𝚺₁) ≊ 𝐃 :=
  Logic.equiv_of_eq provabilityLogic_add_localReflectionOn_Sigma_eq_D_of_sigma1Sound

theorem provabilityLogic_add_localReflectionOn_Sigma_equiv_D_peano [NeZero n] :
    PL(𝗣𝗔, 𝗣𝗔 ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 n] 𝗣𝗔) ≊ 𝐃 :=
  have : 𝗕𝚺n ⪯ 𝗣𝗔 := BSigma_weakerThan_ISigma_succ.trans inferInstance;
  Logic.equiv_of_eq provabilityLogic_add_localReflectionOn_Sigma_eq_D_of_sigma1Sound

theorem provabilityLogic_add_localReflectionOn_Sigma1_equiv_D_peano :
    PL(𝗣𝗔, 𝗣𝗔 ∪ 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] 𝗣𝗔) ≊ 𝐃 :=
  provabilityLogic_add_localReflectionOn_Sigma_equiv_D_peano

end FFL.ProvabilityLogic
