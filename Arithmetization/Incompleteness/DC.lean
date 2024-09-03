import Arithmetization.Incompleteness.Second
import Logic.FirstOrder.Incompleteness.DerivabilityCondition

noncomputable section

open LO.FirstOrder.DerivabilityCondition

namespace LO.FirstOrder.Arith

open LO.Arith LO.Arith.Formalized

variable (T : Theory ℒₒᵣ) [𝐈𝚺₁ ≼ T]

variable (U : Theory ℒₒᵣ) [U.Delta1Definable] [ℕ ⊧ₘ* U] [𝐑₀ ≼ U]

instance : Diagonalization T where
  fixpoint := fixpoint
  diag θ := diagonal θ

abbrev _root_.LO.FirstOrder.Theory.standardDP : ProvabilityPredicate ℒₒᵣ ℒₒᵣ := ⟨U.provableₐ⟩

instance : U.standardDP.HBL1 T U := ⟨provableₐ_D1⟩
instance : U.standardDP.HBL2 T U := ⟨provableₐ_D2⟩
instance : U.standardDP.HBL3 T U := ⟨provableₐ_D3⟩
instance : U.standardDP.HBL T U := ⟨⟩
instance : U.standardDP.GoedelSound T U := ⟨fun h ↦ by simpa using provableₐ_sound h⟩

end LO.FirstOrder.Arith

end
