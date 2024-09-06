import Incompleteness.Arith.First
import Incompleteness.Arith.Second
import Incompleteness.DC.Basic

noncomputable section

open LO.FirstOrder.DerivabilityCondition

namespace LO.FirstOrder.Arith

open LO.Arith LO.Arith.Formalized

variable (T : Theory ℒₒᵣ) [𝐈𝚺₁ ≼ T]

variable (U : Theory ℒₒᵣ) [U.Delta1Definable] [ℕ ⊧ₘ* U] [𝐑₀ ≼ U]

instance : Diagonalization T where
  fixpoint := fixpoint
  diag θ := diagonal θ

abbrev _root_.LO.FirstOrder.Theory.standardDP : ProvabilityPredicate T U where
  prov := U.provableₐ
  spec := provableₐ_D1

instance : (Theory.standardDP T U).HBL2 := ⟨provableₐ_D2⟩
instance : (Theory.standardDP T U).HBL3 := ⟨provableₐ_D3⟩
instance : (Theory.standardDP T U).HBL := ⟨⟩
instance : (Theory.standardDP T U).GoedelSound := ⟨fun h ↦ by simpa using provableₐ_sound h⟩

end LO.FirstOrder.Arith

end
