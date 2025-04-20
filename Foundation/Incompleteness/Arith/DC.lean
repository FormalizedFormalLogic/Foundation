import Foundation.Incompleteness.Arith.First
import Foundation.Incompleteness.Arith.Second
import Foundation.Incompleteness.DC.Basic

noncomputable section

open LO.FirstOrder.DerivabilityCondition

namespace LO.FirstOrder.Arith

open LO.Arith LO.Arith.Formalized

variable (T : Theory ℒₒᵣ) [𝐈𝚺₁ ⪯ T]

variable (U : Theory ℒₒᵣ) [U.Delta1Definable]

instance : Diagonalization T where
  fixpoint := fixpoint
  diag θ := diagonal θ

/-- TODO: rename to `standardPP`-/
abbrev _root_.LO.FirstOrder.Theory.standardDP : ProvabilityPredicate T U where
  prov := U.provableₐ
  D1 := provableₐ_D1

instance : (Theory.standardDP T U).HBL2 := ⟨provableₐ_D2⟩
instance : (Theory.standardDP T U).HBL3 := ⟨provableₐ_D3⟩
instance : (Theory.standardDP T U).HBL := ⟨⟩
instance [ℕ ⊧ₘ* U] [𝐑₀ ⪯ U] : (Theory.standardDP T U).GoedelSound := ⟨fun h ↦ by simpa using provableₐ_sound h⟩

lemma standardDP_def (σ : Sentence ℒₒᵣ) : (T.standardDP U) σ = U.provableₐ.val/[⌜σ⌝] := rfl

end LO.FirstOrder.Arith

end
