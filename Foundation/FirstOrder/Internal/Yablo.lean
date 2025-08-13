import Foundation.ProvabilityLogic.Incompleteness
import Foundation.FirstOrder.Internal.FixedPoint
import Foundation.FirstOrder.Internal.RosserProvability

namespace LO.FirstOrder

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath InternalArithmetic

namespace Theory

variable {V} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]
         {L : Language} [L.Encodable] [L.LORDefinable]
         (T : Theory ℒₒᵣ) [T.Δ₁]

def YabloSystem (φ n : V) : Prop := ∀ m, n < m → ¬T.Provable (substNumeral φ m)

def yabloSystem : 𝚷₁.Semisentence 2 := .mkPi
  “φ n. ∀ m, n < m → ∀ nσ, !ssnum nσ φ m → ¬!T.provable (nσ)”

lemma YabloSystem_defined :
    𝚷₁-Relation[V] (T.YabloSystem) via T.yabloSystem := by
  intro f;
  simp [Theory.YabloSystem, Theory.yabloSystem];

end Theory

end LO.FirstOrder
