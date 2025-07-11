import Foundation.FirstOrder.Incompleteness.Second

/-!
# $\Delta_1$-definability of theories

*TODO: Prove `𝐈𝚺₁` and `𝐏𝐀` are $\Delta_1$-definable.*

-/

namespace LO.FirstOrder

axiom ISigma1_delta1Definable : 𝐈𝚺₁.Δ₁Definable

axiom PA_delta1Definable : 𝐏𝐀.Δ₁Definable

attribute [instance] ISigma1_delta1Definable PA_delta1Definable

instance : 𝐈𝚺₁ ⪱ 𝐈𝚺₁ + 𝐈𝚺₁.Con := inferInstance

instance : 𝐈𝚺₁ + 𝐈𝚺₁.Con ⪯ 𝐓𝐀 := inferInstance

instance : 𝐈𝚺₁ ⪱ 𝐈𝚺₁ + 𝐈𝚺₁.Incon := inferInstance

instance : 𝐏𝐀 ⪱ 𝐏𝐀 + 𝐏𝐀.Con := inferInstance

instance : 𝐏𝐀 + 𝐏𝐀.Con ⪯ 𝐓𝐀 := inferInstance

instance : 𝐏𝐀 ⪱ 𝐏𝐀 + 𝐏𝐀.Incon := inferInstance

instance : 𝐏𝐀 + 𝐏𝐀.Con ⪱ 𝐏𝐀 + 𝐏𝐀.Con + (𝐏𝐀 + 𝐏𝐀.Con).Incon :=
  have : 𝐈𝚺₁ ⪯ 𝐏𝐀 + 𝐏𝐀.Con := Entailment.WeakerThan.trans (inferInstanceAs (𝐈𝚺₁ ⪯ 𝐏𝐀)) inferInstance
  inferInstance

end LO.FirstOrder
