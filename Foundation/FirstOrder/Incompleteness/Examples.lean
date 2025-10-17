import Foundation.FirstOrder.Incompleteness.First
import Foundation.FirstOrder.Incompleteness.Second

/-!
# $\Delta_1$-definability of theories

*TODO: Prove `𝗜𝚺₁` and `𝗣𝗔` are $\Delta_1$-definable.*
-/

namespace LO.FirstOrder

axiom ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁

axiom PA_delta1Definable : 𝗣𝗔.Δ₁

attribute [instance] ISigma1_delta1Definable PA_delta1Definable

instance : 𝗜𝚺₁ ⪱ 𝗜𝚺₁ + 𝗜𝚺₁.Con := inferInstance

instance : 𝗜𝚺₁ + 𝗜𝚺₁.Con ⪱ 𝗧𝗔 := inferInstance

instance : 𝗜𝚺₁ ⪱ 𝗜𝚺₁ + 𝗜𝚺₁.Incon := inferInstance

instance : 𝗣𝗔 ⪱ 𝗣𝗔 + 𝗣𝗔.Con := inferInstance

instance : 𝗣𝗔 + 𝗣𝗔.Con ⪱ 𝗧𝗔 := inferInstance

instance : 𝗣𝗔 ⪱ 𝗣𝗔 + 𝗣𝗔.Incon := inferInstance

instance : 𝗣𝗔 + 𝗣𝗔.Con ⪱ 𝗣𝗔 + 𝗣𝗔.Con + (𝗣𝗔 + 𝗣𝗔.Con).Incon :=
  have : 𝗜𝚺₁ ⪯ 𝗣𝗔 + 𝗣𝗔.Con := Entailment.WeakerThan.trans (inferInstanceAs (𝗜𝚺₁ ⪯ 𝗣𝗔)) inferInstance
  inferInstance

end LO.FirstOrder
