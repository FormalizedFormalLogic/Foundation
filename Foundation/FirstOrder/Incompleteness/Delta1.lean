import Foundation.FirstOrder.Incompleteness.Second

/-!
# $\Delta_1$-definability of theories

*TODO: Prove `𝐈𝚺₁` and `𝐏𝐀` are $\Delta_1$-definable.*

-/

namespace LO.FirstOrder

axiom ISigma1_delta1Definable : 𝐈𝚺₁.Delta1Definable

axiom PA_delta1Definable : 𝐏𝐀.Delta1Definable

attribute [instance] ISigma1_delta1Definable PA_delta1Definable

instance : 𝐈𝚺₁ ⪱ 𝐈𝚺₁ + 𝐂𝐨𝐧[𝐈𝚺₁] := inferInstance

instance : 𝐈𝚺₁ + 𝐂𝐨𝐧[𝐈𝚺₁] ⪯ 𝐓𝐀 := inferInstance

instance : 𝐈𝚺₁ ⪱ 𝐈𝚺₁ + ¬𝐂𝐨𝐧[𝐈𝚺₁] := inferInstance

instance : 𝐏𝐀 ⪱ 𝐏𝐀 + 𝐂𝐨𝐧[𝐏𝐀] := inferInstance

instance : 𝐏𝐀 + 𝐂𝐨𝐧[𝐏𝐀] ⪯ 𝐓𝐀 := inferInstance

instance : 𝐏𝐀 ⪱ 𝐏𝐀 + ¬𝐂𝐨𝐧[𝐏𝐀] := inferInstance

end LO.FirstOrder
