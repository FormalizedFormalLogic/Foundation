module

public import Foundation.FirstOrder.Incompleteness.First
public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Incompleteness.Definability

@[expose] public section
/-!
# Examples of incompleteness theorems

The definability infrastructure is provided by
`Foundation.FirstOrder.Incompleteness.Definability`
and is used by the examples below.
-/

namespace FFL.FirstOrder.Arithmetic

instance : 𝗜𝚺⁺₁ ⪱ 𝗜𝚺⁺₁ ∪ 𝗜𝚺⁺₁.Con := inferInstance

instance : 𝗜𝚺⁺₁ ∪ 𝗜𝚺⁺₁.Con ⪱ 𝗧𝗔 := inferInstance

instance : 𝗜𝚺⁺₁ ⪱ 𝗜𝚺⁺₁ ∪ 𝗜𝚺⁺₁.Incon := inferInstance

instance : 𝗣𝗔 ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Con := inferInstance

instance : 𝗣𝗔 ∪ 𝗣𝗔.Con ⪱ 𝗧𝗔 := inferInstance

instance : 𝗣𝗔 ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Incon := inferInstance

instance : 𝗣𝗔 ∪ 𝗣𝗔.Con ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Con ∪ (𝗣𝗔 ∪ 𝗣𝗔.Con).Incon := inferInstance

end FFL.FirstOrder.Arithmetic
