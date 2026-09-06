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

namespace LO.FirstOrder.Arithmetic

instance : 𝗜𝚺₁ ⪱ 𝗜𝚺₁ ∪ 𝗜𝚺₁.Con := inferInstance

instance : 𝗜𝚺₁ ∪ 𝗜𝚺₁.Con ⪱ 𝗧𝗔 := inferInstance

instance : 𝗜𝚺₁ ⪱ 𝗜𝚺₁ ∪ 𝗜𝚺₁.Incon := inferInstance

instance : 𝗣𝗔 ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Con := inferInstance

instance : 𝗣𝗔 ∪ 𝗣𝗔.Con ⪱ 𝗧𝗔 := inferInstance

instance : 𝗣𝗔 ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Incon := inferInstance

instance : 𝗣𝗔 ∪ 𝗣𝗔.Con ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Con ∪ (𝗣𝗔 ∪ 𝗣𝗔.Con).Incon :=
  have : 𝗜𝚺₁ ⪯ 𝗣𝗔 := inferInstance
  have : 𝗜𝚺₁ ⪯ 𝗣𝗔 ∪ 𝗣𝗔.Con := Entailment.WeakerThan.trans this inferInstance
  inferInstance

end LO.FirstOrder.Arithmetic
