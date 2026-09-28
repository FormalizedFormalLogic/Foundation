module

public import Foundation.FirstOrder.Incompleteness.First
public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Incompleteness.Definability

/-!
# Examples of incompleteness theorems
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

instance : 𝗜𝚺₁ ⪱ 𝗜𝚺₁ ∪ 𝗜𝚺₁.Con := inferInstance

instance : 𝗜𝚺₁ ∪ 𝗜𝚺₁.Con ⪱ 𝗧𝗔 := inferInstance

instance : 𝗜𝚺₁ ⪱ 𝗜𝚺₁ ∪ 𝗜𝚺₁.Incon := inferInstance

instance : 𝗣𝗔 ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Con := inferInstance

instance : 𝗣𝗔 ∪ 𝗣𝗔.Con ⪱ 𝗧𝗔 := inferInstance

instance : 𝗣𝗔 ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Incon := inferInstance

instance : 𝗣𝗔 ∪ 𝗣𝗔.Con ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Con ∪ (𝗣𝗔 ∪ 𝗣𝗔.Con).Incon := inferInstance

end FFL.FirstOrder.Arithmetic
