module

public import Foundation.FirstOrder.Arithmetic.LeastNumber.Basic

/-!
# Relations between fragments at concrete indices

The relations between the fragments are stated for every index, which leaves the theory zoo —
whose vertices are closed theories — with nothing to draw. These are their instances at the first
few indices.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

instance : 𝗜𝚺⁺ 1 ≊ 𝗜𝚷⁺ 1 := ISigmaPlus_equiv_IPiPlus 1

instance : 𝗜𝚺⁺ 2 ≊ 𝗜𝚷⁺ 2 := ISigmaPlus_equiv_IPiPlus 2

instance : 𝗟𝚺⁺ 1 ≊ 𝗜𝚺⁺ 1 := LSigmaPlus_equiv_ISigmaPlus 1

instance : 𝗟𝚷⁺ 1 ≊ 𝗜𝚺⁺ 1 := LPiPlus_equiv_ISigmaPlus 1

instance : 𝗟𝚺⁺ 2 ≊ 𝗜𝚺⁺ 2 := LSigmaPlus_equiv_ISigmaPlus 2

instance : 𝗜𝚺⁺ 1 ⪯ 𝗜𝚺⁺ 2 := ISigmaPlus_weakerThan_of_le (by decide)

instance : 𝗜𝚺⁺ 2 ⪯ 𝗣𝗔 := inferInstance

end FFL.FirstOrder.Arithmetic
