module

public import Foundation.FirstOrder.Arithmetic.Collection.Induction
public import Foundation.FirstOrder.Arithmetic.LeastNumber.Basic

/-!
# Relations between fragments at concrete indices

The relations between the fragments are stated for every index, which leaves the theory zoo —
whose vertices are closed theories — with nothing to draw. These are their instances at the first
few indices.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

instance : 𝗕𝚺 1 ⪯ 𝗜𝚺 1 := BSigma_weakerThan_ISigma 0

instance : 𝗕𝚺 2 ⪯ 𝗜𝚺 2 := BSigma_weakerThan_ISigma 1

instance : 𝗕𝚺 1 ≊ 𝗕𝚷 0 := BSigma_succ_equiv_BPi 0

instance : 𝗕𝚺 2 ≊ 𝗕𝚷 1 := BSigma_succ_equiv_BPi 1

instance : 𝗜𝚺 1 ≊ 𝗜𝚷 1 := ISigma_equiv_IPi 1

instance : 𝗜𝚺 2 ≊ 𝗜𝚷 2 := ISigma_equiv_IPi 2

instance : 𝗟𝚺 1 ≊ 𝗜𝚺 1 := LSigma_equiv_ISigma 1

instance : 𝗟𝚷 1 ≊ 𝗜𝚺 1 := LPi_equiv_ISigma 1

instance : 𝗟𝚺 2 ≊ 𝗜𝚺 2 := LSigma_equiv_ISigma 2

instance : 𝗜𝚺 1 ⪯ 𝗜𝚺 2 := ISigma_weakerThan_of_le (by decide)

instance : 𝗜𝚺 0 ⪯ 𝗕𝚺 1 := ISigma_weakerThan_BSigma_succ 0

instance : 𝗜𝚺 1 ⪯ 𝗕𝚺 2 := ISigma_weakerThan_BSigma_succ 1

instance : 𝗜𝚺 2 ⪯ 𝗣𝗔 := inferInstance

end FFL.FirstOrder.Arithmetic
