module

public import Foundation.FirstOrder.Arithmetic.Collection.Equiv
public import Foundation.FirstOrder.Arithmetic.LeastNumber.Basic

/-!
# Relations between fragments at concrete indices

The relations between the fragments are stated for every index, which leaves the theory zoo —
whose vertices are closed theories — with nothing to draw. These are their instances at the first
few indices.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

instance : 𝗕𝚺 1 ⪯ 𝗜𝚺⁺ 1 := BSigma_weakerThan_IBroadSigma (s := 0)

instance : 𝗕𝚺 2 ⪯ 𝗜𝚺⁺ 2 := BSigma_weakerThan_IBroadSigma (s := 1)

instance : 𝗕𝚺 1 ≊ 𝗕𝚷 0 := BSigma_succ_equiv_BPi (s := 0)

instance : 𝗕𝚺 2 ≊ 𝗕𝚷 1 := BSigma_succ_equiv_BPi (s := 1)

instance : 𝗜𝚺⁺ 1 ≊ 𝗜𝚷⁺ 1 := IBroadSigma_equiv_IBroadPi 1

instance : 𝗜𝚺⁺ 2 ≊ 𝗜𝚷⁺ 2 := IBroadSigma_equiv_IBroadPi 2

instance : 𝗟𝚺⁺ 1 ≊ 𝗜𝚺⁺ 1 := LBroadSigma_equiv_IBroadSigma 1

instance : 𝗟𝚷⁺ 1 ≊ 𝗜𝚺⁺ 1 := LBroadPi_equiv_IBroadSigma 1

instance : 𝗟𝚺⁺ 2 ≊ 𝗜𝚺⁺ 2 := LBroadSigma_equiv_IBroadSigma 2

instance : 𝗜𝚺⁺ 1 ⪯ 𝗜𝚺⁺ 2 := IBroadSigma_weakerThan_of_le (by decide)

instance : 𝗜𝚺⁺ 0 ⪯ 𝗕𝚺 1 := IBroadSigma_weakerThan_BSigma_succ (s := 0)

instance : 𝗜𝚺⁺ 1 ⪯ 𝗕𝚺 2 := IBroadSigma_weakerThan_BSigma_succ (s := 1)

instance : 𝗜𝚺⁺ 2 ⪯ 𝗣𝗔 := inferInstance

end FFL.FirstOrder.Arithmetic
