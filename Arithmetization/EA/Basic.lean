import Arithmetization.IDeltaZero.Exponential

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Nonempty M] [Zero M] [One M] [Add M] [Mul M] [_root_.Exp M] [LT M] [M ⊧ₘ* 𝐄𝐀]

namespace Model

section ISigma₀

variable [M ⊧ₘ* 𝐈𝚺₀]


end ISigma₀

end Model

end

end Arith

end LO.FirstOrder
