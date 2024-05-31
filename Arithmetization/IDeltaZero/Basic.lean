import Arithmetization.Basic.IOpen
import Mathlib.Tactic.Linarith

namespace LO.FirstOrder

attribute [simp] Semiformula.eval_substs Matrix.vecHead Matrix.vecTail Matrix.comp_vecCons' Matrix.constant_eq_singleton

namespace Arith

noncomputable section

variable {M : Type*} [Nonempty M] [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐏𝐀⁻]

namespace Model

section ISigma₀

variable [M ⊧ₘ* 𝐈𝚺₀]


end ISigma₀

end Model

end

end Arith

end LO.FirstOrder
