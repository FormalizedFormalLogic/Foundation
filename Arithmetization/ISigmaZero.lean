import Arithmetization.IOpen
import Mathlib.Tactic.Linarith

namespace LO.FirstOrder

attribute [simp] Semiformula.eval_substs Matrix.vecHead Matrix.vecTail Matrix.comp_vecCons' Matrix.constant_eq_singleton

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

section ISigma₀

variable [𝐈𝚺₀.Mod M]


end ISigma₀

end Model

end

end Arith

end LO.FirstOrder
