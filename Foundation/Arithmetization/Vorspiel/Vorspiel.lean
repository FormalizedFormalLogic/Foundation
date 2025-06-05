import Foundation.FirstOrder.Arith.Representation
import Foundation.FirstOrder.Arith.PeanoMinus
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Order.Sub.Basic

namespace LO

namespace FirstOrder

namespace Arith

-- attribute [simp] Matrix.vecHead Matrix.vecTail Matrix.comp_vecCons' Matrix.constant_eq_singleton

end Arith

end LO

namespace List.Vector

variable {α : Type*}

@[simp] lemma nil_get (v : Vector α 0) : v.get = ![] := by
  ext i; exact i.elim0

end List.Vector
