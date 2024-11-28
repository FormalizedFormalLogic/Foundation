import Foundation.FirstOrder.Arith.Hierarchy

namespace Fin

@[inline] def addCast (m) : Fin n → Fin (m + n) :=
  castLE <| Nat.le_add_left n m

@[simp] lemma addCast_val (i : Fin n) : (i.addCast m : ℕ) = i := rfl

end Fin

namespace Matrix

variable {α : Type*}

@[simp] lemma appeendr_addCast (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
    appendr u v (i.addCast n) = u i := by simp [appendr, vecAppend_eq_ite]

@[simp] lemma appeendr_addNat (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
    appendr u v (i.addNat m) = v i := by simp [appendr, vecAppend_eq_ite]

end Matrix

namespace LO.FirstOrder

variable {L : Language}

namespace Semiformula

open Rew

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)


end Semiformula

end LO.FirstOrder
