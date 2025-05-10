import Foundation.Vorspiel.Vorspiel

namespace List.Vector

variable {α : Type*}

lemma get_mk_eq_get {n} (l : List α) (h : l.length = n) (i : Fin n) : List.Vector.get (⟨l, h⟩ : List.Vector α n) i = l.get (i.cast h.symm) := rfl

lemma get_one {α : Type*} {n} (v : Vector α (n + 2)) : v.get 1 = v.tail.head := by
  rw [←Vector.get_zero, Vector.get_tail_succ]; rfl

lemma ofFn_vecCons (a : α) (v : Fin n → α) :
    ofFn (a :> v) = a ::ᵥ ofFn v := by
  ext i; cases i using Fin.cases <;> simp

@[simp] lemma nil_get (v : Vector α 0) : v.get = ![] := by
  ext i; exact i.elim0

end List.Vector
