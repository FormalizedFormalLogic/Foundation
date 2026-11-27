module

public import Foundation.Vorspiel.Matrix
public import Mathlib.Data.Vector.Basic

/-!
# Vectors and functions on `Fin`

Companion of Mathlib's `List.Vector.tail_ofFn` and `List.Vector.head_ofFn`.
-/

@[expose] public section

namespace List.Vector

variable {α : Type*} {n : ℕ}

@[simp] lemma ofFn_cons (a : α) (f : Fin n → α) : ofFn (a :> f) = a ::ᵥ ofFn f := by simp [ofFn]

end List.Vector
