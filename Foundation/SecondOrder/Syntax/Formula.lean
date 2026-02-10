module

public import Foundation.FirstOrder.Basic

@[expose] public section

/-!
# Formulas of monadic second-order logic
-/

namespace LO.SecondOrder

open FirstOrder

inductive Semiformula (L : Language) (ξ : Type*) (ζ : Type*) : ℕ → ℕ → Type _ where
  |  verum {n} {m} : Semiformula L ξ ζ n m
  | falsum {n} {m} : Semiformula L ξ ζ n m
  |    rel {n} {m} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ ζ n m
  |   nrel {n} {m} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ ζ n m
  |    mem {n} {m} : Semiterm L ξ n → ζ ⊕ Fin m → Semiformula L ξ ζ n m
  |   nmem {n} {m} : Semiterm L ξ n → ζ ⊕ Fin m → Semiformula L ξ ζ n m
  |    and {n} {m} : Semiformula L ξ ζ n m → Semiformula L ξ ζ n m → Semiformula L ξ ζ n m
  |     or {n} {m} : Semiformula L ξ ζ n m → Semiformula L ξ ζ n m → Semiformula L ξ ζ n m
  |    all {n} {m} : Semiformula L ξ ζ (n + 1) m → Semiformula L ξ ζ n m
  |     ex {n} {m} : Semiformula L ξ ζ (n + 1) m → Semiformula L ξ ζ n m

end SecondOrder

end LO
