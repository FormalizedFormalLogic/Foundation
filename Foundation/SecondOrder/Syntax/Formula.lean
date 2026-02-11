module

public import Foundation.FirstOrder.Basic

@[expose] public section

/-!
# Formulas of monadic second-order logic
-/

namespace LO.SecondOrder

open FirstOrder

inductive Semiformula (L : Language) (ξ : Type*) (ζ : Type*) : ℕ → ℕ → Type _ where
  |    rel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ ζ n m
  |   nrel : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ ζ n m
  |   bvar : Fin m → Semiterm L ξ n → Semiformula L ξ ζ n m
  |  nbvar : Fin m → Semiterm L ξ n → Semiformula L ξ ζ n m
  |   fvar : ζ → Semiterm L ξ n → Semiformula L ξ ζ n m
  |  nfvar : ζ → Semiterm L ξ n → Semiformula L ξ ζ n m
  |  verum : Semiformula L ξ ζ n m
  | falsum : Semiformula L ξ ζ n m
  |    and : Semiformula L ξ ζ n m → Semiformula L ξ ζ n m → Semiformula L ξ ζ n m
  |     or : Semiformula L ξ ζ n m → Semiformula L ξ ζ n m → Semiformula L ξ ζ n m
  |   all₀ : Semiformula L ξ ζ (n + 1) m → Semiformula L ξ ζ n m
  |    ex₀ : Semiformula L ξ ζ (n + 1) m → Semiformula L ξ ζ n m
  |   all₁ : Semiformula L ξ ζ n (m + 1) → Semiformula L ξ ζ n m
  |    ex₁ : Semiformula L ξ ζ n (m + 1) → Semiformula L ξ ζ n m

abbrev Formula (L : Language) (ξ ζ : Type*) := Semiformula L ξ ζ 0 0

abbrev Semisentence (L : Language) (n m : ℕ) := Semiformula L Empty Empty n m

abbrev Sentence (L : Language) := Semiformula L Empty Empty 0 0

abbrev Semistatement (L : Language) (n m : ℕ) := Semiformula L ℕ ℕ n m

abbrev Statement (L : Language) := Semiformula L ℕ ℕ 0 0

instance : Top (Semiformula L ξ ζ n m) where
  top := Semiformula.verum

end SecondOrder

end LO
