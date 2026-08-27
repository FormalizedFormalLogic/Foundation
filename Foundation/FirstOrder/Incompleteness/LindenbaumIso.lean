module

public import Foundation.FirstOrder.Incompleteness.Dense
public import Foundation.Vorspiel.Order.BooleanAlgebra.Iso

@[expose] public section
namespace LO

open Entailment LindenbaumAlgebra FirstOrder

/-- The Lindenbaum algebras of any two consistent, `𝗜𝚺₁`-extension, `Δ₁`-definable
arithmetic theories are order isomorphic: both are countable, nontrivial, atomless
Boolean algebras, so `iso_of_countable_atomless` applies. -/
theorem lindenbaum_iso (T U : ArithmeticTheory)
    [𝗜𝚺₁ ⪯ T] [T.Δ₁] [Consistent T] [𝗜𝚺₁ ⪯ U] [U.Δ₁] [Consistent U] :
    Nonempty (LindenbaumAlgebra T ≃o LindenbaumAlgebra U) := by
  sorry

end LO
