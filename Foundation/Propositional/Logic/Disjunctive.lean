import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Kripke.Hilbert.Int

namespace LO.Propositional

protected class Logic.Disjunctive (L : Logic) where
  disjunctive {φ ψ} : φ ⋎ ψ ∈ L → φ ∈ L ∨ ψ ∈ L


namespace Hilbert

open Entailment

instance {H : Hilbert ℕ} [Entailment.Disjunctive H] : H.logic.Disjunctive  := ⟨fun {_ _} h => disjunctive h⟩

end Hilbert


instance : (Logic.Int).Disjunctive := inferInstance


end LO.Propositional
