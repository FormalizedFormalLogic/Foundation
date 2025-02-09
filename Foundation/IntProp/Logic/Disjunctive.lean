import Foundation.IntProp.Logic.Basic
import Foundation.IntProp.Kripke.Hilbert.Int.DP

namespace LO.IntProp

protected class Logic.Disjunctive (L : Logic) where
  disjunctive {φ ψ} : φ ⋎ ψ ∈ L → φ ∈ L ∨ ψ ∈ L


namespace Hilbert

open System

instance {H : Hilbert ℕ} [System.Disjunctive H] : H.logic.Disjunctive  := ⟨fun {_ _} h => disjunctive h⟩

end Hilbert

instance : (Logic.Int).Disjunctive := inferInstance

end LO.IntProp
