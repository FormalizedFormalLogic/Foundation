module

public import Foundation.ProvabilityLogic.Formula.Basic

/-!
# Logics

A logic is a set of modal formulas.
-/

@[expose] public section

namespace FFL.ProvabilityLogic

abbrev Logic (α : Type*) := Set (Formula α)

end FFL.ProvabilityLogic

end
