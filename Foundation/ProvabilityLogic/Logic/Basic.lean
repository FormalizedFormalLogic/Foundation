module

public import Foundation.ProvabilityLogic.Formula.Basic

/-!
# Logics
-/

@[expose] public section

namespace FFL.ProvabilityLogic

abbrev Logic (α : Type*) := Set (Formula α)

end FFL.ProvabilityLogic

end
