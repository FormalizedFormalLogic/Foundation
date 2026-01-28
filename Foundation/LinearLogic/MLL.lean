module
public import Foundation.Logic.Entailment

/-!
# Multiplicative linear logic
-/

@[expose] public section

namespace LO.LinearLogic

inductive MLLFormula where
  | atom : α → MLLFormula
  | natom : α → MLLFormula
  | one : MLLFormula
  | bot : MLLFormula
  | tensor : MLLFormula → MLLFormula → MLLFormula
  | par : MLLFormula → MLLFormula → MLLFormula

namespace MLLFormula

instance : One MLLFormula := ⟨one⟩

instance : Bot MLLFormula := ⟨bot⟩

instance : HasTensor MLLFormula := ⟨tensor⟩

instance : HasPar MLLFormula := ⟨par⟩

variable {α : Type*}



end MLLFormula

end LO.LinearLogic
