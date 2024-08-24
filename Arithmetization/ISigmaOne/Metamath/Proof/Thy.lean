import Arithmetization.ISigmaOne.Metamath.Formula.Functions
import Arithmetization.ISigmaOne.Metamath.Formula.Iteration

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section theory

variable (L)

structure _root_.LO.FirstOrder.Arith.LDef.TDef (pL : LDef) where
  ch : 𝚫₁.Semisentence 1

protected structure Language.Theory (L : Arith.Language V) {pL : LDef} [Arith.Language.Defined L pL] where
  set : Set V

instance : Membership V L.Theory := ⟨fun x T ↦ x ∈ T.set⟩

instance : HasSubset L.Theory := ⟨fun T U ↦ T.set ⊆ U.set⟩

variable {L}

namespace Language.Theory

protected class Defined (T : L.Theory) (pT : outParam pL.TDef) where
  defined : 𝚫₁-Predicate (· ∈ T.set) via pT.ch

variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]

instance mem_defined : 𝚫₁-Predicate (· ∈ T) via pT.ch := Defined.defined

instance mem_definable : 𝚫₁-Predicate (· ∈ T) := (mem_defined T).to_definable

end Language.Theory

end theory
