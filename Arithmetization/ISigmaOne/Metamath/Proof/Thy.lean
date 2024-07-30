import Arithmetization.ISigmaOne.Metamath.Formula.Functions
import Arithmetization.ISigmaOne.Metamath.Formula.Iteration

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section theory

variable (L)

structure _root_.LO.FirstOrder.Arith.LDef.TDef (pL : LDef) where
  ch : HSemisentence ℒₒᵣ 1 𝚫₁

protected structure Language.Theory (L : Arith.Language V) {pL : LDef} [Arith.Language.Defined L pL] where
  set : Set V

instance : Membership V L.Theory := ⟨fun x T ↦ x ∈ T.set⟩

variable {L}

namespace Language.Theory

protected class Defined (T : L.Theory) (pT : outParam pL.TDef) where
  defined : 𝚫₁-Predicate (· ∈ T.set) via pT.ch

variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]

instance mem_defined : 𝚫₁-Predicate (· ∈ T) via pT.ch := Defined.defined

instance mem_definable : 𝚫₁-Predicate (· ∈ T) := (mem_defined T).to_definable

end Language.Theory

end theory
