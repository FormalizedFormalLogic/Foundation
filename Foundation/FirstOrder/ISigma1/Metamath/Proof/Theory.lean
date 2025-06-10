import Foundation.FirstOrder.ISigma1.Metamath.Formula.Functions
import Foundation.FirstOrder.ISigma1.Metamath.Formula.Iteration

namespace LO.ISigma1.Metamath

open FirstOrder Arith PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Metamath.Language V} {pL : LDef} [Metamath.Language.Defined L pL]

section theory

variable (L)

structure _root_.LO.FirstOrder.Arith.LDef.TDef (pL : LDef) where
  ch : 𝚫₁.Semisentence 1

protected structure Language.Theory (L : Metamath.Language V) {pL : LDef} [Metamath.Language.Defined L pL] where
  set : Set V

instance : Membership V L.Theory := ⟨fun T x ↦ x ∈ T.set⟩

instance : HasSubset L.Theory := ⟨fun T U ↦ T.set ⊆ U.set⟩

omit [V ⊧ₘ* 𝐈𝚺₁] in
lemma Language.Theory.mem_def {T : L.Theory} {p} : p ∈ T ↔ p ∈ T.set := by rfl

variable {L}

namespace Language.Theory

protected class Defined (T : L.Theory) (pT : outParam pL.TDef) where
  defined : 𝚫₁-Predicate (· ∈ T.set) via pT.ch

variable (T : L.Theory) {pT : pL.TDef} [T.Defined pT]

instance mem_defined : 𝚫₁-Predicate (· ∈ T) via pT.ch := Defined.defined

instance mem_definable : 𝚫₁-Predicate (· ∈ T) := (mem_defined T).to_definable

end Language.Theory

end theory

end LO.ISigma1.Metamath
