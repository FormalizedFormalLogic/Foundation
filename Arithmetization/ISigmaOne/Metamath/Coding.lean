import Arithmetization.ISigmaOne.Metamath.Language

namespace LO.FirstOrder

namespace Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

noncomputable def finArrowToSeq : {k : ℕ} → (Fin k → M) → M
  | 0,     _ => ∅
  | k + 1, v => finArrowToSeq (k := k) (fun i ↦ v i) ⁀' (v k)

noncomputable def listToSeqRev : List M → M
  | []      => ∅
  | x :: xs => listToSeqRev xs ⁀' x

noncomputable def listToSeq (l : List M) : M := listToSeqRev l.reverse

end Model

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]
  {ξ : Type*} [Encodable ξ] [ℕ ⊧ₘ* 𝐈𝚺₁]

noncomputable def termEncode : Semiterm L ξ n → ℕ
  | #z => Nat.pair 0 z + 1
  | &x => Nat.pair 1 (Encodable.encode x) + 1
  | Semiterm.func (arity := k) f v =>
  Nat.pair 2 (Nat.pair k (Nat.pair (Encodable.encode f) (Model.finArrowToSeq (fun i ↦ termEncode (v i))))) + 1

end Arith

end LO.FirstOrder
