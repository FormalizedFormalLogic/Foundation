import Arithmetization.ISigmaOne.Metamath.Term
import Arithmetization.Definability.Absoluteness

noncomputable section

namespace LO.FirstOrder

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

namespace Arith.Model

def finArrowToSeq : {k : ℕ} → (Fin k → M) → M
  | 0,     _ => ∅
  | k + 1, v => finArrowToSeq (k := k) (fun i ↦ v i) ⁀' (v k)

@[simp] lemma finArrowToSeq_nil : finArrowToSeq (![] : Fin 0 → M) = ∅ := rfl

@[simp] lemma finArrowToSeq_singleton (a : M) : finArrowToSeq ![a] = !⟨a⟩ := rfl

@[simp] lemma finArrowToSeq_doubleton (a b : M) : finArrowToSeq ![a, b] = !⟨a, b⟩ := rfl

@[simp] lemma finArrowToSeq_cons (v : Fin k → M) (a : M) :
    finArrowToSeq (v <: a) = finArrowToSeq v ⁀' a  := by simp [finArrowToSeq]

lemma nat_cast_empty : ((∅ : ℕ) : M) = ∅ := rfl

lemma finArrowToSeq_absolute (v : Fin k → ℕ) : ((finArrowToSeq v : ℕ) : M) = finArrowToSeq fun i ↦ (v i : M) := by
  induction' k with k ih
  · simp [finArrowToSeq, nat_cast_empty]
  · simp [finArrowToSeq, ih, seqCons_absolute]

end Arith.Model

namespace Semiterm

open Arith Model

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]
  [DefinableLanguage L] [DefinableLanguage.T L ≼ 𝐏𝐀⁻]

def codeInModel {n} : SyntacticSemiterm L n → M
  | #z                    => ^#z
  | &x                    => ^&x
  | func (arity := k) f v => ^func (k : M) (Encodable.encode f) (finArrowToSeq fun i ↦ (v i).codeInModel)

end Semiterm

end LO.FirstOrder

end
