import Arithmetization.ISigmaOne.Metamath.Term
import Arithmetization.Definability.Absoluteness

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

def finArrowToSeq : {k : ℕ} → (Fin k → M) → M
  | 0,     _ => ∅
  | k + 1, v => finArrowToSeq (k := k) (fun i ↦ v i.castSucc) ⁀' (v k)

@[simp] lemma finArrowToSeq_nil : finArrowToSeq (![] : Fin 0 → M) = ∅ := rfl

@[simp] lemma finArrowToSeq_singleton (a : M) : finArrowToSeq ![a] = !⟦a⟧ := rfl

@[simp] lemma finArrowToSeq_doubleton (a b : M) : finArrowToSeq ![a, b] = !⟦a, b⟧ := rfl

@[simp] lemma finArrowToSeq_cons (v : Fin k → M) (a : M) :
    finArrowToSeq (v <: a) = finArrowToSeq v ⁀' a  := by simp [finArrowToSeq]

@[simp] lemma finArrowToSeq_seq (v : Fin k → M) : Seq (finArrowToSeq v) := by
  induction' k with k ih <;> simp [finArrowToSeq, Matrix.empty_eq]
  exact ih (fun i ↦ v i.castSucc) |>.seqCons (v (Fin.last k))

@[simp] lemma finArrowToSeq_lh (v : Fin k → M) : lh (finArrowToSeq v) = k := by
  induction' k with k ih <;> simp [finArrowToSeq, Matrix.empty_eq, *]

lemma mem_finArrowToSeq_iff {v : Fin k → M} : ⟪i, x⟫ ∈ finArrowToSeq v ↔ ∃ i' : Fin k, i' = i ∧ v i' = x := by
  induction' k with k ih <;> simp [finArrowToSeq, Matrix.empty_eq]
  simp only [mem_seqCons_iff, finArrowToSeq_lh, ih]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩)
    · exact ⟨Fin.last k, by simp⟩
    · exact ⟨i, by simp⟩
  · rintro ⟨i, rfl, rfl⟩
    cases i using Fin.lastCases
    case last => simp
    case cast i =>
      right; exact ⟨i, by simp⟩

lemma nat_cast_empty : ((∅ : ℕ) : M) = ∅ := rfl

lemma finArrowToSeq_absolute (v : Fin k → ℕ) : ((finArrowToSeq v : ℕ) : M) = finArrowToSeq fun i ↦ (v i : M) := by
  induction' k with k ih
  · simp [finArrowToSeq, nat_cast_empty]
  · simp [finArrowToSeq, ih, seqCons_absolute]

end LO.Arith

namespace LO.FirstOrder.Semiterm

open LO.Arith FirstOrder.Arith

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (M)

def codeIn {n} : SyntacticSemiterm L n → M
  | #z                    => ^#z
  | &x                    => ^&x
  | func (arity := k) f v => ^func (k : M) (Encodable.encode f) (finArrowToSeq fun i ↦ (v i).codeIn)

@[simp] lemma codeIn_bvar (z : Fin n) : (#z : SyntacticSemiterm L n).codeIn M = ^#(z : M) := rfl

@[simp] lemma codeIn_fvar (x : ℕ) : (&x : SyntacticSemiterm L n).codeIn M = ^&(x : M) := rfl

@[simp] lemma codeIn_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (func f v).codeIn M = ^func (k : M) (Encodable.encode f) (finArrowToSeq fun i ↦ (v i).codeIn M) := rfl

end LO.FirstOrder.Semiterm

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

@[simp] lemma isSemiterm_codeIn {n} (t : SyntacticSemiterm L n) :
    (L.codeIn M).IsSemiterm n (t.codeIn M) := by
  induction t <;> simp
  case func k f v ih =>
    exact IsSemiterm.func (by simp) (by simp) (by simp) (by
      simp only [mem_finArrowToSeq_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      rintro _ i rfl; exact ih i)

/-- TOFO: move to PeanoMinus -/
@[simp] lemma nat_cast_inj {n m : ℕ} : (n : M) = m ↔ n = m := by
  induction' n with n ih
  · cases m <;> simp
  · cases m <;> simp

lemma termSubst_codeIn {n m} (t : SyntacticSemiterm L n) (v : Fin n → SyntacticSemiterm L m) :
    (Rew.substs v t).codeIn M = (L.codeIn M).termSubst n m (finArrowToSeq fun i ↦ (v i).codeIn M) (t.codeIn M) := by
  induction t
  case bvar z =>
    simp; symm
    exact termSubst_bvar
      (by simp [Language.TermSeq, mem_finArrowToSeq_iff]) (by simp)
      (by simp [mem_finArrowToSeq_iff]; exact ⟨z, by simp⟩)
  case fvar x =>
    simp; symm
    exact termSubst_fvar (by simp [Language.TermSeq, mem_finArrowToSeq_iff]) _
  case func k f v ih =>
    simp; symm
    apply termSubst_func (by simp [Language.TermSeq, mem_finArrowToSeq_iff]) (by simp) (by simp) (by simp)
      (by simp [mem_finArrowToSeq_iff]) (by simp) (by simp) (by simp [mem_finArrowToSeq_iff])
    simp only [mem_finArrowToSeq_iff, forall_exists_index, and_imp]
    rintro _ _ _ i rfl rfl j hij rfl
    rcases Fin.val_inj.mp <| nat_cast_inj.mp hij
    exact Eq.symm (ih i)

lemma termShift_codeIn {n} (t : SyntacticSemiterm L n) :
    (Rew.shift t).codeIn M = (L.codeIn M).termShift n (t.codeIn M) := by
  induction t
  case bvar => simp [termShift_bvar]
  case fvar => simp
  case func k f v ih =>
    simp; symm
    apply termShift_func (by simp) (by simp) (by simp) (by simp [mem_finArrowToSeq_iff])
      (by simp) (by simp) (by simp [mem_finArrowToSeq_iff])
    simp only [mem_finArrowToSeq_iff, forall_exists_index, and_imp]
    rintro _ _ _ i rfl rfl j hij rfl
    rcases Fin.val_inj.mp <| nat_cast_inj.mp hij
    exact Eq.symm (ih i)

end LO.Arith

end
