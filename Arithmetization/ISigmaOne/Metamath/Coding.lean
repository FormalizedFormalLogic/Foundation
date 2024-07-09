import Arithmetization.ISigmaOne.Metamath.Formula.Functions
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

/-- TOFO: move to PeanoMinus -/
@[simp] lemma nat_cast_inj {n m : ℕ} : (n : M) = (m : M) ↔ n = m := by
  induction' n with n ih
  · cases m <;> simp
  · cases m <;> simp

@[simp] lemma znth_finArrowToSeq_fin {v : Fin k → M} (i : Fin k) : znth (finArrowToSeq v) i = v i :=
  (finArrowToSeq_seq v).znth_eq_of_mem (by simp [mem_finArrowToSeq_iff, Fin.val_inj])

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

@[simp] lemma semiterm_codeIn {n} (t : SyntacticSemiterm L n) :
    (L.codeIn M).Semiterm n (t.codeIn M) := by
  induction t <;> simp
  case func k f v ih =>
    exact ⟨by simp, by simp, by simp [mem_finArrowToSeq_iff]; rintro _ i rfl; exact ih i⟩

lemma termSubst_codeIn {n m} (t : SyntacticSemiterm L n) (w : Fin n → SyntacticSemiterm L m) :
    (Rew.substs w t).codeIn M = (L.codeIn M).termSubst n m (finArrowToSeq fun i ↦ (w i).codeIn M) (t.codeIn M) := by
  induction t
  case bvar z => simp
  case fvar x => simp
  case func k f v ih =>
    have Hw : (L.codeIn M).SemitermSeq n m (finArrowToSeq fun i ↦ Semiterm.codeIn M (w i)) := ⟨by simp, by simp, by simp [mem_finArrowToSeq_iff]⟩
    have Hv : (L.codeIn M).SemitermSeq k n (finArrowToSeq fun i ↦ Semiterm.codeIn M (v i)) := ⟨by simp, by simp, by simp [mem_finArrowToSeq_iff]⟩
    simp only [Rew.func, Semiterm.codeIn_func, codeIn_func_encode, termSubst_func (codeIn_func_encode f) Hv]
    congr
    apply Seq.lh_ext (by simp) (Hw.termSubstSeq Hv |>.seq) (by simp [←Hw.termSubstSeq Hv |>.lh])
    simp only [mem_finArrowToSeq_iff, forall_exists_index, and_imp]
    rintro _ x₁ x₂ i rfl rfl h
    have : (L.codeIn M).termSubst n m (finArrowToSeq fun i ↦ Semiterm.codeIn M (w i)) (Semiterm.codeIn M (v i)) = x₂ := by
      simpa [mem_finArrowToSeq_iff, Fin.val_inj] using Language.SemitermSeq.of_mem_termSubstSeq Hv h
    rcases this; exact ih i

lemma termShift_codeIn {n} (t : SyntacticSemiterm L n) :
    (Rew.shift t).codeIn M = (L.codeIn M).termShift n (t.codeIn M) := by
  induction t
  case bvar => simp [termShift_bvar]
  case fvar => simp
  case func k f v ih =>
    have Hv : (L.codeIn M).SemitermSeq k n (finArrowToSeq fun i ↦ Semiterm.codeIn M (v i)) := ⟨by simp, by simp, by simp [mem_finArrowToSeq_iff]⟩
    simp only [Rew.func, Semiterm.codeIn_func, codeIn_func_encode, termShift_func (codeIn_func_encode f) Hv]
    congr
    apply Seq.lh_ext (by simp) (Hv.termShiftSeq |>.seq) (by simp [←Hv.termShiftSeq |>.lh])
    simp only [mem_finArrowToSeq_iff, forall_exists_index, and_imp]
    rintro _ x₁ x₂ i rfl rfl h
    have : (L.codeIn M).termShift n (Semiterm.codeIn M (v i)) = x₂ := by
      simpa [mem_finArrowToSeq_iff, Fin.val_inj] using Language.SemitermSeq.of_mem_termShiftSeq Hv h
    rcases this; exact ih i

end LO.Arith

end
