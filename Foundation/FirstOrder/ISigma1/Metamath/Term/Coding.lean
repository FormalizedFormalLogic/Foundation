import Foundation.FirstOrder.ISigma1.Metamath.Term.Typed

open Encodable LO FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath

namespace LO.ISigma1.Metamath

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

lemma nat_cast_empty : ((∅ : ℕ) : V) = ∅ := rfl

noncomputable def finArrowToVec : {k : ℕ} → (Fin k → V) → V
  |     0, _ => 0
  | k + 1, v => v 0 ∷ finArrowToVec (k := k) (v ·.succ)

/-- quasi-quotation rather than Godel quotation -/
noncomputable instance : GoedelQuote (Fin k → V) V := ⟨finArrowToVec⟩

lemma quote_matrix_def (v : Fin k → V) : ⌜v⌝ = finArrowToVec v := rfl

@[simp] lemma quote_nil : (⌜(![] : Fin 0 → V)⌝ : V) = 0 := rfl

@[simp] lemma quote_singleton (a : V) : (⌜![a]⌝ : V) = ?[a] := rfl

@[simp] lemma quote_doubleton (a b : V) : (⌜![a, b]⌝ : V) = ?[a, b] := rfl

@[simp] lemma quote_matrix_empty (v : Fin 0 → V) :
    (⌜v⌝ : V) = 0 := by rfl

lemma quote_matrix_succ (v : Fin (k + 1) → V) :
    (⌜v⌝ : V) = v 0 ∷ ⌜fun i : Fin k ↦ v i.succ⌝ := by simp [quote_matrix_def, finArrowToVec]

@[simp] lemma quote_cons (v : Fin k → V) (a : V) :
    (⌜a :> v⌝ : V) = a ∷ ⌜v⌝  := by simp [quote_matrix_succ]

@[simp] lemma quote_matrix_inj (v w : Fin k → V) : (⌜v⌝ : V) = ⌜w⌝ ↔ v = w := by
  induction' k with k ih
  · simp [Matrix.empty_eq]
  · simp only [quote_matrix_succ, cons_inj, ih]
    constructor
    · rintro ⟨h0, hs⟩
      funext x; cases' x using Fin.cases with x
      · exact h0
      · exact congr_fun hs x
    · rintro rfl; simp

@[simp] lemma quote_lh (v : Fin k → V) : len (⌜v⌝ : V) = k := by
  induction' k with k ih <;> simp [quote_matrix_succ, Matrix.empty_eq, *]

@[simp] lemma quote_nth_fin (v : Fin k → V) (i : Fin k) : (⌜v⌝ : V).[i] = v i := by
  induction' k with k ih
  · exact i.elim0
  · cases' i using Fin.cases with i <;> simp [quote_matrix_succ, ih]

@[simp] lemma quote_matrix_absolute (v : Fin k → ℕ) : ((⌜v⌝ : ℕ) : V) = ⌜fun i ↦ (v i : V)⌝ := by
  induction' k with k ih
  · simp
  · simp [quote_matrix_succ, ih, cons_absolute]

lemma quote_eq_vecToNat (v : Fin k → ℕ) : ⌜v⌝ = Matrix.vecToNat v := by
  induction k
  case zero => simp
  case succ k ih =>
    simp [quote_matrix_succ, Matrix.vecToNat, cons, nat_pair_eq, Function.comp_def, ih]

section

variable {α : Type*} [Encodable α]

instance : GoedelQuote α V := ⟨fun x ↦ Encodable.encode x⟩

lemma quote_eq_coe_encode (x : α) : (⌜x⌝ : V) = Encodable.encode x := rfl

@[simp] lemma quote_nat (n : ℕ) : (⌜n⌝ : V) = n := rfl

lemma coe_quote (x : α) : ↑(⌜x⌝ : ℕ) = (⌜x⌝ : V) := by simp [quote_eq_coe_encode]

@[simp] lemma quote_quote (x : α) : (⌜(⌜x⌝ : ℕ)⌝ : V) = ⌜x⌝ := by simp [quote_eq_coe_encode]

lemma quote_eq_encode (x : α) : (⌜x⌝ : ℕ) = Encodable.encode x := by simp [quote_eq_coe_encode]

@[simp] lemma val_quote {ξ n e ε} (x : α) : Semiterm.valm V e ε (⌜x⌝ : FirstOrder.Semiterm ℒₒᵣ ξ n) = ⌜x⌝ := by
  simp [goedelNumber'_def, quote_eq_coe_encode, numeral_eq_natCast]

lemma numeral_quote (x : α) : Semiterm.Operator.numeral ℒₒᵣ (⌜x⌝ : ℕ) = (⌜x⌝ : FirstOrder.Semiterm ℒₒᵣ ξ n) := by simp [quote_eq_coe_encode]; rfl

@[simp] lemma quote_inj_iff {x y : α} : (⌜x⌝ : V) = ⌜y⌝ ↔ x = y := by simp [quote_eq_coe_encode]

end

end LO.ISigma1.Metamath

namespace LO.FirstOrder.Semiterm

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable]

variable (V)

lemma quote_eq_toNat (t : SyntacticSemiterm L n) : (⌜t⌝ : V) = toNat t := rfl

@[simp] lemma quote_bvar (z : Fin n) : ⌜(#z : SyntacticSemiterm L n)⌝ = ^#(z : V) := by
  simp [quote_eq_toNat, toNat, qqBvar, ←nat_pair_eq, nat_cast_pair]

@[simp] lemma quote_fvar (x : ℕ) : ⌜(&x : SyntacticSemiterm L n)⌝ = ^&(x : V) := by
  simp [quote_eq_toNat, toNat, qqFvar, ←nat_pair_eq, nat_cast_pair]

lemma quote_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    ⌜func f v⌝ = ^func (k : V) ⌜f⌝ ⌜fun i ↦ ⌜v i⌝⌝ := by
  simp [quote_eq_toNat, toNat, qqFunc, ←nat_pair_eq, nat_cast_pair, quote_func_def, quote_eq_vecToNat, ←quote_matrix_absolute]

@[simp] lemma codeIn_inj {n} {t u : SyntacticSemiterm L n} : (⌜t⌝ : V) = ⌜u⌝ ↔ t = u := by
  induction t generalizing u
  case bvar z => rcases u <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc, Fin.val_inj]
  case fvar x => rcases u <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc]
  case func k f v ih =>
    rcases u
    · simp [quote_bvar, quote_func, qqBvar, qqFunc]
    · simp [quote_fvar, quote_func, qqFvar, qqFunc]
    case func w =>
      simp only [quote_func, qqFunc, add_left_inj, pair_ext_iff, Nat.cast_inj, true_and, func.injEq,
        and_congr_right_iff]
      rintro rfl; simp only [quote_inj_iff, quote_matrix_inj, heq_eq_eq, and_congr_right_iff]; rintro rfl
      constructor
      · intro h; funext i; exact (ih i).mp (congr_fun h i)
      · rintro rfl; rfl

@[simp] lemma quote_zero (n) :
    (⌜(Semiterm.func Language.Zero.zero ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = 𝟎 := by
  simp [FirstOrder.Semiterm.quote_func, InternalArithmetic.zero, InternalArithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]; rfl

@[simp] lemma quote_zero' (n) : (⌜(‘0’ : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = 𝟎 := quote_zero V n

@[simp] lemma quote_one (n) :
    (⌜(Semiterm.func Language.One.one ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = 𝟏 := by
  simp [FirstOrder.Semiterm.quote_func, InternalArithmetic.one, InternalArithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]; rfl

@[simp] lemma quote_one' (n) : (⌜(‘1’ : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = 𝟏 := quote_one V n

@[simp] lemma quote_add (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiterm.func Language.Add.add ![t, u]⌝ : V) = (⌜t⌝ ^+ ⌜u⌝) := by simp [FirstOrder.Semiterm.quote_func]; rfl

@[simp] lemma quote_add' (t u : SyntacticSemiterm ℒₒᵣ n) : (⌜‘!!t + !!u’⌝ : V) = (⌜t⌝ ^+ ⌜u⌝) := quote_add V t u

@[simp] lemma quote_mul (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiterm.func Language.Mul.mul ![t, u]⌝ : V) = (⌜t⌝ ^* ⌜u⌝) := by simp [FirstOrder.Semiterm.quote_func]; rfl

@[simp] lemma quote_mul' (t u : SyntacticSemiterm ℒₒᵣ n) : (⌜‘!!t * !!u’⌝ : V) = (⌜t⌝ ^* ⌜u⌝) := quote_mul V t u

@[simp] lemma quote_absolute (t : SyntacticSemiterm L n) :
    ((⌜t⌝ : ℕ) : V) = ⌜t⌝ := by
  induction t <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc, nat_cast_pair, *]

lemma quote_eq_encode (t : SyntacticSemiterm L n) : ⌜t⌝ = Encodable.encode t := by
  induction t
  case bvar z => simp [encode_eq_toNat, toNat, quote_bvar, qqBvar, nat_pair_eq]
  case fvar z => simp [encode_eq_toNat, toNat, quote_fvar, qqFvar, nat_pair_eq]
  case func k f v ih =>
    simp [encode_eq_toNat, toNat, quote_func, qqFunc, nat_pair_eq, quote_func_def, quote_eq_vecToNat, ih]

end LO.FirstOrder.Semiterm

namespace LO.ISigma1.Metamath

open FirstOrder.Semiterm

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

@[simp] lemma semiterm_codeIn {n} (t : SyntacticSemiterm L n) :
    IsSemiterm (V := V) L n ⌜t⌝ := by
  induction t
  · simp [quote_bvar]
  · simp [quote_fvar]
  case func k f v ih =>
    simpa [quote_bvar, quote_fvar, quote_func]
    using IsSemitermVec.iff.mpr
      ⟨by simp, by
          rintro i hi
          rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
          simpa using ih i⟩

@[simp] lemma semitermVec_codeIn {k n} (v : Fin k → SyntacticSemiterm L n) :
    IsSemitermVec (V := V) L k n ⌜fun i ↦ ⌜v i⌝⌝ := IsSemitermVec.iff.mpr
  ⟨by simp, by intro i hi; rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩; simp⟩

@[simp] lemma isUTermVec_codeIn {k n} (v : Fin k → SyntacticSemiterm L n) :
    IsUTermVec (V := V) L k ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v |>.isUTerm

@[simp] lemma quote_termSubst {n m} (t : SyntacticSemiterm L n) (w : Fin n → SyntacticSemiterm L m) :
    (⌜Rew.substs w t⌝ : V) = termSubst L ⌜fun i ↦ ⌜w i⌝⌝ ⌜t⌝ := by
  induction t
  case bvar z => simp [quote_bvar]
  case fvar x => simp [quote_fvar]
  case func k f v ih =>
    have Hw : IsSemitermVec (V := V) L n m ⌜fun i ↦ ⌜w i⌝⌝ := semitermVec_codeIn w
    have Hv : IsSemitermVec (V := V) L k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, termSubst_func (codeIn_func_quote f) Hv.isUTerm]
    congr
    apply nth_ext (by simp [(Hw.termSubstVec Hv).lh])
    intro i hi
    have hi : i < k := by simpa [Hw.termSubstVec Hv |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termSubstVec Hv.isUTerm hi]
    simpa using ih i

lemma quote_termSubstVec {k n m} (w : Fin n → SyntacticSemiterm L m) (v : Fin k → SyntacticSemiterm L n) :
    (⌜fun i ↦ ⌜(Rew.substs w) (v i)⌝⌝ : V) = termSubstVec L ↑k ⌜fun i ↦ ⌜w i⌝⌝ ⌜fun i ↦ ⌜v i⌝⌝ := by
  have Hw : IsSemitermVec (V := V) L n m ⌜fun i ↦ ⌜w i⌝⌝ := semitermVec_codeIn w
  have Hv : IsSemitermVec (V := V) L k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
  apply nth_ext (by simp [Hw.termSubstVec Hv |>.lh])
  intro i hi
  have hi : i < k := by simpa [Hw.termSubstVec Hv |>.lh] using hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  simp [nth_termSubstVec Hv.isUTerm hi]

@[simp] lemma quote_termShift {n} (t : SyntacticSemiterm L n) :
    (⌜Rew.shift t⌝ : V) = termShift L ⌜t⌝ := by
  induction t
  case bvar => simp [quote_bvar]
  case fvar => simp [quote_fvar]
  case func k f v ih =>
    have Hv : IsSemitermVec (V := V) L k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, termShift_func (codeIn_func_quote f) Hv.isUTerm]
    congr
    apply nth_ext (by simp [Hv.termShiftVec |>.lh])
    intro i hi
    have hi : i < k := by simpa [Hv.termShiftVec |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termShiftVec Hv.isUTerm hi]
    simpa using ih i

lemma quote_termShiftVec {k n} (v : Fin k → SyntacticSemiterm L n) :
    (⌜fun i ↦ ⌜Rew.shift (v i)⌝⌝ : V) = termShiftVec (V := V) L k ⌜fun i ↦ ⌜v i⌝⌝ := by
  have Hv : IsSemitermVec (V := V) L k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
  apply nth_ext (by simp [Hv.termShiftVec |>.lh])
  intro i hi
  have hi : i < k := by simpa [Hv.termShiftVec |>.lh] using hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  simp [nth_termShiftVec Hv.isUTerm hi]

@[simp] lemma quote_termBShift {n} (t : SyntacticSemiterm L n) :
    (⌜Rew.bShift t⌝ : V) = termBShift (V := V) L ⌜t⌝ := by
  induction t
  case bvar => simp [quote_bvar]
  case fvar => simp [quote_fvar]
  case func k f v ih =>
    have Hv : IsSemitermVec (V := V) L k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, termBShift_func (codeIn_func_quote f) Hv.isUTerm]
    congr
    apply nth_ext (by simp [Hv.termBShiftVec |>.lh])
    intro i hi
    have hi : i < k := by simpa [Hv.termBShiftVec |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termBShiftVec Hv.isUTerm hi]
    simpa using ih i

@[simp] lemma InternalArithmetic.quote_numeral_eq_numeral (k : ℕ) :
    (⌜(↑k : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = InternalArithmetic.numeral (k : V) := by
  induction k
  case zero => simp
  case succ k ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    cases' k with k
    · simp
    · calc
        ⌜(‘↑(k + 1 + 1)’ : SyntacticSemiterm ℒₒᵣ n)⌝
        _ = ⌜(Operator.operator (Operator.numeral ℒₒᵣ (k + 1)) ![] : SyntacticSemiterm ℒₒᵣ n)⌝
          ^+ ⌜(Operator.operator op(1) ![] : SyntacticSemiterm ℒₒᵣ n)⌝ := by
          unfold Semiterm.numeral
          simp [Operator.numeral_succ, Matrix.fun_eq_vec_two]
        _ = numeral ((k + 1 : ℕ) : V) ^+ ↑𝟏 := by
          rw [←quote_one']
          congr
        _ = numeral ((k : V) + 1) ^+ ↑𝟏     := by rfl
        _ = numeral ((k + 1 : V) + 1)       := by simp

omit [L.LORDefinable] in
lemma quote_eterm_eq_quote_emb (t : FirstOrder.Semiterm L Empty n) : (⌜t⌝ : V) = (⌜Rew.embs t⌝ : V) := by
  simp [quote_eq_coe_encode]

@[simp] lemma InternalArithmetic.quote_numeral_eq_numeral' (k : ℕ) :
    (⌜(↑k : FirstOrder.Semiterm ℒₒᵣ Empty n)⌝ : V) = InternalArithmetic.numeral (k : V) := by
  simp [quote_eterm_eq_quote_emb]

@[simp] lemma quote_quote_eq_numeral {α : Type*} [Encodable α] {x : α} :
    (⌜(⌜x⌝ : FirstOrder.Semiterm ℒₒᵣ ℕ n)⌝ : V) = InternalArithmetic.numeral ⌜x⌝ := by
  simp [goedelNumber'_def]; simp [quote_eq_coe_encode]

end LO.ISigma1.Metamath

namespace LO.FirstOrder

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (V)

variable {n : ℕ}

namespace Semiterm

def typed_quote (t : SyntacticSemiterm L n) : Metamath.Semiterm V L n := ⟨⌜t⌝, by simp⟩

instance : GoedelQuote (SyntacticSemiterm L n) (Metamath.Semiterm V L n) := ⟨Semiterm.typed_quote V⟩

@[simp] lemma typed_quote_val (t : SyntacticSemiterm L n) : (⌜t⌝ : Metamath.Semiterm V L n).val = ⌜t⌝ := rfl

noncomputable def typed_quote_vec {k n} (v : Fin k → SyntacticSemiterm L n) : Metamath.SemitermVec V L k n := ⟨⌜fun i ↦ ⌜v i⌝⌝, by simp⟩

noncomputable instance {k n} : GoedelQuote (Fin k → SyntacticSemiterm L n) (Metamath.SemitermVec V L k n) := ⟨Semiterm.typed_quote_vec V⟩

@[simp] lemma typed_quote_vec_val (v : Fin k → SyntacticSemiterm L n) : (⌜v⌝ : Metamath.SemitermVec V L k n).val = ⌜fun i ↦ ⌜v i⌝⌝ := rfl

@[simp] lemma typed_quote_bvar (z : Fin n) :
    (⌜(#z : SyntacticSemiterm L n)⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.bvar L ↑z := by ext; simp [quote_bvar]

@[simp] lemma typed_quote_fvar (x : ℕ) :
    (⌜(&x : SyntacticSemiterm L n)⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.fvar L (x : V) := by ext; simp [quote_fvar]

lemma typed_quote_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜func f v⌝ : Metamath.Semiterm V L n) =
      Metamath.Semiterm.func (V := V) (L := L) (k := k) (f := ⌜f⌝) (by simp) ⌜v⌝ := by ext; simp [quote_func, Metamath.Semiterm.func]

@[simp] lemma typed_quote_zero (n : ℕ) :
    (⌜(func Language.Zero.zero ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ↑(0 : V) := by ext; simp

@[simp] lemma typed_quote_one (n : ℕ) :
    (⌜(func Language.One.one ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ↑(1 : V) := by ext; simp

@[simp] lemma typed_quote_add (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Add.add v⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜v 0⌝ + ⌜v 1⌝ := by ext; rw [Matrix.fun_eq_vec_two (v := v)]; simp [quote_add]

@[simp] lemma typed_quote_mul (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Mul.mul v⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜v 0⌝ * ⌜v 1⌝ := by ext; rw [Matrix.fun_eq_vec_two (v := v)]; simp

end Semiterm
