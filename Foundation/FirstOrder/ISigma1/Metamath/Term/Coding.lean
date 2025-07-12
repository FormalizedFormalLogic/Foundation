import Foundation.FirstOrder.ISigma1.Metamath.Term.Typed

open Encodable LO FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath

/-
namespace LO.ISigma1.Metamath

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]


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
-/

namespace LO.FirstOrder.Semiterm

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (V) {n : ℕ}

noncomputable def typedQuote : SyntacticSemiterm L n → Metamath.Semiterm V L n
  |       #x => Metamath.Semiterm.bvar x
  |       &x => Metamath.Semiterm.fvar x
  | func f v => Metamath.Semiterm.func f fun i ↦ (v i).typedQuote

noncomputable instance : GoedelQuote (SyntacticSemiterm L n) (Metamath.Semiterm V L n) where
  quote := typedQuote V

variable {V}

@[simp] lemma typed_quote_bvar (x : Fin n) :
    (⌜(#x : SyntacticSemiterm L n)⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.bvar x := rfl

@[simp] lemma typed_quote_fvar (x : ℕ) :
    (⌜(&x : SyntacticSemiterm L n)⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.fvar ↑x := rfl

@[simp] lemma typed_quote_func (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜func f v⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.func f fun i ↦ ⌜v i⌝ := rfl

@[simp] lemma typed_quote_shift (t : SyntacticSemiterm L n) :
    (⌜Rew.shift t⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.shift (⌜t⌝ : Metamath.Semiterm V L n) := by
  induction t <;> simp [Rew.func, *]; rfl

@[simp] lemma typed_quote_bShift (t : SyntacticSemiterm L n) :
    (⌜Rew.bShift t⌝ : Metamath.Semiterm V L (n + 1)) = Metamath.Semiterm.bShift (⌜t⌝ : Metamath.Semiterm V L n) := by
  induction t <;> simp [Rew.func, *]; rfl

@[simp] lemma typed_quote_substs {n m} (t : SyntacticSemiterm L n) (w : Fin n → SyntacticSemiterm L m) :
    (⌜Rew.substs w t⌝ : Metamath.Semiterm V L m) = Metamath.Semiterm.substs (fun i ↦ ⌜w i⌝) ⌜t⌝ := by
  induction t <;> simp [Rew.func, *]; rfl

open InternalArithmetic

@[simp] lemma typed_quote_add (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(‘!!t + !!u’ : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜t⌝ + ⌜u⌝ := rfl

@[simp] lemma typed_quote_mul (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(‘!!t * !!u’ : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜t⌝ * ⌜u⌝ := rfl

lemma typed_quote_numeral_eq_numeral_one :
    (⌜((1 : ℕ) : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = typedNumeral 1 := by
  simp [InternalArithmetic.typedNumeral,
    InternalArithmetic.one, InternalArithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
  rfl

@[simp] lemma typed_quote_numeral_eq_numeral (k : ℕ) :
    (⌜(↑k : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = typedNumeral ↑k := by
  match k with
  |         0 =>
    simp [InternalArithmetic.typedNumeral,
      InternalArithmetic.zero, InternalArithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
    rfl
  |         1 => simp [typed_quote_numeral_eq_numeral_one]
  | k + 1 + 1 =>
    calc (⌜(↑(k + 1 + 1) : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n)
      _ = ⌜(↑(k + 1) : SyntacticSemiterm ℒₒᵣ n)⌝ + ⌜((1 : ℕ) : SyntacticSemiterm ℒₒᵣ n)⌝ := rfl
      _ = typedNumeral ↑(k + 1) + typedNumeral 1 := by simp [typed_quote_numeral_eq_numeral (k + 1), typed_quote_numeral_eq_numeral_one]
      _ = typedNumeral (↑k + 1 + 1)              := by simp

lemma typed_quote_inj {t u : SyntacticSemiterm L n} : (⌜t⌝ : Metamath.Semiterm V L n) = ⌜u⌝ → t = u :=
  match t, u with
  |         #x,         #y => by simp
  |         &x,         &y => by simp
  | func f₁ v₁, func f₂ v₂ => by
    simp only [typed_quote_func, Metamath.Semiterm.func, Semiterm.mk.injEq, qqFunc_inj,
      Nat.cast_inj, func.injEq, and_imp]
    rintro rfl
    simp only [quote_func_inj, heq_eq_eq, true_and]
    rintro rfl
    suffices ((fun i ↦ ⌜v₁ i⌝) = fun i ↦ ⌜v₂ i⌝) → v₁ = v₂ by
      simpa [←SemitermVec.val_inj]
    intro h
    ext i
    exact typed_quote_inj (congr_fun h i)
  |         #_,         &_
  |         #_,   func _ _
  |         &_,         #_
  |         &_,   func _ _
  |   func _ _,         #_
  |   func _ _,         &_ => by simp [Metamath.Semiterm.bvar, Metamath.Semiterm.fvar, Metamath.Semiterm.func, qqBvar, qqFvar, qqFunc]

@[simp] lemma typed_quote_inj_iff {t u : SyntacticSemiterm L n} :
    (⌜t⌝ : Metamath.Semiterm V L n) = ⌜u⌝ ↔ t = u := ⟨typed_quote_inj, by rintro rfl; rfl⟩

noncomputable instance : GoedelQuote (SyntacticSemiterm L n) V where
  quote t := (⌜t⌝ : Metamath.Semiterm V L n).val

def quote_def (t : SyntacticSemiterm L n) : (⌜t⌝ : V) = (⌜t⌝ : Metamath.Semiterm V L n).val := rfl

private lemma quote_eq_encode'_aux (v : Fin k → Semiterm L ℕ n)
    (H : ∀ i, (⌜v i⌝ : Metamath.Semiterm V L n).val = encode ↑(v i)) :
    (SemitermVec.val fun i ↦ (⌜v i⌝ : Metamath.Semiterm V L n)) = ↑(Matrix.vecToNat fun i ↦ encode (v i)) := by
  induction k
  case zero => simp
  case succ k ih =>
    suffices
        (⌜v 0⌝ : Metamath.Semiterm V L n).val = encode ↑(v 0) ∧
        SemitermVec.val (fun i ↦ ⌜v i.succ⌝) = ↑(Matrix.vecToNat fun i ↦ encode (v i.succ) : V) by
      simpa [Matrix.vecToNat, coe_pair_eq_pair_coe, cons_def, Matrix.vecHead, Matrix.vecTail, Function.comp_def]
    constructor
    · exact H 0
    · exact ih (fun i ↦ v i.succ) (fun i ↦ by simpa using H i.succ)

lemma quote_eq_encode (t : SyntacticSemiterm L n) : (⌜t⌝ : V) = ↑(encode t) := by
  match t with
  |       #x => simp [quote_def, encode_eq_toNat, toNat, qqBvar, coe_pair_eq_pair_coe]
  |       &x => simp [quote_def, encode_eq_toNat, toNat, qqFvar, coe_pair_eq_pair_coe]
  | func f v =>
    suffices (⌜f⌝ : V) = ↑(encode f) ∧ (SemitermVec.val (V := V) fun i ↦ ⌜v i⌝) = ↑(Matrix.vecToNat fun i ↦ encode (v i)) by
      simpa [quote_def, encode_eq_toNat, toNat, Metamath.Semiterm.func, qqFunc, coe_pair_eq_pair_coe]
    constructor
    · rfl
    · exact quote_eq_encode'_aux _ fun i ↦ quote_eq_encode (v i)

lemma quote_eq_encode' (v : Fin k → Semiterm L ℕ n) :
    (SemitermVec.val fun i ↦ (⌜v i⌝ : Metamath.Semiterm V L n)) = ↑(Matrix.vecToNat fun i ↦ encode (v i)) :=
  quote_eq_encode'_aux _ fun i ↦ quote_eq_encode (v i)

lemma quote_eq_encode_standard (t : SyntacticSemiterm L n) : (⌜t⌝ : ℕ) = encode t := by simp [quote_eq_encode]

variable (V)

noncomputable instance : GoedelQuote (Semiterm L Empty n) (Metamath.Semiterm V L n) where
  quote t := ⌜(Rew.emb t : SyntacticSemiterm L n)⌝

variable {V}

def empty_typed_quote_def (t : Semiterm L Empty n) :
    (⌜t⌝ : Metamath.Semiterm V L n) = ⌜(Rew.emb t : SyntacticSemiterm L n)⌝ := rfl

@[simp] lemma empty_typed_quote_bvar (x : Fin n) :
    (⌜(#x : Semiterm L Empty n)⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.bvar x := rfl

@[simp] lemma empty_typed_quote_func (f : L.Func k) (v : Fin k → Semiterm L Empty n) :
    (⌜func f v⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.func f fun i ↦ ⌜v i⌝ := rfl

@[simp] lemma empty_typed_quote_add (t u : Semiterm ℒₒᵣ Empty n) :
    (⌜(‘!!t + !!u’ : Semiterm ℒₒᵣ Empty n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜t⌝ + ⌜u⌝ := rfl

@[simp] lemma empty_typed_quote_mul (t u : Semiterm ℒₒᵣ Empty n) :
    (⌜(‘!!t * !!u’ : Semiterm ℒₒᵣ Empty n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜t⌝ * ⌜u⌝ := rfl

@[simp] lemma empty_typed_quote_numeral_eq_numeral (k : ℕ) :
    (⌜(↑k : Semiterm ℒₒᵣ Empty n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = typedNumeral ↑k := by
  simp [empty_typed_quote_def]

noncomputable instance : GoedelQuote (Semiterm L Empty n) V where
  quote t := ⌜(Rew.emb t : SyntacticSemiterm L n)⌝

lemma empty_quote_def (t : Semiterm L Empty n) : (⌜t⌝ : V) = ⌜(Rew.emb t : SyntacticSemiterm L n)⌝ := rfl

def empty_quote_eq (t : Semiterm L Empty n) : (⌜t⌝ : V) = (⌜t⌝ : Metamath.Semiterm V L n).val := rfl

lemma empty_quote_eq_encode (t : Semiterm L Empty n) : (⌜t⌝ : V) = ↑(encode t) := by simp [empty_quote_def, quote_eq_encode]


/-
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
-/

end LO.FirstOrder.Semiterm

/-
namespace LO.ISigma1.Metamath

open FirstOrder.Semiterm

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

@[simp] lemma semiterm_codeIn {n} (t : SyntacticSemiterm L n) :
    IsSemiterm (V := V) L n ⌜t⌝ := by simp [quote_def]

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

instance : GoedelQuote (Semiterm L Empty n) (Metamath.Semiterm V L n) := ⟨fun t ↦ ⌜Rew.embs t⌝⟩

@[simp] lemma typed_quote_val (t : SyntacticSemiterm L n) : (⌜t⌝ : Metamath.Semiterm V L n).val = ⌜t⌝ := rfl

lemma empty_typed_quote_def (t : Semiterm L Empty n) : (⌜t⌝ : Metamath.Semiterm V L n) = ⌜Rew.embs t⌝ := rfl

@[simp] lemma typed_quote_bvar (z : Fin n) :
    (⌜(#z : SyntacticSemiterm L n)⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.bvar z := by ext; simp [quote_bvar]

@[simp] lemma typed_quote_fvar (x : ℕ) :
    (⌜(&x : SyntacticSemiterm L n)⌝ : Metamath.Semiterm V L n) = Metamath.Semiterm.fvar (x : V) := by ext; simp [quote_fvar]

lemma typed_quote_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜func f v⌝ : Metamath.Semiterm V L n) =
      Metamath.Semiterm.func (V := V) (L := L) (k := k) (f := f) (fun i ↦ ⌜v i⌝) := by ext; simp [quote_func, Metamath.Semiterm.func]

@[simp] lemma typed_quote_zero (n : ℕ) :
    (⌜(func Language.Zero.zero ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ↑(0 : V) := by ext; simp

@[simp] lemma typed_quote_one (n : ℕ) :
    (⌜(func Language.One.one ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ↑(1 : V) := by ext; simp

@[simp] lemma typed_quote_add (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Add.add v⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜v 0⌝ + ⌜v 1⌝ := by ext; rw [Matrix.fun_eq_vec_two (v := v)]; simp [quote_add]

@[simp] lemma typed_quote_mul (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Mul.mul v⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜v 0⌝ * ⌜v 1⌝ := by ext; rw [Matrix.fun_eq_vec_two (v := v)]; simp

/-! code in arithmetic -/

@[simp] lemma typed_quote_zero' :
    (⌜(‘0’  : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ↑(0 : V) := by ext; simp

@[simp] lemma typed_quote_one' :
    (⌜(‘1’ : SyntacticSemiterm ℒₒᵣ n)⌝ : Metamath.Semiterm V ℒₒᵣ n) = ↑(1 : V) := by ext; simp

@[simp] lemma typed_quote_add' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜‘!!t + !!u’⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜t⌝ + ⌜u⌝ := by ext; simp

@[simp] lemma typed_quote_mul' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜‘!!t * !!u’⌝ : Metamath.Semiterm V ℒₒᵣ n) = ⌜t⌝ * ⌜u⌝ := by ext; simp

end Semiterm

-/
