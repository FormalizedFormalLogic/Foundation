import Arithmetization.ISigmaOne.Metamath.Formula.Typed
import Arithmetization.Definability.Absoluteness
import Mathlib.Combinatorics.Colex

namespace LO.FirstOrder

namespace Semiformula.Operator

variable {L : Language}

lemma lt_eq [L.LT] (t u : Semiterm L ξ n) :
    LT.lt.operator ![t, u] = Semiformula.rel Language.LT.lt ![t, u] := by simp [operator, LT.sentence_eq, Rew.rel]

end Semiformula.Operator

end LO.FirstOrder

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

lemma nat_cast_empty : ((∅ : ℕ) : V) = ∅ := rfl

def finArrowToVec : {k : ℕ} → (Fin k → V) → V
  | 0,     _ => 0
  | k + 1, v => v 0 ∷ finArrowToVec (k := k) (v ·.succ)

/-- quasi-quotation rather than Godel quotation -/
instance : GoedelQuote (Fin k → V) V := ⟨finArrowToVec⟩

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
  · simp [quote_matrix_succ, ih]
    constructor
    · rintro ⟨h0, hs⟩
      funext x; cases' x using Fin.cases with x
      · exact h0
      · exact congr_fun hs x
    · rintro rfl; simp

@[simp] lemma quote_lh (v : Fin k → V) : len (⌜v⌝ : V) = k := by
  induction' k with k ih <;> simp [quote_matrix_succ, Matrix.empty_eq, *]

@[simp] lemma quote_nth_fin (v : Fin k → V) (i : Fin k) : (⌜v⌝ : V).[i] = v i := by
  induction' k with k ih <;> simp [quote_matrix_succ]
  · exact i.elim0
  · cases' i using Fin.cases with i <;> simp [ih]

@[simp] lemma quote_matrix_absolute (v : Fin k → ℕ) : ((⌜v⌝ : ℕ) : V) = ⌜fun i ↦ (v i : V)⌝ := by
  induction' k with k ih
  · simp
  · simp [quote_matrix_succ, ih, cons_absolute]

end LO.Arith

namespace LO.FirstOrder.Semiterm

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

def codeIn {n} : SyntacticSemiterm L n → V
  | #z                    => ^#z
  | &x                    => ^&x
  | func (arity := k) f v => ^func (k : V) ⌜f⌝ ⌜fun i ↦ (v i).codeIn⌝

instance : GoedelQuote (SyntacticSemiterm L n) V := ⟨(·.codeIn V)⟩

lemma quote_syntacticSemiterm_def (t : SyntacticSemiterm L n) : ⌜t⌝ = t.codeIn V := rfl

lemma quote_bvar (z : Fin n) : ⌜(#z : SyntacticSemiterm L n)⌝ = ^#(z : V) := rfl

lemma quote_fvar (x : ℕ) : ⌜(&x : SyntacticSemiterm L n)⌝ = ^&(x : V) := rfl

lemma quote_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    ⌜func f v⌝ = ^func (k : V) ⌜f⌝ ⌜fun i ↦ ⌜v i⌝⌝ := rfl

@[simp] lemma codeIn_inj {n} {t u : SyntacticSemiterm L n} : (⌜t⌝ : V) = ⌜u⌝ ↔ t = u := by
  induction t generalizing u
  case bvar z => rcases u <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc, Fin.val_inj]
  case fvar x => rcases u <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc]
  case func k f v ih =>
    rcases u <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc]
    rintro rfl; simp; rintro rfl
    constructor
    · intro h; funext i; exact (ih i).mp (congr_fun h i)
    · rintro rfl; rfl

@[simp] lemma quote_zero (n) :
    (⌜(Semiterm.func Language.Zero.zero ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = 𝟎 := by
  simp [FirstOrder.Semiterm.quote_func, Formalized.zero, Formalized.qqFunc_absolute]; rfl

@[simp] lemma quote_one (n) :
    (⌜(Semiterm.func Language.One.one ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = 𝟏 := by
  simp [FirstOrder.Semiterm.quote_func, Formalized.one, Formalized.qqFunc_absolute]; rfl

@[simp] lemma quote_add (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiterm.func Language.Add.add ![t, u]⌝ : V) = (⌜t⌝ ^+ ⌜u⌝) := by simp [FirstOrder.Semiterm.quote_func]; rfl

@[simp] lemma quote_mul (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiterm.func Language.Mul.mul ![t, u]⌝ : V) = (⌜t⌝ ^* ⌜u⌝) := by simp [FirstOrder.Semiterm.quote_func]; rfl

@[simp] lemma quote_absolute (t : SyntacticSemiterm L n) :
    ((⌜t⌝ : ℕ) : V) = ⌜t⌝ := by
  induction t <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc, Fin.val_inj, nat_cast_pair, *]

end LO.FirstOrder.Semiterm

namespace LO.Arith

open FirstOrder FirstOrder.Semiterm FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

/-- TODO: move-/
lemma eq_fin_of_lt_nat {n : ℕ} {x : V} (hx : x < n) : ∃ i : Fin n, x = i := by
  rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩
  exact ⟨⟨x, by simpa using hx⟩, by simp⟩

@[simp] lemma semiterm_codeIn {n} (t : SyntacticSemiterm L n) :
    (L.codeIn V).IsSemiterm n ⌜t⌝ := by
  induction t <;> simp [quote_bvar, quote_fvar, quote_func]
  case func k f v ih =>
    apply Language.IsSemitermVec.iff.mpr
    exact ⟨by simp, by
      rintro i hi
      rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
      simpa using ih i⟩

@[simp] lemma semitermVec_codeIn {k n} (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := Language.IsSemitermVec.iff.mpr
  ⟨by simp, by intro i hi; rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩; simp⟩

@[simp] lemma isUTermVec_codeIn {k n} (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).IsUTermVec k ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v |>.isUTerm

lemma termSubst_quote {n m} (t : SyntacticSemiterm L n) (w : Fin n → SyntacticSemiterm L m) :
    (L.codeIn V).termSubst ⌜fun i ↦ ⌜w i⌝⌝ ⌜t⌝ = ⌜Rew.substs w t⌝ := by
  induction t
  case bvar z => simp [quote_bvar, quote_fvar, quote_func]
  case fvar x => simp [quote_bvar, quote_fvar, quote_func]
  case func k f v ih =>
    have Hw : (L.codeIn V).IsSemitermVec n m ⌜fun i ↦ ⌜w i⌝⌝ := semitermVec_codeIn w
    have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, codeIn_func_quote, Language.termSubst_func (codeIn_func_quote f) Hv.isUTerm]
    congr
    apply nth_ext (by simp [(Hw.termSubstVec Hv).lh])
    intro i hi
    have hi : i < k := by simpa [Hw.termSubstVec Hv |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termSubstVec Hv.isUTerm hi]
    simpa using ih i

lemma termSubstVec_quote {k n m} (w : Fin n → SyntacticSemiterm L m) (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).termSubstVec ↑k ⌜fun i ↦ ⌜w i⌝⌝ ⌜fun i => ⌜v i⌝⌝ = ⌜fun i ↦ ⌜(Rew.substs w) (v i)⌝⌝ := by
  have Hw : (L.codeIn V).IsSemitermVec n m ⌜fun i ↦ ⌜w i⌝⌝ := semitermVec_codeIn w
  have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
  apply nth_ext (by simp [Hw.termSubstVec Hv |>.lh])
  intro i hi
  have hi : i < k := by simpa [Hw.termSubstVec Hv |>.lh] using hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  rw [nth_termSubstVec Hv.isUTerm hi]
  simpa using termSubst_quote (v i) w

lemma termShift_quote {n} (t : SyntacticSemiterm L n) :
    (L.codeIn V).termShift ⌜t⌝ = ⌜Rew.shift t⌝ := by
  induction t
  case bvar => simp [quote_bvar, quote_fvar, quote_func]
  case fvar => simp [quote_bvar, quote_fvar, quote_func]
  case func k f v ih =>
    have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, codeIn_func_quote, Language.termShift_func (codeIn_func_quote f) Hv.isUTerm]
    congr
    apply nth_ext (by simp [Hv.termShiftVec |>.lh])
    intro i hi
    have hi : i < k := by simpa [Hv.termShiftVec |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termShiftVec Hv.isUTerm hi]
    simpa using ih i

lemma termShiftVec_quote {k n} (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).termShiftVec k ⌜fun i ↦ ⌜v i⌝⌝ = ⌜fun i ↦ ⌜Rew.shift (v i)⌝⌝ := by
  have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
  apply nth_ext (by simp [Hv.termShiftVec |>.lh])
  intro i hi
  have hi : i < k := by simpa [Hv.termShiftVec |>.lh] using hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  rw [nth_termShiftVec Hv.isUTerm hi]
  simpa using termShift_quote (v i)

lemma termBShift_quote {n} (t : SyntacticSemiterm L n) :
    (L.codeIn V).termBShift ⌜t⌝ = ⌜Rew.bShift t⌝ := by
  induction t
  case bvar => simp [quote_bvar, quote_fvar, quote_func]
  case fvar => simp [quote_bvar, quote_fvar, quote_func]
  case func k f v ih =>
    have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, codeIn_func_quote, Language.termBShift_func (codeIn_func_quote f) Hv.isUTerm]
    congr
    apply nth_ext (by simp [Hv.termBShiftVec |>.lh])
    intro i hi
    have hi : i < k := by simpa [Hv.termBShiftVec |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termBShiftVec Hv.isUTerm hi]
    simpa using ih i

end LO.Arith

namespace LO.FirstOrder.Semiformula

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

def codeIn : {n : ℕ} → SyntacticSemiformula L n → V
  | _, rel (arity := k) R v  => ^rel (k : V) ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝
  | _, nrel (arity := k) R v => ^nrel (k : V) ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝
  | _, ⊤                     => ^⊤
  | _, ⊥                     => ^⊥
  | _, p ⋏ q                 => p.codeIn ^⋏ q.codeIn
  | _, p ⋎ q                 => p.codeIn ^⋎ q.codeIn
  | _, ∀' p                  => ^∀ p.codeIn
  | _, ∃' p                  => ^∃ p.codeIn

instance : GoedelQuote (SyntacticSemiformula L n) V := ⟨codeIn V⟩

lemma quote_syntacticSemiformula_def (p : SyntacticSemiformula L n) : ⌜p⌝ = p.codeIn V := rfl

lemma quote_rel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜rel R v⌝ : V) = ^rel ↑k ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝ := rfl
lemma quote_nrel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜nrel R v⌝ : V) = ^nrel ↑k ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝ := rfl
lemma quote_verum (n : ℕ) : ⌜(⊤ : SyntacticSemiformula L n)⌝ = (^⊤ : V) := rfl
lemma quote_falsum (n : ℕ) : ⌜(⊥ : SyntacticSemiformula L n)⌝ = (^⊥ : V) := rfl
lemma quote_and (p q : SyntacticSemiformula L n) : (⌜p ⋏ q⌝ : V) = ⌜p⌝ ^⋏ ⌜q⌝ := rfl
lemma quote_or (p q : SyntacticSemiformula L n) : (⌜p ⋎ q⌝ : V) = ⌜p⌝ ^⋎ ⌜q⌝ := rfl
lemma quote_all (p : SyntacticSemiformula L (n + 1)) : (⌜∀' p⌝ : V) = ^∀ ⌜p⌝ := rfl
lemma quote_ex (p : SyntacticSemiformula L (n + 1)) : (⌜∃' p⌝ : V) = ^∃ ⌜p⌝ := rfl

@[simp] lemma quote_eq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.rel Language.Eq.eq ![t, u]⌝ : V) = (⌜t⌝ ^= ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_rel]; rfl

@[simp] lemma quote_neq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.nrel Language.Eq.eq ![t, u]⌝ : V) = (⌜t⌝ ^≠ ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_nrel]; rfl

@[simp] lemma quote_lt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.rel Language.LT.lt ![t, u]⌝ : V) = (⌜t⌝ ^< ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_rel]; rfl

@[simp] lemma quote_nlt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.nrel Language.LT.lt ![t, u]⌝ : V) = (⌜t⌝ ^≮ ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_nrel]; rfl

@[simp] lemma codeIn_inj {n} {p q : SyntacticSemiformula L n} : (⌜p⌝ : V) = ⌜q⌝ ↔ p = q := by
  induction p using rec'
  case hrel =>
    cases q using cases' <;>
      simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]
    rintro rfl; simp; rintro rfl;
    constructor
    · intro h; funext i; simpa using congr_fun h i
    · rintro rfl; rfl
  case hnrel =>
    cases q using cases' <;>
      simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]
    rintro rfl; simp; rintro rfl;
    constructor
    · intro h; funext i; simpa using congr_fun h i
    · rintro rfl; rfl
  case hverum =>
    cases q using cases' <;>
      simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]
  case hfalsum =>
    cases q using cases' <;>
      simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]
  case hand n p q ihp ihq =>
    cases q using cases' <;>
      simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]
    rw [ihp, ihq]
  case hor n p q ihp ihq =>
    cases q using cases' <;>
      simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]
    rw [ihp, ihq]
  case hall n p ih =>
    cases q using cases' <;>
      simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]
    rw [ih]
  case hex n p ih =>
    cases q using cases' <;>
      simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]
    rw [ih]

@[simp] lemma quote_absolute (p : SyntacticSemiformula L n) :
    ((⌜p⌝ : ℕ) : V) = ⌜p⌝ := by
  induction p using rec' <;> simp [quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
        qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx, nat_cast_pair, *]

instance : GoedelQuote (Semisentence L n) V := ⟨fun σ ↦ ⌜(Rew.emb.hom σ : SyntacticSemiformula L n)⌝⟩

lemma quote_semisentence_def (p : Semisentence L n) : (⌜p⌝ : V) = ⌜(Rew.emb.hom p : SyntacticSemiformula L n)⌝ := rfl

@[simp] lemma quote_semisentence_absolute (p : Semisentence L n) : ((⌜p⌝ : ℕ) : V) = ⌜p⌝ := by
  simp [quote_semisentence_def]

instance : Semiterm.Operator.GoedelNumber ℒₒᵣ (SyntacticFormula L) := ⟨fun p ↦ Semiterm.Operator.numeral ℒₒᵣ ⌜p⌝⟩

instance : Semiterm.Operator.GoedelNumber ℒₒᵣ (Sentence L) := ⟨fun σ ↦ Semiterm.Operator.numeral ℒₒᵣ ⌜σ⌝⟩

lemma sentence_goedelNumber_def (σ : Sentence L) :
  (⌜σ⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.numeral ℒₒᵣ ⌜σ⌝ := rfl

lemma syntacticformula_goedelNumber_def (p : SyntacticFormula L) :
  (⌜p⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.numeral ℒₒᵣ ⌜p⌝ := rfl

end LO.FirstOrder.Semiformula

namespace LO.Arith

open FirstOrder FirstOrder.Arith FirstOrder.Semiformula

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

@[simp] lemma semiformula_quote {n} (p : SyntacticSemiformula L n) :
    (L.codeIn V).IsSemiformula n ⌜p⌝ := by
  induction p using Semiformula.rec'
  case hrel n k r v => simp [Semiformula.quote_rel]
  case hnrel n k r v => simp [Semiformula.quote_nrel]
  case hverum n => simp [Semiformula.quote_verum]
  case hfalsum n => simp [Semiformula.quote_falsum]
  case hand n p q ihp ihq => simp [Semiformula.quote_and, ihp, ihq]
  case hor n p q ihp ihq => simp [Semiformula.quote_or, ihp, ihq]
  case hall n p ihp => simpa [Semiformula.quote_all] using ihp
  case hex n p ihp => simpa [Semiformula.quote_ex] using ihp

@[simp] lemma isUFormula_quote {n} (p : SyntacticSemiformula L n) :
    (L.codeIn V).IsUFormula ⌜p⌝ := semiformula_quote p |>.isUFormula

@[simp] lemma semiformula_quote_succ {n} (p : SyntacticSemiformula L (n + 1)) :
    (L.codeIn V).IsSemiformula (n + 1) ⌜p⌝ := by simpa using semiformula_quote p

lemma neg_quote {n} (p : SyntacticSemiformula L n) :
    (L.codeIn V).neg ⌜p⌝ = ⌜~p⌝ := by
  induction p using Semiformula.rec' <;>
    simp [*, quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex]

lemma shift_quote {n} (p : SyntacticSemiformula L n) :
    (L.codeIn V).shift ⌜p⌝ = ⌜Rew.shift.hom p⌝ := by
  induction p using Semiformula.rec' <;>
    simp [*, quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
      Rew.rel, Rew.nrel, termShiftVec_quote]

lemma qVec_quote (w : Fin n → SyntacticSemiterm L m) :
    (L.codeIn V).qVec ⌜fun i => ⌜w i⌝⌝ = ⌜^#0 :> fun i ↦ (⌜Rew.bShift (w i)⌝ : V)⌝ := by
  have Hw : (L.codeIn V).IsSemitermVec ↑n (↑m + 1) ((L.codeIn V).termBShiftVec ↑n ⌜fun i ↦ ⌜w i⌝⌝) :=
    (semitermVec_codeIn w).termBShiftVec
  have HqVec : (L.codeIn V).IsSemitermVec (↑n + 1) (↑m + 1) ((L.codeIn V).qVec ⌜fun i ↦ ⌜w i⌝⌝) :=
    (semitermVec_codeIn w).qVec
  apply nth_ext (by simp [←HqVec.lh])
  intro i hi
  have : i < ↑(n + 1) := by simpa [Language.qVec, Hw.lh] using hi
  rcases eq_fin_of_lt_nat this with ⟨i, rfl⟩
  cases' i using Fin.cases with i
  · simp [Language.qVec]
  · simp [Language.qVec, termBShift_quote]

lemma substs_quote {n m} (w : Fin n → SyntacticSemiterm L m) (p : SyntacticSemiformula L n) :
    (L.codeIn V).substs ⌜fun i ↦ ⌜w i⌝⌝ ⌜p⌝ = ⌜(Rew.substs w).hom p⌝ := by
  induction p using Semiformula.rec' generalizing m <;>
    simp [*, quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
      Rew.rel, Rew.nrel, termSubstVec_quote, Rew.q_substs]
  case hall p ih => simp [←ih, qVec_quote, Semiterm.quote_bvar]
  case hex p ih => simp [←ih, qVec_quote, Semiterm.quote_bvar]

lemma free_quote (p : SyntacticSemiformula L 1) :
    (L.codeIn V).free ⌜p⌝ = ⌜Rew.free.hom p⌝ := by
  rw [←Rew.hom_substs_mbar_zero_comp_shift_eq_free, ←substs_quote, ←shift_quote]
  simp [Language.free, Language.substs₁, Semiterm.quote_fvar]

end LO.Arith


namespace LO.FirstOrder.Derivation2

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]
  [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

-- def codeIn : {Γ : Finset (SyntacticFormula L)} → Derivation2 Γ → V

end LO.FirstOrder.Derivation2

/-!

### Typed

-/

namespace LO.FirstOrder

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

variable {n : ℕ}

namespace Semiterm

def codeIn' (t : SyntacticSemiterm L n) : (L.codeIn V).Semiterm n := ⟨⌜t⌝, by simp⟩

instance : GoedelQuote (SyntacticSemiterm L n) ((L.codeIn V).Semiterm n) := ⟨Semiterm.codeIn' V⟩

@[simp] lemma codeIn'_val (t : SyntacticSemiterm L n) : (⌜t⌝ : (L.codeIn V).Semiterm n).val = ⌜t⌝ := rfl

def vCodeIn' {k n} (v : Fin k → SyntacticSemiterm L n) : (L.codeIn V).SemitermVec k n := ⟨⌜fun i ↦ ⌜v i⌝⌝, by simp⟩

instance {k n} : GoedelQuote (Fin k → SyntacticSemiterm L n) ((L.codeIn V).SemitermVec k n) := ⟨Semiterm.vCodeIn' V⟩

@[simp] lemma vCodeIn'_val (v : Fin k → SyntacticSemiterm L n) : (⌜v⌝ : (L.codeIn V).SemitermVec k n).val = ⌜fun i ↦ ⌜v i⌝⌝ := rfl

@[simp] lemma codeIn'_bvar (z : Fin n) : (⌜(#z : SyntacticSemiterm L n)⌝ : (L.codeIn V).Semiterm n) = (L.codeIn V).bvar z := rfl
@[simp] lemma codeIn'_fvar (x : ℕ) : (⌜(&x : SyntacticSemiterm L n)⌝ : (L.codeIn V).Semiterm n) = (L.codeIn V).fvar x := rfl
lemma codeIn'_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜func f v⌝ : (L.codeIn V).Semiterm n) = (L.codeIn V).func (k := k) (f := ⌜f⌝) (by simp) ⌜v⌝ := rfl

@[simp] lemma codeIn'_zero (n : ℕ) :
    (⌜(func Language.Zero.zero ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : (Language.codeIn ℒₒᵣ V).Semiterm n) = ↑(0 : V) := by ext; simp
@[simp] lemma codeIn'_one (n : ℕ) :
    (⌜(func Language.One.one ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : (Language.codeIn ℒₒᵣ V).Semiterm n) = ↑(1 : V) := by ext; simp
@[simp] lemma codeIn'_add (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Add.add v⌝ : (Language.codeIn ℒₒᵣ V).Semiterm n) = ⌜v 0⌝ + ⌜v 1⌝ := by ext; simp; rfl
@[simp] lemma codeIn'_mul (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Mul.mul v⌝ : (Language.codeIn ℒₒᵣ V).Semiterm n) = ⌜v 0⌝ * ⌜v 1⌝ := by ext; simp; rfl

end Semiterm

namespace Semiformula

def codeIn' (p : SyntacticSemiformula L n) : (L.codeIn V).Semiformula n := ⟨⌜p⌝, by simp⟩

instance : GoedelQuote (SyntacticSemiformula L n) ((L.codeIn V).Semiformula n) := ⟨Semiformula.codeIn' V⟩

@[simp] lemma codeIn'_val (p : SyntacticSemiformula L n) : (⌜p⌝ : (L.codeIn V).Semiformula n).val = ⌜p⌝ := rfl

@[simp] lemma codeIn'_verum (n : ℕ) : (⌜(⊤ : SyntacticSemiformula L n)⌝ : (L.codeIn V).Semiformula n) = ⊤ := rfl
@[simp] lemma codeIn'_falsum (n : ℕ) : (⌜(⊥ : SyntacticSemiformula L n)⌝ : (L.codeIn V).Semiformula n) = ⊥ := rfl
@[simp] lemma codeIn'_and (p q : SyntacticSemiformula L n) : (⌜p ⋏ q⌝ : (L.codeIn V).Semiformula n) = ⌜p⌝ ⋏ ⌜q⌝ := rfl
@[simp] lemma codeIn'_or (p q : SyntacticSemiformula L n) : (⌜p ⋎ q⌝ : (L.codeIn V).Semiformula n) = ⌜p⌝ ⋎ ⌜q⌝ := rfl
@[simp] lemma codeIn'_all (p : SyntacticSemiformula L (n + 1)) : (⌜∀' p⌝ : (L.codeIn V).Semiformula n) = .all (.cast (n := ↑(n + 1)) ⌜p⌝) := rfl
@[simp] lemma codeIn'_ex (p : SyntacticSemiformula L (n + 1)) : (⌜∃' p⌝ : (L.codeIn V).Semiformula n) = .ex (.cast (n := ↑(n + 1)) ⌜p⌝) := rfl
@[simp] lemma codeIn'_neg (p : SyntacticSemiformula L n) : (⌜~p⌝ : (L.codeIn V).Semiformula n) = ~⌜p⌝ := by
  ext; simp [neg_quote]
@[simp] lemma codeIn'_imp (p q : SyntacticSemiformula L n) : (⌜p ⟶ q⌝ : (L.codeIn V).Semiformula n) = ⌜p⌝ ⟶ ⌜q⌝ := by
  simp [Semiformula.imp_eq, Language.Semiformula.imp_def]

open LO.Arith Formalized

@[simp] lemma codeIn'_eq (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜rel Language.Eq.eq v⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = (⌜v 0⌝ =' ⌜v 1⌝) := by ext; simp [Language.Semiterm.equals]; rfl
@[simp] lemma codeIn'_neq (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜nrel Language.Eq.eq v⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = (⌜v 0⌝ ≠' ⌜v 1⌝) := by ext; simp [Language.Semiterm.notEquals]; rfl
@[simp] lemma codeIn'_lt (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜rel Language.LT.lt v⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = (⌜v 0⌝ <' ⌜v 1⌝) := by ext; simp [Language.Semiterm.lessThan]; rfl
@[simp] lemma codeIn'_nlt (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜nrel Language.LT.lt v⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = (⌜v 0⌝ ≮' ⌜v 1⌝) := by ext; simp [Language.Semiterm.notLessThan]; rfl
@[simp] lemma codeIn'_ball (t : SyntacticSemiterm ℒₒᵣ n) (p : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    (⌜∀[“#0 < !!(Rew.bShift t)”] p⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = Language.Semiformula.ball ⌜t⌝ (.cast (n := ↑(n + 1)) ⌜p⌝) := by
  ext; simp [LogicalConnective.ball, imp_eq, Language.Semiformula.cast,
    Language.Semiformula.ball, Semiformula.Operator.lt_eq, termBShift_quote]
@[simp] lemma codeIn'_bex (t : SyntacticSemiterm ℒₒᵣ n) (p : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    (⌜∃[“#0 < !!(Rew.bShift t)”] p⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = Language.Semiformula.bex ⌜t⌝ (.cast (n := ↑(n + 1)) ⌜p⌝) := by
  ext; simp [LogicalConnective.bex, imp_eq, Language.Semiformula.cast,
    Language.Semiformula.ball, Semiformula.Operator.lt_eq, termBShift_quote]

instance : GoedelQuote (Sentence L) ((L.codeIn V).TFormula) := ⟨fun σ ↦ (⌜Rew.embs.hom σ⌝ : (Language.codeIn L V).Semiformula (0 : ℕ))⟩

lemma quote_sentence_def' (σ : Sentence L) : (⌜σ⌝ : (L.codeIn V).TFormula) = (⌜Rew.embs.hom σ⌝ : (Language.codeIn L V).Semiformula (0 : ℕ)) := rfl

@[simp] lemma quote_sentence_val (σ : Sentence L) : (⌜σ⌝ : (L.codeIn V).TFormula).val = ⌜σ⌝ := rfl

end Semiformula

end LO.FirstOrder
