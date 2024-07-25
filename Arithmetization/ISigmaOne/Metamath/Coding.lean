import Arithmetization.ISigmaOne.Metamath.Proof.Typed
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

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

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

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

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

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

/-- TODO: move-/
lemma eq_fin_of_lt_nat {n : ℕ} {x : V} (hx : x < n) : ∃ i : Fin n, x = i := by
  rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩
  exact ⟨⟨x, by simpa using hx⟩, by simp⟩

@[simp] lemma semiterm_codeIn {n} (t : SyntacticSemiterm L n) :
    (L.codeIn V).Semiterm n ⌜t⌝ := by
  induction t <;> simp [quote_bvar, quote_fvar, quote_func]
  case func k f v ih =>
    exact ⟨by simp, by
      rintro i hi
      rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
      simpa using ih i⟩

@[simp] lemma semitermVec_codeIn {k n} (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).SemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ :=
  ⟨by simp, by intro i hi; rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩; simp⟩

lemma termSubst_quote {n m} (t : SyntacticSemiterm L n) (w : Fin n → SyntacticSemiterm L m) :
    (L.codeIn V).termSubst ↑n ↑m ⌜fun i ↦ ⌜w i⌝⌝ ⌜t⌝ = ⌜Rew.substs w t⌝ := by
  induction t
  case bvar z => simp [quote_bvar, quote_fvar, quote_func]
  case fvar x => simp [quote_bvar, quote_fvar, quote_func]
  case func k f v ih =>
    have Hw : (L.codeIn V).SemitermVec n m ⌜fun i ↦ ⌜w i⌝⌝ := semitermVec_codeIn w
    have Hv : (L.codeIn V).SemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, codeIn_func_quote, termSubst_func (codeIn_func_quote f) Hv]
    congr
    apply nth_ext (by simp [←Hw.termSubstVec Hv |>.lh])
    intro i hi
    have hi : i < k := by simpa [← Hw.termSubstVec Hv |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simpa [nth_termSubstVec] using ih i

lemma termSubstVec_quote {k n m} (w : Fin n → SyntacticSemiterm L m) (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).termSubstVec ↑k ↑n ↑m ⌜fun i ↦ ⌜w i⌝⌝ ⌜fun i => ⌜v i⌝⌝ = ⌜fun i ↦ ⌜(Rew.substs w) (v i)⌝⌝ := by
  have Hw : (L.codeIn V).SemitermVec n m ⌜fun i ↦ ⌜w i⌝⌝ := semitermVec_codeIn w
  have Hv : (L.codeIn V).SemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
  apply nth_ext (by simp [←Hw.termSubstVec Hv |>.lh])
  intro i hi
  have hi : i < k := by simpa [← Hw.termSubstVec Hv |>.lh] using hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  simpa [nth_termSubstVec] using termSubst_quote (v i) w

lemma termShift_quote {n} (t : SyntacticSemiterm L n) :
    (L.codeIn V).termShift n ⌜t⌝ = ⌜Rew.shift t⌝ := by
  induction t
  case bvar => simp [quote_bvar, quote_fvar, quote_func]
  case fvar => simp [quote_bvar, quote_fvar, quote_func]
  case func k f v ih =>
    have Hv : (L.codeIn V).SemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, codeIn_func_quote, termShift_func (codeIn_func_quote f) Hv]
    congr
    apply nth_ext (by simp [←Hv.termShiftVec |>.lh])
    intro i hi
    have hi : i < k := by simpa [← Hv.termShiftVec |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simpa [nth_termShiftVec] using ih i

lemma termShiftVec_quote {k n} (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).termShiftVec k n ⌜fun i ↦ ⌜v i⌝⌝ = ⌜fun i ↦ ⌜Rew.shift (v i)⌝⌝ := by
  have Hv : (L.codeIn V).SemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
  apply nth_ext (by simp [←Hv.termShiftVec |>.lh])
  intro i hi
  have hi : i < k := by simpa [← Hv.termShiftVec |>.lh] using hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  simpa [nth_termShiftVec] using termShift_quote (v i)

lemma termBShift_quote {n} (t : SyntacticSemiterm L n) :
    (L.codeIn V).termBShift n ⌜t⌝ = ⌜Rew.bShift t⌝ := by
  induction t
  case bvar => simp [quote_bvar, quote_fvar, quote_func]
  case fvar => simp [quote_bvar, quote_fvar, quote_func]
  case func k f v ih =>
    have Hv : (L.codeIn V).SemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, codeIn_func_quote, termBShift_func (codeIn_func_quote f) Hv]
    congr
    apply nth_ext (by simp [←Hv.termBShiftVec |>.lh])
    intro i hi
    have hi : i < k := by simpa [← Hv.termBShiftVec |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simpa [nth_termBShiftVec] using ih i

end LO.Arith

namespace LO.FirstOrder.Semiformula

open LO.Arith FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

def codeIn : {n : ℕ} → SyntacticSemiformula L n → V
  | n, rel (arity := k) R v  => ^rel (n : V) (k : V) ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝
  | n, nrel (arity := k) R v => ^nrel (n : V) (k : V) ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝
  | n, ⊤                     => ^⊤[n]
  | n, ⊥                     => ^⊥[n]
  | n, p ⋏ q                 => p.codeIn ^⋏[n] q.codeIn
  | n, p ⋎ q                 => p.codeIn ^⋎[n] q.codeIn
  | n, ∀' p                  => ^∀[n] p.codeIn
  | n, ∃' p                  => ^∃[n] p.codeIn

instance : GoedelQuote (SyntacticSemiformula L n) V := ⟨codeIn V⟩

lemma quote_syntacticSemiformula_def (p : SyntacticSemiformula L n) : ⌜p⌝ = p.codeIn V := rfl

lemma quote_rel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜rel R v⌝ : V) = ^rel ↑n ↑k ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝ := rfl
lemma quote_nrel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜nrel R v⌝ : V) = ^nrel ↑n ↑k ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝ := rfl
lemma quote_verum (n : ℕ) : ⌜(⊤ : SyntacticSemiformula L n)⌝ = ^⊤[(n : V)] := rfl
lemma quote_falsum (n : ℕ) : ⌜(⊥ : SyntacticSemiformula L n)⌝ = ^⊥[(n : V)] := rfl
lemma quote_and (p q : SyntacticSemiformula L n) : ⌜p ⋏ q⌝ = ⌜p⌝ ^⋏[(n : V)] ⌜q⌝ := rfl
lemma quote_or (p q : SyntacticSemiformula L n) : ⌜p ⋎ q⌝ = ⌜p⌝ ^⋎[(n : V)] ⌜q⌝ := rfl
lemma quote_all (p : SyntacticSemiformula L (n + 1)) : ⌜∀' p⌝ = ^∀[(n : V)] ⌜p⌝ := rfl
lemma quote_ex (p : SyntacticSemiformula L (n + 1)) : ⌜∃' p⌝ = ^∃[(n : V)] ⌜p⌝ := rfl

@[simp] lemma quote_eq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.rel Language.Eq.eq ![t, u]⌝ : V) = (⌜t⌝ ^=[(n : V)] ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_rel]; rfl

@[simp] lemma quote_neq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.nrel Language.Eq.eq ![t, u]⌝ : V) = (⌜t⌝ ^≠[(n : V)] ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_nrel]; rfl

@[simp] lemma quote_lt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.rel Language.LT.lt ![t, u]⌝ : V) = (⌜t⌝ ^<[(n : V)] ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_rel]; rfl

@[simp] lemma quote_nlt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.nrel Language.LT.lt ![t, u]⌝ : V) = (⌜t⌝ ^≮[(n : V)] ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_nrel]; rfl

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

instance : Semiterm.Operator.GoedelNumber ℒₒᵣ (Sentence L) := ⟨fun σ ↦ Semiterm.Operator.numeral ℒₒᵣ ⌜σ⌝⟩

lemma sentence_goedelNumber_def (σ : Sentence L) :
  (⌜σ⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.numeral ℒₒᵣ ⌜σ⌝ := rfl

end LO.FirstOrder.Semiformula

namespace LO.Arith

open FirstOrder FirstOrder.Arith FirstOrder.Semiformula

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

@[simp] lemma semiformula_quote {n} (p : SyntacticSemiformula L n) :
    (L.codeIn V).Semiformula n ⌜p⌝ := by
  induction p using Semiformula.rec'
  case hrel n k r v => simp [Semiformula.quote_rel]
  case hnrel n k r v => simp [Semiformula.quote_nrel]
  case hverum n => simp [Semiformula.quote_verum]
  case hfalsum n => simp [Semiformula.quote_falsum]
  case hand n p q ihp ihq => simp [Semiformula.quote_and, ihp, ihq]
  case hor n p q ihp ihq => simp [Semiformula.quote_or, ihp, ihq]
  case hall n p ihp => simpa [Semiformula.quote_all] using ihp
  case hex n p ihp => simpa [Semiformula.quote_ex] using ihp

@[simp] lemma semiformula_quote_succ {n} (p : SyntacticSemiformula L (n + 1)) :
    (L.codeIn V).Semiformula (n + 1) ⌜p⌝ := by simpa using semiformula_quote p

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
    (L.codeIn V).qVec ↑n ↑m ⌜fun i => ⌜w i⌝⌝ = ⌜^#0 :> fun i ↦ (⌜Rew.bShift (w i)⌝ : V)⌝ := by
  have Hw : (L.codeIn V).SemitermVec ↑n (↑m + 1) ((L.codeIn V).termBShiftVec ↑n ↑m ⌜fun i ↦ ⌜w i⌝⌝) :=
    (semitermVec_codeIn w).termBShiftVec
  have HqVec : (L.codeIn V).SemitermVec (↑n + 1) (↑m + 1) ((L.codeIn V).qVec ↑n ↑m ⌜fun i ↦ ⌜w i⌝⌝) :=
    (semitermVec_codeIn w).qVec
  apply nth_ext (by simp [←HqVec.lh])
  intro i hi
  have : i < ↑(n + 1) := by simpa [Language.qVec, ←Hw.lh] using hi
  rcases eq_fin_of_lt_nat this with ⟨i, rfl⟩
  cases' i using Fin.cases with i
  · simp [Language.qVec]
  · simp [Language.qVec, termBShift_quote]

lemma substs_quote {n m} (w : Fin n → SyntacticSemiterm L m) (p : SyntacticSemiformula L n) :
    (L.codeIn V).substs ↑m ⌜fun i ↦ ⌜w i⌝⌝ ⌜p⌝ = ⌜(Rew.substs w).hom p⌝ := by
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

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

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

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

variable {n : ℕ}

namespace Semiterm

def codeIn' (t : SyntacticSemiterm L n) : (L.codeIn V).TSemiterm n := ⟨⌜t⌝, by simp⟩

instance : GoedelQuote (SyntacticSemiterm L n) ((L.codeIn V).TSemiterm n) := ⟨Semiterm.codeIn' V⟩

@[simp] lemma codeIn'_val (t : SyntacticSemiterm L n) : (⌜t⌝ : (L.codeIn V).TSemiterm n).val = ⌜t⌝ := rfl

def vCodeIn' {k n} (v : Fin k → SyntacticSemiterm L n) : (L.codeIn V).TSemitermVec k n := ⟨⌜fun i ↦ ⌜v i⌝⌝, by simp⟩

instance {k n} : GoedelQuote (Fin k → SyntacticSemiterm L n) ((L.codeIn V).TSemitermVec k n) := ⟨Semiterm.vCodeIn' V⟩

@[simp] lemma vCodeIn'_val (v : Fin k → SyntacticSemiterm L n) : (⌜v⌝ : (L.codeIn V).TSemitermVec k n).val = ⌜fun i ↦ ⌜v i⌝⌝ := rfl

@[simp] lemma codeIn'_bvar (z : Fin n) : (⌜(#z : SyntacticSemiterm L n)⌝ : (L.codeIn V).TSemiterm n) = (L.codeIn V).bvar z := rfl
@[simp] lemma codeIn'_fvar (x : ℕ) : (⌜(&x : SyntacticSemiterm L n)⌝ : (L.codeIn V).TSemiterm n) = (L.codeIn V).fvar x := rfl
lemma codeIn'_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜func f v⌝ : (L.codeIn V).TSemiterm n) = (L.codeIn V).func (k := k) (f := ⌜f⌝) (by simp) ⌜v⌝ := rfl

@[simp] lemma codeIn'_zero (n : ℕ) :
    (⌜(func Language.Zero.zero ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : (Language.codeIn ℒₒᵣ V).TSemiterm n) = ↑(0 : V) := by ext; simp
@[simp] lemma codeIn'_one (n : ℕ) :
    (⌜(func Language.One.one ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : (Language.codeIn ℒₒᵣ V).TSemiterm n) = ↑(1 : V) := by ext; simp
@[simp] lemma codeIn'_add (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Add.add v⌝ : (Language.codeIn ℒₒᵣ V).TSemiterm n) = ⌜v 0⌝ + ⌜v 1⌝ := by ext; simp; rfl
@[simp] lemma codeIn'_mul (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Mul.mul v⌝ : (Language.codeIn ℒₒᵣ V).TSemiterm n) = ⌜v 0⌝ * ⌜v 1⌝ := by ext; simp; rfl

end Semiterm

namespace Semiformula

def codeIn' (p : SyntacticSemiformula L n) : (L.codeIn V).TSemiformula n := ⟨⌜p⌝, by simp⟩

instance : GoedelQuote (SyntacticSemiformula L n) ((L.codeIn V).TSemiformula n) := ⟨Semiformula.codeIn' V⟩

@[simp] lemma codeIn'_val (p : SyntacticSemiformula L n) : (⌜p⌝ : (L.codeIn V).TSemiformula n).val = ⌜p⌝ := rfl

@[simp] lemma codeIn'_verum (n : ℕ) : (⌜(⊤ : SyntacticSemiformula L n)⌝ : (L.codeIn V).TSemiformula n) = ⊤ := rfl
@[simp] lemma codeIn'_falsum (n : ℕ) : (⌜(⊥ : SyntacticSemiformula L n)⌝ : (L.codeIn V).TSemiformula n) = ⊥ := rfl
@[simp] lemma codeIn'_and (p q : SyntacticSemiformula L n) : (⌜p ⋏ q⌝ : (L.codeIn V).TSemiformula n) = ⌜p⌝ ⋏ ⌜q⌝ := rfl
@[simp] lemma codeIn'_or (p q : SyntacticSemiformula L n) : (⌜p ⋎ q⌝ : (L.codeIn V).TSemiformula n) = ⌜p⌝ ⋎ ⌜q⌝ := rfl
@[simp] lemma codeIn'_all (p : SyntacticSemiformula L (n + 1)) : (⌜∀' p⌝ : (L.codeIn V).TSemiformula n) = .all (.cast (n := ↑(n + 1)) ⌜p⌝) := rfl
@[simp] lemma codeIn'_ex (p : SyntacticSemiformula L (n + 1)) : (⌜∃' p⌝ : (L.codeIn V).TSemiformula n) = .ex (.cast (n := ↑(n + 1)) ⌜p⌝) := rfl
@[simp] lemma codeIn'_neg (p : SyntacticSemiformula L n) : (⌜~p⌝ : (L.codeIn V).TSemiformula n) = ~⌜p⌝ := by
  ext; simp [neg_quote]
@[simp] lemma codeIn'_imp (p q : SyntacticSemiformula L n) : (⌜p ⟶ q⌝ : (L.codeIn V).TSemiformula n) = ⌜p⌝ ⟶ ⌜q⌝ := by
  simp [Semiformula.imp_eq, Language.TSemiformula.imp_def]

open LO.Arith Formalized

@[simp] lemma codeIn'_eq (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜rel Language.Eq.eq v⌝ : (Language.codeIn ℒₒᵣ V).TSemiformula n) = (⌜v 0⌝ =' ⌜v 1⌝) := by ext; simp [Language.TSemiterm.equals]; rfl
@[simp] lemma codeIn'_neq (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜nrel Language.Eq.eq v⌝ : (Language.codeIn ℒₒᵣ V).TSemiformula n) = (⌜v 0⌝ ≠' ⌜v 1⌝) := by ext; simp [Language.TSemiterm.notEquals]; rfl
@[simp] lemma codeIn'_lt (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜rel Language.LT.lt v⌝ : (Language.codeIn ℒₒᵣ V).TSemiformula n) = (⌜v 0⌝ <' ⌜v 1⌝) := by ext; simp [Language.TSemiterm.lessThan]; rfl
@[simp] lemma codeIn'_nlt (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜nrel Language.LT.lt v⌝ : (Language.codeIn ℒₒᵣ V).TSemiformula n) = (⌜v 0⌝ ≮' ⌜v 1⌝) := by ext; simp [Language.TSemiterm.notLessThan]; rfl
@[simp] lemma codeIn'_ball (t : SyntacticSemiterm ℒₒᵣ n) (p : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    (⌜∀[“#0 < !!(Rew.bShift t)”] p⌝ : (Language.codeIn ℒₒᵣ V).TSemiformula n) = Language.TSemiformula.ball ⌜t⌝ (.cast (n := ↑(n + 1)) ⌜p⌝) := by
  ext; simp [LogicalConnective.ball, imp_eq, Language.TSemiformula.cast,
    Language.TSemiformula.ball, Semiformula.Operator.lt_eq, termBShift_quote]
@[simp] lemma codeIn'_bex (t : SyntacticSemiterm ℒₒᵣ n) (p : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    (⌜∃[“#0 < !!(Rew.bShift t)”] p⌝ : (Language.codeIn ℒₒᵣ V).TSemiformula n) = Language.TSemiformula.bex ⌜t⌝ (.cast (n := ↑(n + 1)) ⌜p⌝) := by
  ext; simp [LogicalConnective.bex, imp_eq, Language.TSemiformula.cast,
    Language.TSemiformula.ball, Semiformula.Operator.lt_eq, termBShift_quote]

end Semiformula

namespace Derivation2

def Sequent.codeIn (Γ : Finset (SyntacticFormula L)) : V := ∑ p ∈ Γ, exp (⌜p⌝ : V)

instance : GoedelQuote (Finset (SyntacticFormula L)) V := ⟨Sequent.codeIn V⟩

lemma Sequent.codeIn_def (Γ : Finset (SyntacticFormula L)) : ⌜Γ⌝ = ∑ p ∈ Γ, exp (⌜p⌝ : V) := rfl

variable {V}

open Classical

@[simp] lemma Sequent.codeIn_empty : (⌜(∅ : Finset (SyntacticFormula L))⌝ : V) = ∅ := by
  simp [Sequent.codeIn_def, emptyset_def]

lemma Sequent.mem_codeIn_iff {Γ : Finset (SyntacticFormula L)} {p} : ⌜p⌝ ∈ (⌜Γ⌝ : V) ↔ p ∈ Γ := by
  induction Γ using Finset.induction generalizing p
  case empty => simp [Sequent.codeIn_def]
  case insert a Γ ha ih =>
    have : exp ⌜a⌝ + ∑ p ∈ Γ, exp (⌜p⌝ : V) = insert (⌜a⌝ : V) (⌜Γ⌝ : V) := by
      simp [insert, bitInsert, (not_iff_not.mpr ih.symm).mp ha, add_comm]
      rw [Sequent.codeIn_def]
    simp [ha, Sequent.codeIn_def]
    rw [this]
    simp [←ih]

@[simp] lemma Sequent.codeIn_insert (Γ : Finset (SyntacticFormula L)) (p) : (⌜(insert p Γ)⌝ : V) = insert ⌜p⌝ ⌜Γ⌝ := by
  by_cases hp : p ∈ Γ
  · simp [Sequent.mem_codeIn_iff, hp, insert_eq_self_of_mem]
  · have : (⌜insert p Γ⌝ : V) = exp ⌜p⌝ + ⌜Γ⌝ := by simp [Sequent.codeIn_def, hp]
    simp [Sequent.mem_codeIn_iff, this, insert_eq, bitInsert, hp, add_comm]

lemma Sequent.mem_codeIn {Γ : Finset (SyntacticFormula L)} (hx : x ∈ (⌜Γ⌝ : V)) : ∃ p ∈ Γ, x = ⌜p⌝ := by
  induction Γ using Finset.induction
  case empty => simp at hx
  case insert a Γ _ ih =>
    have : x = ⌜a⌝ ∨ x ∈ (⌜Γ⌝ : V) := by simpa using hx
    rcases this with (rfl | hx)
    · exact ⟨a, by simp⟩
    · rcases ih hx with ⟨p, hx, rfl⟩
      exact ⟨p, by simp [*]⟩

variable (V)

def codeIn : {Γ : Finset (SyntacticFormula L)} → ⊢¹ᶠ Γ → V
  | _, axL (Δ := Δ) p _ _                     => Arith.axL ⌜Δ⌝ ⌜p⌝
  | _, verum (Δ := Δ) _                       => Arith.verumIntro ⌜Δ⌝
  | _, and (Δ := Δ) _ (p := p) (q := q) bp bq => Arith.andIntro ⌜Δ⌝ ⌜p⌝ ⌜q⌝ bp.codeIn bq.codeIn
  | _, or (Δ := Δ) (p := p) (q := q) _ d      => Arith.orIntro ⌜Δ⌝ ⌜p⌝ ⌜q⌝ d.codeIn
  | _, all (Δ := Δ) (p := p) _ d              => Arith.allIntro ⌜Δ⌝ ⌜p⌝ d.codeIn
  | _, ex (Δ := Δ) (p := p) _ t d             => Arith.exIntro ⌜Δ⌝ ⌜p⌝ ⌜t⌝ d.codeIn
  | _, wk (Γ := Γ) d _                        => Arith.wkRule ⌜Γ⌝ d.codeIn
  | _, shift (Δ := Δ) d                       => Arith.shiftRule ⌜Δ.image Rew.shift.hom⌝ d.codeIn
  | _, cut (Δ := Δ) (p := p) d dn             => Arith.cutRule ⌜Δ⌝ ⌜p⌝ d.codeIn dn.codeIn

instance (Γ : Finset (SyntacticFormula L)) : GoedelQuote (⊢¹ᶠ Γ) V := ⟨codeIn V⟩

lemma quote_derivation_def {Γ : Finset (SyntacticFormula L)} (d : ⊢¹ᶠ Γ) : (⌜d⌝ : V) = d.codeIn V := rfl

@[simp] lemma fstidx_quote {Γ : Finset (SyntacticFormula L)} (d : ⊢¹ᶠ Γ) : fstIdx (⌜d⌝ : V) = ⌜Γ⌝ := by
  induction d <;> simp [quote_derivation_def, codeIn]

end Derivation2

end LO.FirstOrder

namespace LO.Arith

open FirstOrder FirstOrder.Arith FirstOrder.Semiformula

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

open Classical

@[simp] lemma formulaSet_codeIn_finset (Γ : Finset (SyntacticFormula L)) : (L.codeIn V).FormulaSet ⌜Γ⌝ := by
  intro x hx
  rcases Derivation2.Sequent.mem_codeIn hx with ⟨p, _, rfl⟩;
  apply semiformula_quote

open Derivation2

lemma quote_image_shift (Γ : Finset (SyntacticFormula L)) : (L.codeIn V).setShift (⌜Γ⌝ : V) = ⌜Γ.image Rew.shift.hom⌝ := by
  induction Γ using Finset.induction
  case empty => simp
  case insert p Γ _ ih => simp [shift_quote, ih]

@[simp] lemma derivation_quote {Γ : Finset (SyntacticFormula L)} (d : ⊢¹ᶠ Γ) : (L.codeIn V).Derivation ⌜d⌝ := by
  induction d
  case axL p hp hn =>
    exact Language.Derivation.axL (by simp)
      (by simp [Sequent.mem_codeIn_iff, hp])
      (by simp [Sequent.mem_codeIn_iff, neg_quote, hn])
  case verum Δ h =>
    exact Language.Derivation.verumIntro (by simp)
      (by simpa [quote_verum] using (Sequent.mem_codeIn_iff (V := V)).mpr h)
  case and Δ p q hpq dp dq ihp ihq =>
    apply Language.Derivation.andIntro
      (by simpa using (Sequent.mem_codeIn_iff (V := V)).mpr hpq)
      ⟨by simp [fstidx_quote], ihp⟩
      ⟨by simp [fstidx_quote], ihq⟩
  case or Δ p q hpq d ih =>
    apply Language.Derivation.orIntro
      (by simpa using (Sequent.mem_codeIn_iff (V := V)).mpr hpq)
      ⟨by simp [fstidx_quote], ih⟩
  case all Δ p h d ih =>
    apply Language.Derivation.allIntro
      (by simpa using (Sequent.mem_codeIn_iff (V := V)).mpr h)
      ⟨by simp [fstidx_quote, quote_image_shift, free_quote], ih⟩
  case ex Δ p h t d ih =>
    apply Language.Derivation.exIntro
      (by simpa using (Sequent.mem_codeIn_iff (V := V)).mpr h)
      (semiterm_codeIn t)
      ⟨by simp [fstidx_quote, ←substs_quote, Language.substs₁], ih⟩
  case wk Δ Γ d h ih =>
    apply Language.Derivation.wkRule (s' := ⌜Δ⌝)
      (by simp)
      (by intro x hx; rcases Sequent.mem_codeIn hx with ⟨p, hp, rfl⟩
          simp [Sequent.mem_codeIn_iff, h hp])
      ⟨by simp [fstidx_quote], ih⟩
  case shift Δ d ih =>
    simp [quote_derivation_def, Derivation2.codeIn, ←quote_image_shift]
    apply Language.Derivation.shiftRule
      ⟨by simp [fstidx_quote], ih⟩
  case cut Δ p d dn ih ihn =>
    apply Language.Derivation.cutRule
      ⟨by simp [fstidx_quote], ih⟩
      ⟨by simp [fstidx_quote, neg_quote], ihn⟩

@[simp] lemma derivationOf_quote {Γ : Finset (SyntacticFormula L)} (d : ⊢¹ᶠ Γ) : (L.codeIn V).DerivationOf ⌜d⌝ ⌜Γ⌝ :=
  ⟨by simp, by simp⟩

section

class DefinableSigma₁Theory (T : Theory L) extends LDef.TDef L.lDef where
  mem_iff {σ} : σ ∈ T ↔ 𝐈𝚺₁ ⊢₌! ch.val/[⌜σ⌝]
  fvfree : 𝐈𝚺₁ ⊢₌! “∀ σ, !ch σ → !L.lDef.isFVFreeDef σ”

def _root_.LO.FirstOrder.Theory.tDef (T : Theory L) [d : DefinableSigma₁Theory T] : LDef.TDef L.lDef := d.toTDef

variable {T : Theory L} [DefinableSigma₁Theory T]

variable (T V)

def _root_.LO.FirstOrder.Theory.codeIn : (L.codeIn V).Theory where
  set := {x | V ⊧/![x] T.tDef.ch.val}
  set_fvFree := by
    intro x hx
    have : ∀ x, V ⊧/![x] T.tDef.ch.val → (L.codeIn V).IsFVFree x := by
      simpa [models_iff, (isFVFree_defined (V := V) (L.codeIn V)).df.iff] using
        consequence_iff_add_eq.mp (sound! <| DefinableSigma₁Theory.fvfree (T := T)) V inferInstance
    exact this x hx

variable {T V}

lemma Language.Theory.codeIn_iff : x ∈ T.codeIn V ↔ V ⊧/![x] T.tDef.ch.val := iff_of_eq rfl

lemma mem_coded_theory {σ} (h : σ ∈ T) : ⌜σ⌝ ∈ T.codeIn V := Language.Theory.codeIn_iff.mpr <| by
  have := consequence_iff_add_eq.mp (sound! <| DefinableSigma₁Theory.mem_iff.mp h) V inferInstance
  simpa [models_iff, Semiformula.sentence_goedelNumber_def, numeral_eq_natCast] using this

instance : (T.codeIn V).Defined T.tDef where
  defined := by intro v; simp [Theory.codeIn, ←Matrix.constant_eq_singleton']

theorem D1 : T ⊢! σ → (T.codeIn V).Provable ⌜σ⌝ := by {
  provable_iff_derivation2
  }

end

namespace Formalized

variable (T : Theory ℒₒᵣ)



end Formalized

end LO.Arith
