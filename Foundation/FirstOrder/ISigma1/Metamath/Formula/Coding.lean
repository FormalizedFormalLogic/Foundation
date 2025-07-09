import Foundation.FirstOrder.ISigma1.Metamath.Formula.Typed
import Foundation.FirstOrder.ISigma1.Metamath.Term.Coding

open Encodable LO FirstOrder Arithmetic PeanoMinus IOpen ISigma0 ISigma1 Metamath

namespace LO.FirstOrder.Semiformula

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable]

lemma quote_eq_toNat (φ : SyntacticSemiformula L n) : (⌜φ⌝ : V) = toNat φ := rfl

lemma quote_rel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) : (⌜rel R v⌝ : V) = ^rel ↑k ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝ := by
  simp [Semiterm.quote_eq_toNat, quote_eq_toNat, toNat, qqRel, ←nat_pair_eq, nat_cast_pair, quote_rel_def, ←quote_eq_vecToNat]; rfl

lemma quote_nrel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) : (⌜nrel R v⌝ : V) = ^nrel ↑k ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝ := by
  simp [Semiterm.quote_eq_toNat, quote_eq_toNat, toNat, ←nat_pair_eq, nat_cast_pair, quote_rel_def, ←quote_eq_vecToNat]; rfl

@[simp] lemma quote_verum (n : ℕ) : ⌜(⊤ : SyntacticSemiformula L n)⌝ = (^⊤ : V) := by
  simp [quote_eq_toNat, toNat, qqVerum, ←pair_coe_eq_coe_pair, nat_cast_pair]

@[simp] lemma quote_falsum (n : ℕ) : ⌜(⊥ : SyntacticSemiformula L n)⌝ = (^⊥ : V) := by
  simp [quote_eq_toNat, toNat, qqFalsum, ←pair_coe_eq_coe_pair, nat_cast_pair]

@[simp] lemma quote_and (φ ψ : SyntacticSemiformula L n) : (⌜φ ⋏ ψ⌝ : V) = ⌜φ⌝ ^⋏ ⌜ψ⌝ := by
  simp [quote_eq_toNat, toNat, qqAnd, ←pair_coe_eq_coe_pair, nat_cast_pair]

@[simp] lemma quote_or (φ ψ : SyntacticSemiformula L n) : (⌜φ ⋎ ψ⌝ : V) = ⌜φ⌝ ^⋎ ⌜ψ⌝ := by
  simp [quote_eq_toNat, toNat, qqOr, ←pair_coe_eq_coe_pair, nat_cast_pair]

@[simp] lemma quote_all (φ : SyntacticSemiformula L (n + 1)) : (⌜∀' φ⌝ : V) = ^∀ ⌜φ⌝ := by
  simp [quote_eq_toNat, toNat, qqAll, ←pair_coe_eq_coe_pair, nat_cast_pair]

@[simp] lemma quote_ex (φ : SyntacticSemiformula L (n + 1)) : (⌜∃' φ⌝ : V) = ^∃ ⌜φ⌝ := by
  simp [quote_eq_toNat, toNat, qqEx, ←pair_coe_eq_coe_pair, nat_cast_pair]

@[simp] lemma quote_eq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.rel Language.Eq.eq ![t, u]⌝ : V) = (⌜t⌝ ^= ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_rel]; rfl
@[simp] lemma quote_neq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.nrel Language.Eq.eq ![t, u]⌝ : V) = (⌜t⌝ ^≠ ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_nrel]; rfl

@[simp] lemma quote_lt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.rel Language.LT.lt ![t, u]⌝ : V) = (⌜t⌝ ^< ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_rel]; rfl

@[simp] lemma quote_nlt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.nrel Language.LT.lt ![t, u]⌝ : V) = (⌜t⌝ ^≮ ⌜u⌝) := by simp [FirstOrder.Semiformula.quote_nrel]; rfl

@[simp] lemma quote_neq' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜“!!t ≠ !!u”⌝ : V) = (⌜t⌝ ^≠ ⌜u⌝) := by simp [Semiformula.Operator.eq_def]

@[simp] lemma quote_eq' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜“!!t = !!u”⌝ : V) = (⌜t⌝ ^= ⌜u⌝) := by simp [Semiformula.Operator.eq_def]

@[simp] lemma quote_lt' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜“!!t < !!u”⌝ : V) = (⌜t⌝ ^< ⌜u⌝) := by simp [Semiformula.Operator.lt_def]

@[simp] lemma quote_nlt' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜“!!t ≮ !!u”⌝ : V) = (⌜t⌝ ^≮ ⌜u⌝) := by simp [Semiformula.Operator.lt_def]

@[simp] lemma quote_semisentence_def (φ : Semisentence L n) : ⌜(Rewriting.embedding φ : SyntacticSemiformula L n)⌝ = (⌜φ⌝ : V) := by
  simp [quote_eq_coe_encode]

lemma sentence_goedelNumber_def (σ : Sentence L) :
  (⌜σ⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.numeral ℒₒᵣ ⌜σ⌝ := by simp [Arithmetic.goedelNumber'_def, quote_eq_encode]

lemma syntacticformula_goedelNumber_def (φ : SyntacticFormula L) :
  (⌜φ⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.numeral ℒₒᵣ ⌜φ⌝ := by simp [Arithmetic.goedelNumber'_def, quote_eq_encode]

@[simp] lemma quote_weight (n : ℕ) : ⌜(weight k : SyntacticSemiformula L n)⌝ = (qqVerums k : V) := by
  unfold weight
  induction k <;> simp [quote_verum, quote_and, List.replicate, *]

end LO.FirstOrder.Semiformula

namespace LO.ISigma1.Metamath

open FirstOrder.Semiformula

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

@[simp] lemma semiformula_quote {n} (φ : SyntacticSemiformula L n) :
    IsSemiformula (V := V) L n (⌜φ⌝ : V) := by
  induction φ using Semiformula.rec'
  case hrel n k r v => simp [Semiformula.quote_rel]
  case hnrel n k r v => simp [Semiformula.quote_nrel]
  case hverum n => simp [Semiformula.quote_verum]
  case hfalsum n => simp [Semiformula.quote_falsum]
  case hand n φ ψ ihp ihq => simp [Semiformula.quote_and, ihp, ihq]
  case hor n φ ψ ihp ihq => simp [Semiformula.quote_or, ihp, ihq]
  case hall n φ ihp => simpa [Semiformula.quote_all] using ihp
  case hex n φ ihp => simpa [Semiformula.quote_ex] using ihp

@[simp] lemma semiformula_quote0 (φ : SyntacticFormula L) :
    IsFormula (V := V) L ⌜φ⌝ := by simpa using semiformula_quote φ

@[simp] lemma semiformula_quote1 (φ : SyntacticSemiformula L 1) :
    IsSemiformula (V := V) L 1 ⌜φ⌝ := by simpa using semiformula_quote (V := V) φ

@[simp] lemma semiformula_quote2 (φ : SyntacticSemiformula L 2) :
    IsSemiformula (V := V) L 2 ⌜φ⌝ := by simpa using semiformula_quote (V := V) φ

@[simp] lemma isUFormula_quote {n} (φ : SyntacticSemiformula L n) :
    IsUFormula (V := V) L ⌜φ⌝ := semiformula_quote φ |>.isUFormula

@[simp] lemma semiformula_quote_succ {n} (φ : SyntacticSemiformula L (n + 1)) :
    IsSemiformula (V := V) L (n + 1) ⌜φ⌝ := by simpa using semiformula_quote φ

@[simp] lemma quote_neg {n} (φ : SyntacticSemiformula L n) :
    (⌜∼φ⌝ : V) = neg L ⌜φ⌝ := by
  induction φ using Semiformula.rec' <;>
    simp [*, quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex]

@[simp] lemma quote_imply {n} (φ ψ : SyntacticSemiformula L n) :
    (⌜φ ➝ ψ⌝ : V) = imp L ⌜φ⌝ ⌜ψ⌝ := by
  simp [Semiformula.imp_eq, Semiformula.quote_or, quote_neg]; rfl

@[simp] lemma quote_iff {n} (φ ψ : SyntacticSemiformula L n) :
    (⌜φ ⭤ ψ⌝ : V) = iff L ⌜φ⌝ ⌜ψ⌝ := by
  simp [Semiformula.imp_eq, LogicalConnective.iff, Semiformula.quote_or, quote_neg]; rfl

@[simp] lemma quote_shift {n} (φ : SyntacticSemiformula L n) :
    (⌜Rewriting.shift φ⌝ : V) = shift L ⌜φ⌝ := by
  induction φ using Semiformula.rec' <;>
    simp [*, quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all, quote_ex,
      rew_rel, rew_nrel, ←quote_termShiftVec]

lemma qVec_quote (w : Fin n → SyntacticSemiterm L m) :
    qVec (V := V) L ⌜fun i ↦ ⌜w i⌝⌝ = ⌜^#0 :> fun i ↦ (⌜Rew.bShift (w i)⌝ : V)⌝ := by
  have Hw : IsSemitermVec (V := V) L ↑n (↑m + 1) (termBShiftVec L ↑n ⌜fun i ↦ ⌜w i⌝⌝) :=
    (semitermVec_codeIn w).termBShiftVec
  have HqVec : IsSemitermVec (V := V) L (↑n + 1) (↑m + 1) (qVec L ⌜fun i ↦ ⌜w i⌝⌝) :=
    (semitermVec_codeIn w).qVec
  apply nth_ext (by simp [←HqVec.lh])
  intro i hi
  have : i < ↑(n + 1) := by simpa [qVec, Hw.lh] using hi
  rcases eq_fin_of_lt_nat this with ⟨i, rfl⟩
  cases' i using Fin.cases with i
  · simp [qVec]
  · simp [qVec, quote_termBShift]

@[simp] lemma quote_substs {n m} (w : Fin n → SyntacticSemiterm L m) (φ : SyntacticSemiformula L n) :
    ⌜φ ⇜ w⌝ = substs (V := V) L ⌜fun i ↦ ⌜w i⌝⌝ ⌜φ⌝ := by
  induction φ using Semiformula.rec' generalizing m
  case hrel => simp [quote_rel, rew_rel, ←quote_termSubstVec]
  case hnrel => simp [quote_nrel, rew_nrel, ←quote_termSubstVec]
  case hverum => simp
  case hfalsum => simp
  case hand => simp [*]
  case hor => simp [*]
  case hall φ ih =>
    simp [*, quote_all, Rew.q_substs, qVec_quote, Semiterm.quote_bvar, Matrix.comp_vecCons']
  case hex φ ih =>
    simp [*, quote_ex, Rew.q_substs, qVec_quote, Semiterm.quote_bvar, Matrix.comp_vecCons']

omit  [L.LORDefinable] in
lemma quote_sentence_eq_quote_emb (σ : Semisentence L n) : (⌜σ⌝ : V) = ⌜Rew.embs ▹ σ⌝ := by simp [quote_eq_coe_encode]

lemma quote_substs' {n m} (w : Fin n → FirstOrder.Semiterm L Empty m) (σ : Semisentence L n) :
    ⌜σ ⇜ w⌝ = substs (V := V) L ⌜fun i ↦ ⌜w i⌝⌝ ⌜σ⌝ := by
  let w' : Fin n → SyntacticSemiterm L m := fun i ↦ Rew.emb (w i)
  suffices (Rew.substs w').comp Rew.embs = Rew.embs.comp (Rew.substs w) by
    have : (⌜fun i ↦ ⌜w i⌝⌝ : V) = ⌜fun i ↦ ⌜w' i⌝⌝ := by
      apply nth_ext' (↑n) (by simp) (by simp)
      intro i hi;
      rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
      simp [w', quote_eterm_eq_quote_emb]
    symm
    rw [quote_sentence_eq_quote_emb, this, ←quote_substs, quote_sentence_eq_quote_emb]
    congr 1
    simp [← TransitiveRewriting.comp_app]; congr 2
  ext x
  · simp [w', Rew.comp_app]
  · contradiction

@[simp] lemma free_quote (φ : SyntacticSemiformula L 1) :
    ⌜Rewriting.free φ⌝ = free (V := V) L ⌜φ⌝ := by
  rw [← LawfulSyntacticRewriting.app_substs_fbar_zero_comp_shift_eq_free, quote_substs, quote_shift]
  simp [free, substs1, Semiterm.quote_fvar, Matrix.constant_eq_singleton]

end LO.ISigma1.Metamath
