module

public import Foundation.Vorspiel.Tactic.Disj
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

/-!
# Internal evaluation of terms

`termVal e t` evaluates the coded `ℒₒᵣ`-term `t` under the coded assignment `e` of its bound
variables, reading free variables as `0`; `termVal' f e t` reads free variables from `f` instead.
Both are `𝚺ᴬ₁`-definable, commute with the arithmetic operations, substitution and shifts, and
agree with the external evaluation on quoted closed terms.

## References

- [HP98, 1.63, 1.64, 1.66, 1.67, remark after 2.58]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma quote_zeroIndex_eq : (⌜(Language.ORing.Func.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 :=
  Arithmetic.coe_zeroIndex_eq

lemma quote_oneIndex_eq : (⌜(Language.ORing.Func.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 :=
  Arithmetic.coe_oneIndex_eq

lemma quote_addIndex_eq : (⌜(Language.ORing.Func.add : (ℒₒᵣ).Func 2)⌝ : V) = 0 :=
  Arithmetic.coe_addIndex_eq

lemma quote_mulIndex_eq : (⌜(Language.ORing.Func.mul : (ℒₒᵣ).Func 2)⌝ : V) = 1 :=
  Arithmetic.coe_mulIndex_eq

lemma isFunc_LOR_iff {k f : V} :
    (ℒₒᵣ).IsFunc k f ↔ (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) := by
  rw [Arithmetic.isFunc_iff_LOR,
    show (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 from quote_zeroIndex_eq,
    show (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 from quote_oneIndex_eq,
    show (⌜(Language.Add.add : (ℒₒᵣ).Func 2)⌝ : V) = 0 from quote_addIndex_eq,
    show (⌜(Language.Mul.mul : (ℒₒᵣ).Func 2)⌝ : V) = 1 from quote_mulIndex_eq];

lemma add_le_pair (a b : V) : a + b ≤ ⟪a, b⟫ := by
  have sq : ∀ c : V, c ≤ c * c := fun c ↦ by
    rcases eq_zero_or_pos c with rfl | hc;
    · simp;
    · exact le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hc);
  rcases lt_or_ge a b with h | h;
  · calc a + b
        ≤ a + b * b := add_le_add le_rfl (sq b)
      _ = ⟪a, b⟫ := by simp [pair, h, add_comm];
  · calc a + b
        ≤ a * a + a + b := add_le_add (le_trans (sq a) le_self_add) le_rfl
      _ = ⟪a, b⟫ := by simp [pair, not_lt.mpr h];

lemma add_lt_qqFunc (k f a b : V) : a + b < ^func k f ?[a, b] :=
  calc a + b
      < a + (b ∷ (0 : V)) := add_lt_add_of_le_of_lt le_rfl (lt_adjoin b 0)
    _ ≤ ⟪a, b ∷ (0 : V)⟫ := add_le_pair _ _
    _ < ?[a, b] := by simp [adjoin_def]
    _ < ^func k f ?[a, b] := terms_lt_qqFunc _ _ _

lemma nth_le_listMax_total (v i : V) : v.[i] ≤ listMax v := by
  rcases lt_or_ge i (len v) with h | h;
  · exact nth_le_listMax h;
  · simp [nth_lt_len h];

lemma qqAdd_eq_qqFunc (a b : V) : (a ^+ b : V) = ^func (2 : V) (0 : V) (?[a, b] : V) := by
  rw [Arithmetic.qqAdd, Arithmetic.coe_addIndex_eq];

lemma qqMul_eq_qqFunc (a b : V) : (a ^* b : V) = ^func (2 : V) (1 : V) (?[a, b] : V) := by
  rw [Arithmetic.qqMul, Arithmetic.coe_mulIndex_eq];

lemma qqZero_eq_qqFunc : (𝟎 : V) = ^func (0 : V) (0 : V) (0 : V) := by
  rw [Arithmetic.coe_zero_eq,
    show (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 from quote_zeroIndex_eq];

lemma qqOne_eq_qqFunc : (𝟏 : V) = ^func (0 : V) (1 : V) (0 : V) := by
  rw [Arithmetic.coe_one_eq,
    show (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 from quote_oneIndex_eq];

namespace TermVal

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z w. !nthDef y w z”
  fvar := .mkSigma “y x w. y = 0”
  func := .mkSigma
    “y k f v v' w.
      (k = 0 ∧ f = 0 → y = 0) ∧
      (k = 0 ∧ f = 1 → y = 1) ∧
      (k = 2 ∧ f = 0 → ∃ a, !nthDef a v' 0 ∧ ∃ b, !nthDef b v' 1 ∧ y = a + b) ∧
      (k = 2 ∧ f = 1 → ∃ a, !nthDef a v' 0 ∧ ∃ b, !nthDef b v' 1 ∧ y = a * b) ∧
      (¬(k = 0 ∧ f = 0) → ¬(k = 0 ∧ f = 1) → ¬(k = 2 ∧ f = 0) → ¬(k = 2 ∧ f = 1) → y = 0)”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (param z)        := (param 0).[z]
  fvar (_     _)        := 0
  func (_     k f _ v') :=
    if k = 0 ∧ f = 0 then 0
    else if k = 0 ∧ f = 1 then 1
    else if k = 2 ∧ f = 0 then v'.[0] + v'.[1]
    else if k = 2 ∧ f = 1 then v'.[0] * v'.[1]
    else 0
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by
    simp only [blueprint];
    split_ifs with h1 h2 h3 h4 <;> simp_all;
    tauto;

end TermVal

section termVal

open TermVal

noncomputable def termVal (e t : V) : V := construction.result ℒₒᵣ ![e] t

noncomputable def termValVec (e k v : V) : V := construction.resultVec ℒₒᵣ ![e] k v

noncomputable def termValGraph : 𝚺ᴬ₁.Semisentence 3 :=
  (blueprint.result ℒₒᵣ).rew <| Rew.subst ![#0, #2, #1]

noncomputable def termValVecGraph : 𝚺ᴬ₁.Semisentence 4 :=
  (blueprint.resultVec ℒₒᵣ).rew <| Rew.subst ![#0, #2, #3, #1]

@[simp] lemma termVal_bvar (e z : V) : termVal e ^#z = e.[z] := by simp [termVal, construction]

@[simp] lemma termVal_fvar (e x : V) : termVal e ^&x = 0 := by simp [termVal, construction]

section

instance termVal.defined : 𝚺ᴬ₁-Function₂ (termVal : V → V → V) via termValGraph := .mk fun v ↦ by
  simpa [termValGraph, termVal, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined.defined ![v 0, v 2, v 1];

instance termVal.definable : 𝚫ᴬ₁-Function₂ (termVal : V → V → V) :=
  termVal.defined.graph_delta.to_definable

instance termValVec.defined : 𝚺ᴬ₁-Function₃ (termValVec : V → V → V → V) via termValVecGraph :=
  .mk fun v ↦ by
  simpa [termValVecGraph, termValVec, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using (construction.resultVec_defined (L := ℒₒᵣ)).defined ![v 0, v 2, v 3, v 1];

instance termValVec.definable : 𝚫ᴬ₁-Function₃ (termValVec : V → V → V → V) :=
  termValVec.defined.graph_delta.to_definable

end

@[simp] lemma len_termValVec {e k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    len (termValVec e k v) = k := construction.resultVec_lh ℒₒᵣ _ hv

@[simp] lemma nth_termValVec {e k v i : V} (hv : IsUTermVec ℒₒᵣ k v) (hi : i < k) :
    (termValVec e k v).[i] = termVal e v.[i] := construction.nth_resultVec ℒₒᵣ _ hv hi

@[simp] lemma termVal_zero (e : V) : termVal e (𝟎 : V) = 0 := by
  have hkf : (ℒₒᵣ).IsFunc (0 : V) (0 : V) := isFunc_LOR_iff.mpr (by disj 1; exact ⟨rfl, rfl⟩);
  have hv : IsUTermVec ℒₒᵣ (0 : V) (0 : V) := by simp;
  have heq : (𝟎 : V) = ^func (0 : V) (0 : V) (0 : V) := qqZero_eq_qqFunc;
  change construction.result ℒₒᵣ ![e] (𝟎 : V) = 0;
  rw [heq, construction.result_func' hkf hv];
  simp [construction];

@[simp] lemma termVal_one (e : V) : termVal e (𝟏 : V) = 1 := by
  have hkf : (ℒₒᵣ).IsFunc (0 : V) (1 : V) := isFunc_LOR_iff.mpr (by disj 2; exact ⟨rfl, rfl⟩);
  have hv : IsUTermVec ℒₒᵣ (0 : V) (0 : V) := by simp;
  have heq : (𝟏 : V) = ^func (0 : V) (1 : V) (0 : V) := qqOne_eq_qqFunc;
  change construction.result ℒₒᵣ ![e] (𝟏 : V) = 1;
  rw [heq, construction.result_func' hkf hv];
  simp [construction];

@[simp] lemma termVal_add {e t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    termVal e (t ^+ u) = termVal e t + termVal e u := by
  have hkf : (ℒₒᵣ).IsFunc (2 : V) (0 : V) :=
    isFunc_LOR_iff.mpr (by disj 3; exact ⟨rfl, rfl⟩);
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  have heq : (t ^+ u : V) = ^func (2 : V) (0 : V) (?[t, u] : V) := qqAdd_eq_qqFunc t u;
  have step : termVal e (^func (2 : V) (0 : V) (?[t, u] : V)) =
      construction.func ![e] 2 0 (?[t, u] : V) (termValVec e 2 (?[t, u] : V)) :=
    construction.result_func' hkf hv;
  rw [heq, step];
  simp [construction, nth_termValVec hv (show (0 : V) < 2 by simp),
    nth_termValVec hv (show (1 : V) < 2 by simp)];

@[simp] lemma termVal_mul {e t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    termVal e (t ^* u) = termVal e t * termVal e u := by
  have hkf : (ℒₒᵣ).IsFunc (2 : V) (1 : V) :=
    isFunc_LOR_iff.mpr (by disj 4; exact ⟨rfl, rfl⟩);
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  have heq : (t ^* u : V) = ^func (2 : V) (1 : V) (?[t, u] : V) := qqMul_eq_qqFunc t u;
  have step : termVal e (^func (2 : V) (1 : V) (?[t, u] : V)) =
      construction.func ![e] 2 1 (?[t, u] : V) (termValVec e 2 (?[t, u] : V)) :=
    construction.result_func' hkf hv;
  rw [heq, step];
  simp [construction, nth_termValVec hv (show (0 : V) < 2 by simp),
    nth_termValVec hv (show (1 : V) < 2 by simp)];

lemma termVal_not_uterm {e t : V} (h : ¬IsUTerm ℒₒᵣ t) : termVal e t = 0 := by
  change construction.result ℒₒᵣ ![e] t = 0;
  exact construction.result_prop_not ℒₒᵣ ![e] h;

lemma termVal_termSubst {e n m w t : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t) :
    termVal e (termSubst ℒₒᵣ w t) = termVal (termValVec e n w) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht;
  · definability;
  · intro z hz; rw [termSubst_bvar, termVal_bvar, nth_termValVec hw.isUTerm hz];
  · intro x; simp;
  · intro k f v hf hv ih;
    rw [termSubst_func hf hv.isUTerm];
    have hv' : IsUTermVec ℒₒᵣ k (termSubstVec ℒₒᵣ k w v) := (hw.termSubstVec hv).isUTerm;
    have key : termValVec e k (termSubstVec ℒₒᵣ k w v) = termValVec (termValVec e n w) k v := by
      apply nth_ext' k (by simp [hv']) (by simp [hv.isUTerm]);
      intro i hi;
      rw [nth_termValVec hv' hi, nth_termSubstVec hv.isUTerm hi, ih i hi,
        nth_termValVec hv.isUTerm hi];
    have step1 : termVal e (^func k f (termSubstVec ℒₒᵣ k w v)) =
        construction.func ![e] k f (termSubstVec ℒₒᵣ k w v)
          (termValVec e k (termSubstVec ℒₒᵣ k w v)) :=
      construction.result_func' hf hv';
    have step2 : termVal (termValVec e n w) (^func k f v) =
        construction.func ![termValVec e n w] k f v (termValVec (termValVec e n w) k v) :=
      construction.result_func' hf hv.isUTerm;
    rw [step1, step2, key];
    simp [construction];

lemma termVal_termBShift {t : V} (ht : IsUTerm ℒₒᵣ t) (x e : V) :
    termVal (x ∷ e) (termBShift ℒₒᵣ t) = termVal e t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht;
  · definability;
  · intro z; simp [termBShift_bvar];
  · intro x'; simp;
  · intro k f v hf hv ih;
    rw [termBShift_func hf hv];
    have hv' : IsUTermVec ℒₒᵣ k (termBShiftVec ℒₒᵣ k v) := hv.isSemitermVec.termBShiftVec.isUTerm;
    have key : termValVec (x ∷ e) k (termBShiftVec ℒₒᵣ k v) = termValVec e k v := by
      apply nth_ext' k (by simp [hv']) (by simp [hv]);
      intro i hi;
      rw [nth_termValVec hv' hi, nth_termBShiftVec hv hi, ih i hi, nth_termValVec hv hi];
    have step1 : termVal (x ∷ e) (^func k f (termBShiftVec ℒₒᵣ k v)) =
        construction.func ![x ∷ e] k f (termBShiftVec ℒₒᵣ k v)
          (termValVec (x ∷ e) k (termBShiftVec ℒₒᵣ k v)) :=
      construction.result_func' hf hv';
    have step2 : termVal e (^func k f v) =
        construction.func ![e] k f v (termValVec e k v) :=
      construction.result_func' hf hv;
    rw [step1, step2, key];
    simp [construction];

lemma termVal_termShift {t : V} (ht : IsUTerm ℒₒᵣ t) (e : V) :
    termVal e (termShift ℒₒᵣ t) = termVal e t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht;
  · definability;
  · intro z; simp;
  · intro x; simp;
  · intro k f v hf hv ih;
    rw [termShift_func hf hv];
    have hv' : IsUTermVec ℒₒᵣ k (termShiftVec ℒₒᵣ k v) := IsUTermVec.termShiftVec hv;
    have key : termValVec e k (termShiftVec ℒₒᵣ k v) = termValVec e k v := by
      apply nth_ext' k (by simp [hv']) (by simp [hv]);
      intro i hi;
      rw [nth_termValVec hv' hi, nth_termShiftVec hv hi, ih i hi, nth_termValVec hv hi];
    have step1 : termVal e (^func k f (termShiftVec ℒₒᵣ k v)) =
        construction.func ![e] k f (termShiftVec ℒₒᵣ k v) (termValVec e k (termShiftVec ℒₒᵣ k v)) :=
      construction.result_func' hf hv';
    have step2 : termVal e (^func k f v) =
        construction.func ![e] k f v (termValVec e k v) :=
      construction.result_func' hf hv;
    rw [step1, step2, key];
    simp [construction];

lemma termVal_quote {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) (v : Fin k → V) :
    termVal (matrixToVec v) ⌜t⌝ = t.valb v := by
  induction t with
  | bvar x => simp [Semiterm.empty_quote_eq, Semiterm.valb]
  | fvar x => exact x.elim
  | @func k' f w ih =>
    match k', f, w, ih with
    | 0, .zero, w, _ =>
      have hz : termVal (matrixToVec v) (^func (0 : V) (0 : V) (0 : V)) = 0 := by
        rw [← qqZero_eq_qqFunc (V := V)];
        exact termVal_zero _;
      simp [Semiterm.empty_quote_eq, Semiterm.valb, quote_zeroIndex_eq, hz];
      rfl;
    | 0, .one, w, _ =>
      have ho : termVal (matrixToVec v) (^func (0 : V) (1 : V) (0 : V)) = 1 := by
        rw [← qqOne_eq_qqFunc (V := V)];
        exact termVal_one _;
      simp [Semiterm.empty_quote_eq, Semiterm.valb, quote_oneIndex_eq, ho];
      rfl;
    | 2, .add, w, ih =>
      have ht : IsUTerm ℒₒᵣ (⌜w 0⌝ : V) := by simp [Semiterm.empty_quote_eq];
      have hu : IsUTerm ℒₒᵣ (⌜w 1⌝ : V) := by simp [Semiterm.empty_quote_eq];
      have heq : (⌜(FirstOrder.Semiterm.func Language.ORing.Func.add w : ClosedSemiterm ℒₒᵣ k)⌝ : V)
        = (⌜w 0⌝ : V) ^+ ⌜w 1⌝ := by
        simp [Semiterm.empty_quote_eq, Arithmetic.qqAdd, quote_addIndex_eq,
          Arithmetic.coe_addIndex_eq,
          Matrix.vecHead, Matrix.vecTail];
      rw [heq, termVal_add ht hu, ih 0, ih 1];
      simp [Semiterm.valb];
      rfl;
    | 2, .mul, w, ih =>
      have ht : IsUTerm ℒₒᵣ (⌜w 0⌝ : V) := by simp [Semiterm.empty_quote_eq];
      have hu : IsUTerm ℒₒᵣ (⌜w 1⌝ : V) := by simp [Semiterm.empty_quote_eq];
      have heq : (⌜(FirstOrder.Semiterm.func Language.ORing.Func.mul w : ClosedSemiterm ℒₒᵣ k)⌝ : V)
        = (⌜w 0⌝ : V) ^* ⌜w 1⌝ := by
        simp [Semiterm.empty_quote_eq, Arithmetic.qqMul, quote_mulIndex_eq,
          Arithmetic.coe_mulIndex_eq,
          Matrix.vecHead, Matrix.vecTail];
      rw [heq, termVal_mul ht hu, ih 0, ih 1];
      simp [Semiterm.valb];
      rfl;

theorem termVal_le_poly (e t : V) : termVal e t ≤ Exp.exp ((listMax e + 2) * (t + 1)) := by
  by_cases ht : IsUTerm ℒₒᵣ t;
  case neg => simp [termVal_not_uterm ht];
  revert t;
  apply IsUTerm.induction (L := ℒₒᵣ) 𝚷
    (P := fun t ↦ termVal e t ≤ Exp.exp ((listMax e + 2) * (t + 1))) ?_ ?_ ?_ ?_;
  · definability;
  · intro z;
    calc termVal e ^#z
        = e.[z] := by simp
      _ ≤ listMax e := nth_le_listMax_total e z
      _ ≤ (listMax e + 2) * (^#z + 1) :=
          le_trans (by simp) (le_mul_of_one_le_right (by simp) (by simp))
      _ ≤ Exp.exp ((listMax e + 2) * (^#z + 1)) := le_of_lt (lt_exp _);
  · intro x; simp;
  · intro k f v hkf hv ih;
    rcases isFunc_LOR_iff.mp hkf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩;
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.lh.symm;
      have hzero : (^func (0 : V) (0 : V) (0 : V)) = (𝟎 : V) := qqZero_eq_qqFunc.symm;
      rw [hv0, hzero];
      simp;
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.lh.symm;
      have hone : (^func (0 : V) (1 : V) (0 : V)) = (𝟏 : V) := qqOne_eq_qqFunc.symm;
      rw [hv0, hone];
      simp;
    · rcases IsUTermVec.two_iff.mp hv with ⟨a, b, ha, hb, rfl⟩;
      have heq : (a ^+ b : V) = ^func (2 : V) (0 : V) ?[a, b] := qqAdd_eq_qqFunc a b;
      have hab : a + b + 1 ≤ a ^+ b := succ_le_iff_lt.mpr (heq ▸ add_lt_qqFunc 2 0 a b);
      have iha : termVal e a ≤ Exp.exp ((listMax e + 2) * (a + 1)) := by
        simpa using ih 0 (by simp);
      have ihb : termVal e b ≤ Exp.exp ((listMax e + 2) * (b + 1)) := by
        simpa using ih 1 (by simp);
      have hM : (1 : V) ≤ listMax e + 2 := le_trans (by simp) le_add_self;
      rw [← heq, termVal_add ha hb];
      calc termVal e a + termVal e b
          ≤ Exp.exp ((listMax e + 2) * (a + 1)) + Exp.exp ((listMax e + 2) * (b + 1)) :=
            add_le_add iha ihb
        _ ≤ Exp.exp ((listMax e + 2) * (a ^+ b)) + Exp.exp ((listMax e + 2) * (a ^+ b)) :=
            add_le_add
              (exp_monotone_le.mpr <|
                mul_le_mul le_rfl (le_trans (by simp) hab) (by simp) (by simp))
              (exp_monotone_le.mpr <|
                mul_le_mul le_rfl (le_trans (by simp) hab) (by simp) (by simp))
        _ = Exp.exp ((listMax e + 2) * (a ^+ b) + 1) := by rw [exp_succ, two_mul]
        _ ≤ Exp.exp ((listMax e + 2) * (a ^+ b + 1)) := by
            rw [exp_monotone_le, mul_add, mul_one];
            exact add_le_add le_rfl hM;
    · rcases IsUTermVec.two_iff.mp hv with ⟨a, b, ha, hb, rfl⟩;
      have heq : (a ^* b : V) = ^func (2 : V) (1 : V) ?[a, b] := qqMul_eq_qqFunc a b;
      have hab : a + b + 1 ≤ a ^* b := succ_le_iff_lt.mpr (heq ▸ add_lt_qqFunc 2 1 a b);
      have iha : termVal e a ≤ Exp.exp ((listMax e + 2) * (a + 1)) := by
        simpa using ih 0 (by simp);
      have ihb : termVal e b ≤ Exp.exp ((listMax e + 2) * (b + 1)) := by
        simpa using ih 1 (by simp);
      have hab' : (a + 1) + (b + 1) ≤ a ^* b + 1 :=
        le_trans (le_of_eq (by simp [add_assoc, add_comm, add_left_comm])) (add_le_add hab le_rfl);
      rw [← heq, termVal_mul ha hb];
      calc termVal e a * termVal e b
          ≤ Exp.exp ((listMax e + 2) * (a + 1)) * Exp.exp ((listMax e + 2) * (b + 1)) :=
            mul_le_mul iha ihb (by simp) (by simp)
        _ = Exp.exp ((listMax e + 2) * (a + 1) + (listMax e + 2) * (b + 1)) := (exp_add _ _).symm
        _ ≤ Exp.exp ((listMax e + 2) * (a ^* b + 1)) := by
            rw [exp_monotone_le, ← mul_add];
            exact mul_le_mul le_rfl hab' (by simp) (by simp);

end termVal

namespace TermValFree

def blueprint : Language.TermRec.Blueprint 2 where
  bvar := .mkSigma “y z f e. !nthDef y e z”
  fvar := .mkSigma “y x f e. !nthDef y f x”
  func := .mkSigma
    “y k g v v' f e.
      (k = 0 ∧ g = 0 → y = 0) ∧
      (k = 0 ∧ g = 1 → y = 1) ∧
      (k = 2 ∧ g = 0 → ∃ a, !nthDef a v' 0 ∧ ∃ b, !nthDef b v' 1 ∧ y = a + b) ∧
      (k = 2 ∧ g = 1 → ∃ a, !nthDef a v' 0 ∧ ∃ b, !nthDef b v' 1 ∧ y = a * b) ∧
      (¬(k = 0 ∧ g = 0) → ¬(k = 0 ∧ g = 1) → ¬(k = 2 ∧ g = 0) →
        ¬(k = 2 ∧ g = 1) → y = 0)”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (param z)        := (param 1).[z]
  fvar (param x)        := (param 0).[x]
  func (_     k g _ v') :=
    if k = 0 ∧ g = 0 then 0
    else if k = 0 ∧ g = 1 then 1
    else if k = 2 ∧ g = 0 then v'.[0] + v'.[1]
    else if k = 2 ∧ g = 1 then v'.[0] * v'.[1]
    else 0
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by
    simp only [blueprint];
    split_ifs with h1 h2 h3 h4 <;> simp_all;
    tauto;

end TermValFree

section termValFree

open TermValFree

noncomputable def termVal' (f e t : V) : V := construction.result ℒₒᵣ ![f, e] t

noncomputable def termValVec' (f e k v : V) : V :=
  construction.resultVec ℒₒᵣ (fun i ↦ ![f, e] i) k v

noncomputable def termVal'Graph : 𝚺ᴬ₁.Semisentence 4 :=
  (blueprint.result ℒₒᵣ).rew <| Rew.subst ![#0, #3, #1, #2]

noncomputable def termValVec'Graph : 𝚺ᴬ₁.Semisentence 5 :=
  (blueprint.resultVec ℒₒᵣ).rew <| Rew.subst ![#0, #3, #4, #1, #2]

@[simp] lemma termVal'_bvar (f e z : V) : termVal' f e ^#z = e.[z] := by
  simp [termVal', construction];

@[simp] lemma termVal'_fvar (f e x : V) : termVal' f e ^&x = f.[x] := by
  simp [termVal', construction];

section

instance termVal'.defined : 𝚺ᴬ₁-Function₃ (termVal' : V → V → V → V) via termVal'Graph :=
  .mk fun v ↦ by
  simpa [termVal'Graph, termVal', Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined.defined ![v 0, v 3, v 1, v 2];

instance termVal'.definable : 𝚫ᴬ₁-Function₃ (termVal' : V → V → V → V) :=
  termVal'.defined.graph_delta.to_definable

instance termValVec'.defined : 𝚺ᴬ₁-Function₄ (termValVec' : V → V → V → V → V) via
    termValVec'Graph :=
  .mk fun v ↦ by
    simpa [termValVec'Graph, termValVec', Matrix.constant_eq_singleton, Matrix.comp_vecCons',
      Function.comp_def]
      using! (construction.resultVec_defined (L := ℒₒᵣ)).defined ![v 0, v 3, v 4, v 1, v 2];

instance termValVec'.definable : 𝚫ᴬ₁-Function₄ (termValVec' : V → V → V → V → V) :=
  termValVec'.defined.graph_delta.to_definable

end

@[simp] lemma len_termValVec' {f e k v : V} (hv : IsUTermVec ℒₒᵣ k v) :
    len (termValVec' f e k v) = k := construction.resultVec_lh ℒₒᵣ _ hv

@[simp] lemma nth_termValVec' {f e k v i : V} (hv : IsUTermVec ℒₒᵣ k v) (hi : i < k) :
    (termValVec' f e k v).[i] = termVal' f e v.[i] :=
  construction.nth_resultVec ℒₒᵣ _ hv hi

@[simp] lemma termVal'_add {f e t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    termVal' f e (t ^+ u) = termVal' f e t + termVal' f e u := by
  have hkf : (ℒₒᵣ).IsFunc (2 : V) (0 : V) :=
    isFunc_LOR_iff.mpr (by disj 3; exact ⟨rfl, rfl⟩);
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  have heq : (t ^+ u : V) = ^func (2 : V) (0 : V) (?[t, u] : V) := qqAdd_eq_qqFunc t u;
  have step : termVal' f e (^func (2 : V) (0 : V) (?[t, u] : V)) =
      construction.func ![f, e] 2 0 (?[t, u] : V) (termValVec' f e 2 (?[t, u] : V)) :=
    construction.result_func' hkf hv;
  rw [heq, step];
  simp [construction, nth_termValVec' hv (show (0 : V) < 2 by simp),
    nth_termValVec' hv (show (1 : V) < 2 by simp)];

@[simp] lemma termVal'_mul {f e t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    termVal' f e (t ^* u) = termVal' f e t * termVal' f e u := by
  have hkf : (ℒₒᵣ).IsFunc (2 : V) (1 : V) :=
    isFunc_LOR_iff.mpr (by disj 4; exact ⟨rfl, rfl⟩);
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  have heq : (t ^* u : V) = ^func (2 : V) (1 : V) (?[t, u] : V) := qqMul_eq_qqFunc t u;
  have step : termVal' f e (^func (2 : V) (1 : V) (?[t, u] : V)) =
      construction.func ![f, e] 2 1 (?[t, u] : V) (termValVec' f e 2 (?[t, u] : V)) :=
    construction.result_func' hkf hv;
  rw [heq, step];
  simp [construction, nth_termValVec' hv (show (0 : V) < 2 by simp),
    nth_termValVec' hv (show (1 : V) < 2 by simp)];

lemma termVal'_not_uterm {f e t : V} (h : ¬IsUTerm ℒₒᵣ t) : termVal' f e t = 0 := by
  exact construction.result_prop_not ℒₒᵣ ![f, e] h;

lemma termVal'_empty (e t : V) : termVal' 0 e t = termVal e t := by
  by_cases ht : IsUTerm ℒₒᵣ t;
  · revert t;
    apply IsUTerm.induction (L := ℒₒᵣ) 𝚺 (P := fun t ↦ termVal' 0 e t = termVal e t) ?_ ?_ ?_ ?_;
    · definability;
    · intro z; simp;
    · intro x; simp;
    · intro k g v hkg hv ih;
      have key : termValVec' 0 e k v = termValVec e k v := by
        apply nth_ext' k (by simp [hv]) (by simp [hv]);
        intro i hi;
        rw [nth_termValVec' hv hi, nth_termValVec hv hi, ih i hi];
      have step1 : termVal' 0 e (^func k g v) =
          construction.func ![0, e] k g v (termValVec' 0 e k v) :=
        construction.result_func' hkg hv;
      have step2 : termVal e (^func k g v) =
          TermVal.construction.func ![e] k g v (termValVec e k v) :=
        TermVal.construction.result_func' hkg hv;
      rw [step1, step2, key];
      simp [construction, TermVal.construction];
  · simp [termVal'_not_uterm ht, termVal_not_uterm ht];

lemma termVal'_termSubst {f e n m w t : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (ht : IsSemiterm ℒₒᵣ n t) :
    termVal' f e (termSubst ℒₒᵣ w t) = termVal' f (termValVec' f e n w) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht;
  · definability;
  · intro z hz;
    rw [termSubst_bvar, termVal'_bvar, nth_termValVec' hw.isUTerm hz];
  · intro x; simp;
  · intro k g v hkg hv ih;
    rw [termSubst_func hkg hv.isUTerm];
    have hv' : IsUTermVec ℒₒᵣ k (termSubstVec ℒₒᵣ k w v) :=
      (hw.termSubstVec hv).isUTerm;
    have key : termValVec' f e k (termSubstVec ℒₒᵣ k w v) =
        termValVec' f (termValVec' f e n w) k v := by
      apply nth_ext' k (by simp [hv']) (by simp [hv.isUTerm]);
      intro i hi;
      rw [nth_termValVec' hv' hi, nth_termSubstVec hv.isUTerm hi, ih i hi,
        nth_termValVec' hv.isUTerm hi];
    have step1 : termVal' f e (^func k g (termSubstVec ℒₒᵣ k w v)) =
        construction.func ![f, e] k g (termSubstVec ℒₒᵣ k w v)
          (termValVec' f e k (termSubstVec ℒₒᵣ k w v)) :=
      construction.result_func' hkg hv';
    have step2 : termVal' f (termValVec' f e n w) (^func k g v) =
        construction.func ![f, termValVec' f e n w] k g v
          (termValVec' f (termValVec' f e n w) k v) :=
      construction.result_func' hkg hv.isUTerm;
    rw [step1, step2, key];
    simp [construction];

lemma termVal'_termShift {f e t : V} (ht : IsUTerm ℒₒᵣ t) :
    termVal' f e (termShift ℒₒᵣ t) = termVal' (sndIdx f) e t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht;
  · definability;
  · intro z; simp;
  · intro x;
    simp [termShift_fvar, nth_succ];
  · intro k g v hkg hv ih;
    rw [termShift_func hkg hv];
    have hv' : IsUTermVec ℒₒᵣ k (termShiftVec ℒₒᵣ k v) := hv.termShiftVec;
    have key : termValVec' f e k (termShiftVec ℒₒᵣ k v) =
        termValVec' (sndIdx f) e k v := by
      apply nth_ext' k (by simp [hv']) (by simp [hv]);
      intro i hi;
      rw [nth_termValVec' hv' hi, nth_termShiftVec hv hi, ih i hi,
        nth_termValVec' hv hi];
    have step1 : termVal' f e (^func k g (termShiftVec ℒₒᵣ k v)) =
        construction.func ![f, e] k g (termShiftVec ℒₒᵣ k v)
          (termValVec' f e k (termShiftVec ℒₒᵣ k v)) :=
      construction.result_func' hkg hv';
    have step2 : termVal' (sndIdx f) e (^func k g v) =
        construction.func ![sndIdx f, e] k g v (termValVec' (sndIdx f) e k v) :=
      construction.result_func' hkg hv;
    rw [step1, step2, key];
    simp [construction];

end termValFree

end FFL.FirstOrder.Arithmetic.Bootstrapping
