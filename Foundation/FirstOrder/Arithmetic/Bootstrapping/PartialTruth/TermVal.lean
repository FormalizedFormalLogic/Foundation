module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax
import Mathlib.Tactic.Bound

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

/-! ## Exponential bounds

`bound` proves `a ≤ Exp.exp (⋯ (Exp.exp c))` by splitting a sum one level of `Exp.exp` at a time
(`add_le_exp`) and lifting a leaf `a ≤ c` through the remaining levels (`le_exp_of_le`, an unsafe
rule so that the levels at which to split are searched for). -/

section expBound

variable {a b c : V}

@[gcongr, bound] lemma exp_le_exp (h : a ≤ b) : Exp.exp a ≤ Exp.exp b := exp_monotone_le.mpr h

lemma le_exp_of_le (h : a ≤ c) : a ≤ Exp.exp c := h.trans (lt_exp c).le

attribute [aesop unsafe 50% apply (rule_sets := [Bound])] le_exp_of_le

lemma two_mul_le_exp (a : V) : 2 * a ≤ Exp.exp a := by
  rcases zero_or_succ a with rfl | ⟨b, rfl⟩;
  · simp;
  · rw [exp_succ];
    gcongr;
    exact succ_le_iff_lt.mpr (lt_exp b);

@[bound] lemma add_le_exp (ha : a ≤ c) (hb : b ≤ c) : a + b ≤ Exp.exp c :=
  calc a + b ≤ 2 * c := by rw [two_mul]; gcongr
    _ ≤ Exp.exp c := two_mul_le_exp c

lemma exp_add_exp_le_of_lt (ha : a < c) (hb : b < c) : Exp.exp a + Exp.exp b ≤ Exp.exp c := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := (zero_or_succ c).resolve_left (by rintro rfl; simp at ha);
  rw [exp_succ, two_mul];
  gcongr <;> exact lt_succ_iff_le.mp ‹_›;

end expBound

/-! ## Codes of the function symbols -/

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

lemma qqZero_eq_qqFunc : (𝟎 : V) = ^func (0 : V) (0 : V) (0 : V) := by
  rw [Arithmetic.coe_zero_eq,
    show (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = 0 from quote_zeroIndex_eq];

lemma qqOne_eq_qqFunc : (𝟏 : V) = ^func (0 : V) (1 : V) (0 : V) := by
  rw [Arithmetic.coe_one_eq,
    show (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = 1 from quote_oneIndex_eq];

lemma qqAdd_eq_qqFunc (a b : V) : (a ^+ b : V) = ^func (2 : V) (0 : V) (?[a, b] : V) := by
  rw [Arithmetic.qqAdd, Arithmetic.coe_addIndex_eq];

lemma qqMul_eq_qqFunc (a b : V) : (a ^* b : V) = ^func (2 : V) (1 : V) (?[a, b] : V) := by
  rw [Arithmetic.qqMul, Arithmetic.coe_mulIndex_eq];

lemma nth_le_listMax_total (v i : V) : v.[i] ≤ listMax v := by
  rcases lt_or_ge i (len v) with h | h;
  · exact nth_le_listMax h;
  · simp [nth_lt_len h];

/-! ## Evaluation of terms -/

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

variable {e t u k f v : V}

@[simp] lemma len_termValVec (hv : IsUTermVec ℒₒᵣ k v) : len (termValVec e k v) = k :=
  construction.resultVec_lh ℒₒᵣ _ hv

@[simp] lemma nth_termValVec {i : V} (hv : IsUTermVec ℒₒᵣ k v) (hi : i < k) :
    (termValVec e k v).[i] = termVal e v.[i] := construction.nth_resultVec ℒₒᵣ _ hv hi

lemma termVal_func (hkf : (ℒₒᵣ).IsFunc k f) (hv : IsUTermVec ℒₒᵣ k v) :
    termVal e (^func k f v) = construction.func ![e] k f v (termValVec e k v) :=
  construction.result_func' hkf hv

lemma termVal_func_congr {e' v' : V} (hkf : (ℒₒᵣ).IsFunc k f) (hv : IsUTermVec ℒₒᵣ k v)
    (hv' : IsUTermVec ℒₒᵣ k v') (h : ∀ i < k, termVal e v.[i] = termVal e' v'.[i]) :
    termVal e (^func k f v) = termVal e' (^func k f v') := by
  have : termValVec e k v = termValVec e' k v' :=
    nth_ext' k (len_termValVec hv) (len_termValVec hv') fun i hi ↦ by simp [hv, hv', hi, h i hi];
  simp [termVal_func hkf hv, termVal_func hkf hv', this, construction];

@[simp] lemma termVal_zero (e : V) : termVal e (𝟎 : V) = 0 := by
  rw [qqZero_eq_qqFunc, termVal_func (isFunc_LOR_iff.mpr (by simp)) (by simp)];
  simp [construction];

@[simp] lemma termVal_one (e : V) : termVal e (𝟏 : V) = 1 := by
  rw [qqOne_eq_qqFunc, termVal_func (isFunc_LOR_iff.mpr (by simp)) (by simp)];
  simp [construction];

section
variable (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

@[simp] lemma termVal_add : termVal e (t ^+ u) = termVal e t + termVal e u := by
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  rw [qqAdd_eq_qqFunc, termVal_func (isFunc_LOR_iff.mpr (by simp)) hv];
  simp [construction, hv];

@[simp] lemma termVal_mul : termVal e (t ^* u) = termVal e t * termVal e u := by
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  rw [qqMul_eq_qqFunc, termVal_func (isFunc_LOR_iff.mpr (by simp)) hv];
  simp [construction, hv];

end

lemma termVal_not_uterm (h : ¬IsUTerm ℒₒᵣ t) : termVal e t = 0 :=
  construction.result_prop_not ℒₒᵣ ![e] h

lemma termVal_termSubst {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t) :
    termVal e (termSubst ℒₒᵣ w t) = termVal (termValVec e n w) t := by
  apply IsSemiterm.induction 𝚺 (by definability) ?_ ?_ ?_ t ht;
  · intro z hz;
    simp [hw.isUTerm, hz];
  · simp;
  · intro k f v hf hv ih;
    rw [termSubst_func hf hv.isUTerm];
    exact termVal_func_congr hf (hw.termSubstVec hv).isUTerm hv.isUTerm fun i hi ↦ by
      rw [nth_termSubstVec hv.isUTerm hi, ih i hi];

lemma termVal_termBShift (ht : IsUTerm ℒₒᵣ t) (x e : V) :
    termVal (x ∷ e) (termBShift ℒₒᵣ t) = termVal e t := by
  apply IsUTerm.induction 𝚺 (by definability) ?_ ?_ ?_ t ht;
  · simp;
  · simp;
  · intro k f v hf hv ih;
    rw [termBShift_func hf hv];
    exact termVal_func_congr hf hv.isSemitermVec.termBShiftVec.isUTerm hv fun i hi ↦ by
      rw [nth_termBShiftVec hv hi, ih i hi];

lemma termVal_termShift (ht : IsUTerm ℒₒᵣ t) (e : V) :
    termVal e (termShift ℒₒᵣ t) = termVal e t := by
  apply IsUTerm.induction 𝚺 (by definability) ?_ ?_ ?_ t ht;
  · simp;
  · simp;
  · intro k f v hf hv ih;
    rw [termShift_func hf hv];
    exact termVal_func_congr hf hv.termShiftVec hv fun i hi ↦ by
      rw [nth_termShiftVec hv hi, ih i hi];

lemma termVal_quote {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) (v : Fin k → V) :
    termVal (matrixToVec v) ⌜t⌝ = t.valb v := by
  induction t with
  | bvar x => simp [Semiterm.empty_quote_eq, Semiterm.valb]
  | fvar x => exact x.elim
  | @func k' f w ih =>
    match k', f, w, ih with
    | 0, .zero, w, _ =>
      simp [Semiterm.empty_quote_eq, Semiterm.valb, quote_zeroIndex_eq, ← qqZero_eq_qqFunc];
      rfl;
    | 0, .one, w, _ =>
      simp [Semiterm.empty_quote_eq, Semiterm.valb, quote_oneIndex_eq, ← qqOne_eq_qqFunc];
      rfl;
    | 2, .add, w, ih =>
      have heq : (⌜(FirstOrder.Semiterm.func .add w : ClosedSemiterm ℒₒᵣ k)⌝ : V) =
          ⌜w 0⌝ ^+ ⌜w 1⌝ := by
        simp [Semiterm.empty_quote_eq, Arithmetic.qqAdd, quote_addIndex_eq,
          Arithmetic.coe_addIndex_eq, Matrix.vecHead, Matrix.vecTail];
      rw [heq, termVal_add (by simp [Semiterm.empty_quote_eq]) (by simp [Semiterm.empty_quote_eq]),
        ih 0, ih 1];
      rfl;
    | 2, .mul, w, ih =>
      have heq : (⌜(FirstOrder.Semiterm.func .mul w : ClosedSemiterm ℒₒᵣ k)⌝ : V) =
          ⌜w 0⌝ ^* ⌜w 1⌝ := by
        simp [Semiterm.empty_quote_eq, Arithmetic.qqMul, quote_mulIndex_eq,
          Arithmetic.coe_mulIndex_eq, Matrix.vecHead, Matrix.vecTail];
      rw [heq, termVal_mul (by simp [Semiterm.empty_quote_eq]) (by simp [Semiterm.empty_quote_eq]),
        ih 0, ih 1];
      rfl;

theorem termVal_le (e t : V) : termVal e t ≤ Exp.exp (Exp.exp (listMax e + t)) := by
  by_cases ht : IsUTerm ℒₒᵣ t;
  case neg => simp [termVal_not_uterm ht];
  revert t;
  apply IsUTerm.induction 𝚷 (P := fun t ↦ termVal e t ≤ Exp.exp (Exp.exp (listMax e + t)))
    (by definability);
  · intro z;
    rw [termVal_bvar];
    exact (nth_le_listMax_total e z).trans (by bound);
  · simp;
  · intro k f v hkf hv ih;
    rcases isFunc_LOR_iff.mp hkf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩;
    · simp [termVal_func hkf hv, construction];
    · simp [termVal_func hkf hv, construction];
    · obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv;
      have iha : termVal e a ≤ Exp.exp (Exp.exp (listMax e + a)) := by simpa using ih 0 (by simp);
      have ihb : termVal e b ≤ Exp.exp (Exp.exp (listMax e + b)) := by simpa using ih 1 (by simp);
      rw [← qqAdd_eq_qqFunc, termVal_add ha hb];
      calc termVal e a + termVal e b
          ≤ Exp.exp (Exp.exp (listMax e + a)) + Exp.exp (Exp.exp (listMax e + b)) := by gcongr
        _ ≤ Exp.exp (Exp.exp (listMax e + a) + Exp.exp (listMax e + b)) :=
          exp_add_exp_le_of_lt (by simp) (by simp)
        _ ≤ Exp.exp (Exp.exp (listMax e + a ^+ b)) := by
          gcongr;
          exact exp_add_exp_le_of_lt (by simp) (by simp);
    · obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv;
      have iha : termVal e a ≤ Exp.exp (Exp.exp (listMax e + a)) := by simpa using ih 0 (by simp);
      have ihb : termVal e b ≤ Exp.exp (Exp.exp (listMax e + b)) := by simpa using ih 1 (by simp);
      rw [← qqMul_eq_qqFunc, termVal_mul ha hb];
      calc termVal e a * termVal e b
          ≤ Exp.exp (Exp.exp (listMax e + a)) * Exp.exp (Exp.exp (listMax e + b)) := by gcongr
        _ = Exp.exp (Exp.exp (listMax e + a) + Exp.exp (listMax e + b)) := (exp_add _ _).symm
        _ ≤ Exp.exp (Exp.exp (listMax e + a ^* b)) := by
          gcongr;
          exact exp_add_exp_le_of_lt (by simp) (by simp);

end termVal

/-! ## Evaluation with free variables -/

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

variable {f e t u k g v : V}

@[simp] lemma len_termValVec' (hv : IsUTermVec ℒₒᵣ k v) : len (termValVec' f e k v) = k :=
  construction.resultVec_lh ℒₒᵣ _ hv

@[simp] lemma nth_termValVec' {i : V} (hv : IsUTermVec ℒₒᵣ k v) (hi : i < k) :
    (termValVec' f e k v).[i] = termVal' f e v.[i] :=
  construction.nth_resultVec ℒₒᵣ _ hv hi

lemma termVal'_func (hkg : (ℒₒᵣ).IsFunc k g) (hv : IsUTermVec ℒₒᵣ k v) :
    termVal' f e (^func k g v) = construction.func ![f, e] k g v (termValVec' f e k v) :=
  construction.result_func' hkg hv

lemma termVal'_func_congr {f' e' v' : V} (hkg : (ℒₒᵣ).IsFunc k g) (hv : IsUTermVec ℒₒᵣ k v)
    (hv' : IsUTermVec ℒₒᵣ k v') (h : ∀ i < k, termVal' f e v.[i] = termVal' f' e' v'.[i]) :
    termVal' f e (^func k g v) = termVal' f' e' (^func k g v') := by
  have : termValVec' f e k v = termValVec' f' e' k v' :=
    nth_ext' k (len_termValVec' hv) (len_termValVec' hv') fun i hi ↦ by simp [hv, hv', hi, h i hi];
  simp [termVal'_func hkg hv, termVal'_func hkg hv', this, construction];

section
variable (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

@[simp] lemma termVal'_add : termVal' f e (t ^+ u) = termVal' f e t + termVal' f e u := by
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  rw [qqAdd_eq_qqFunc, termVal'_func (isFunc_LOR_iff.mpr (by simp)) hv];
  simp [construction, hv];

@[simp] lemma termVal'_mul : termVal' f e (t ^* u) = termVal' f e t * termVal' f e u := by
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  rw [qqMul_eq_qqFunc, termVal'_func (isFunc_LOR_iff.mpr (by simp)) hv];
  simp [construction, hv];

end

lemma termVal'_not_uterm (h : ¬IsUTerm ℒₒᵣ t) : termVal' f e t = 0 :=
  construction.result_prop_not ℒₒᵣ ![f, e] h

lemma termVal'_empty (e t : V) : termVal' 0 e t = termVal e t := by
  by_cases ht : IsUTerm ℒₒᵣ t;
  case neg => simp [termVal'_not_uterm ht, termVal_not_uterm ht];
  revert t;
  apply IsUTerm.induction 𝚺 (P := fun t ↦ termVal' 0 e t = termVal e t) (by definability);
  · simp;
  · simp;
  · intro k g v hkg hv ih;
    have : termValVec' 0 e k v = termValVec e k v :=
      nth_ext' k (len_termValVec' hv) (len_termValVec hv) fun i hi ↦ by simp [hv, hi, ih i hi];
    simp [termVal'_func hkg hv, termVal_func hkg hv, this, construction, TermVal.construction];

lemma termVal'_termSubst {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t) :
    termVal' f e (termSubst ℒₒᵣ w t) = termVal' f (termValVec' f e n w) t := by
  apply IsSemiterm.induction 𝚺 (by definability) ?_ ?_ ?_ t ht;
  · intro z hz;
    simp [hw.isUTerm, hz];
  · simp;
  · intro k g v hkg hv ih;
    rw [termSubst_func hkg hv.isUTerm];
    exact termVal'_func_congr hkg (hw.termSubstVec hv).isUTerm hv.isUTerm fun i hi ↦ by
      rw [nth_termSubstVec hv.isUTerm hi, ih i hi];

lemma termVal'_termShift (ht : IsUTerm ℒₒᵣ t) :
    termVal' f e (termShift ℒₒᵣ t) = termVal' (sndIdx f) e t := by
  apply IsUTerm.induction 𝚺 (by definability) ?_ ?_ ?_ t ht;
  · simp;
  · simp [nth_succ];
  · intro k g v hkg hv ih;
    rw [termShift_func hkg hv];
    exact termVal'_func_congr hkg hv.termShiftVec hv fun i hi ↦ by
      rw [nth_termShiftVec hv hi, ih i hi];

end termValFree

end FFL.FirstOrder.Arithmetic.Bootstrapping
