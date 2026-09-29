module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax
import Mathlib.Tactic.Bound

/-!
# Internal evaluation of terms

`termVal e t` evaluates the coded `ℒₒᵣ`-term `t` under the coded assignment `e` of its bound
variables, reading free variables as `0`.

## References

- [HP98, 1.63, 1.64, 1.66, 1.67, remark after 2.58]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open Arithmetic (isFunc_LOR_iff qqZero_eq_qqFunc qqOne_eq_qqFunc qqAdd_eq_qqFunc qqMul_eq_qqFunc
  quote_zeroIndex_eq quote_oneIndex_eq quote_addIndex_eq quote_mulIndex_eq)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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

lemma termValVec_qVec {n m w e x : V} (hw : IsSemitermVec ℒₒᵣ n m w) :
    termValVec (x ∷ e) (n + 1) (qVec ℒₒᵣ w) = x ∷ termValVec e n w := by
  have hq : IsUTermVec ℒₒᵣ (n + 1) (qVec ℒₒᵣ w) := hw.qVec.isUTerm;
  apply nth_ext' (n + 1) (by simp [hq]) (by simp [len_termValVec hw.isUTerm]);
  intro i hi;
  rw [nth_termValVec hq hi];
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩;
  · simp [qVec];
  · have hj : j < n := by simpa using hi;
    have hnth : (qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] := by
      rw [qVec, hw.lh];
      simp [nth_termBShiftVec hw.isUTerm hj];
    rw [hnth, termVal_termBShift (hw.isUTerm.nth hj) x e];
    simp [nth_termValVec hw.isUTerm hj];

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

end FFL.FirstOrder.Arithmetic.Bootstrapping
