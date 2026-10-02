module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax

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

open Arithmetic (zeroIndex oneIndex addIndex mulIndex zeroIndex_ne_oneIndex addIndex_ne_mulIndex
  quote_func_zero quote_func_one quote_func_add quote_func_mul qqAdd qqMul qqZero_eq_qqFunc
  qqOne_eq_qqFunc)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Evaluation of terms -/

namespace TermVal

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z w. !nthDef y w z”
  fvar := .mkSigma “y x w. y = 0”
  func := .mkSigma
    “y k f v v' w.
      (k = 0 ∧ f = ↑zeroIndex → y = 0) ∧
      (k = 0 ∧ f = ↑oneIndex → y = 1) ∧
      (k = 2 ∧ f = ↑addIndex → ∃ a, !nthDef a v' 0 ∧ ∃ b, !nthDef b v' 1 ∧ y = a + b) ∧
      (k = 2 ∧ f = ↑mulIndex → ∃ a, !nthDef a v' 0 ∧ ∃ b, !nthDef b v' 1 ∧ y = a * b) ∧
      (¬(k = 0 ∧ f = ↑zeroIndex) → ¬(k = 0 ∧ f = ↑oneIndex) → ¬(k = 2 ∧ f = ↑addIndex) →
        ¬(k = 2 ∧ f = ↑mulIndex) → y = 0)”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (param z)        := (param 0).[z]
  fvar (_     _)        := 0
  func (_     k f _ v') :=
    if k = 0 ∧ f = zeroIndex then 0
    else if k = 0 ∧ f = oneIndex then 1
    else if k = 2 ∧ f = addIndex then v'.[0] + v'.[1]
    else if k = 2 ∧ f = mulIndex then v'.[0] * v'.[1]
    else 0
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by
    simp only [blueprint];
    split_ifs <;> simp_all [numeral_eq_natCast, zeroIndex_ne_oneIndex.symm,
      addIndex_ne_mulIndex.symm];
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
  rw [qqZero_eq_qqFunc, termVal_func (by simp) (by simp)];
  simp [construction];

@[simp] lemma termVal_one (e : V) : termVal e (𝟏 : V) = 1 := by
  rw [qqOne_eq_qqFunc, termVal_func (by simp) (by simp)];
  simp [construction, zeroIndex_ne_oneIndex.symm];

section
variable (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

@[simp] lemma termVal_add : termVal e (t ^+ u) = termVal e t + termVal e u := by
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  rw [qqAdd, termVal_func (by simp) hv];
  simp [construction, hv];

@[simp] lemma termVal_mul : termVal e (t ^* u) = termVal e t * termVal e u := by
  have hv : IsUTermVec ℒₒᵣ 2 (?[t, u] : V) := IsUTermVec.mkSeq₂_iff.mpr ⟨ht, hu⟩;
  rw [qqMul, termVal_func (by simp) hv];
  simp [construction, hv, addIndex_ne_mulIndex.symm];

end

lemma termVal_termBShift (ht : IsUTerm ℒₒᵣ t) (x e : V) :
    termVal (x ∷ e) (termBShift ℒₒᵣ t) = termVal e t := by
  apply IsUTerm.induction 𝚺 (by definability) ?_ ?_ ?_ t ht;
  · simp;
  · simp;
  · intro k f v hf hv ih;
    rw [termBShift_func hf hv];
    exact termVal_func_congr hf hv.isSemitermVec.termBShiftVec.isUTerm hv fun i hi ↦ by
      rw [nth_termBShiftVec hv hi, ih i hi];

lemma termVal_quote {k : ℕ} (t : ClosedSemiterm ℒₒᵣ k) (v : Fin k → V) :
    termVal (matrixToVec v) ⌜t⌝ = t.valb v := by
  induction t with
  | bvar x => simp [Semiterm.empty_quote_eq, Semiterm.valb]
  | fvar x => exact x.elim
  | @func k' f w ih =>
    match k', f, w, ih with
    | 0, .zero, w, _ =>
      simp [Semiterm.empty_quote_eq, Semiterm.valb, quote_func_zero, ← qqZero_eq_qqFunc];
      rfl;
    | 0, .one, w, _ =>
      simp [Semiterm.empty_quote_eq, Semiterm.valb, quote_func_one, ← qqOne_eq_qqFunc];
      rfl;
    | 2, .add, w, ih =>
      have heq : (⌜(FirstOrder.Semiterm.func .add w : ClosedSemiterm ℒₒᵣ k)⌝ : V) =
          ⌜w 0⌝ ^+ ⌜w 1⌝ := by
        simp [Semiterm.empty_quote_eq, qqAdd, quote_func_add, Matrix.vecHead, Matrix.vecTail];
      rw [heq, termVal_add (by simp [Semiterm.empty_quote_eq]) (by simp [Semiterm.empty_quote_eq]),
        ih 0, ih 1];
      rfl;
    | 2, .mul, w, ih =>
      have heq : (⌜(FirstOrder.Semiterm.func .mul w : ClosedSemiterm ℒₒᵣ k)⌝ : V) =
          ⌜w 0⌝ ^* ⌜w 1⌝ := by
        simp [Semiterm.empty_quote_eq, qqMul, quote_func_mul, Matrix.vecHead, Matrix.vecTail];
      rw [heq, termVal_mul (by simp [Semiterm.empty_quote_eq]) (by simp [Semiterm.empty_quote_eq]),
        ih 0, ih 1];
      rfl;

end termVal

end FFL.FirstOrder.Arithmetic.Bootstrapping
