module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic

@[expose] public section
namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

section

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace TermSubst

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z w. !nthDef y w z”
  fvar := .mkSigma “y x w. !qqFvarDef y x”
  func := .mkSigma “y k f v v' w. !qqFuncDef y k f v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (param z)        := (param 1).[z]
  fvar (_     x)        := ^&x
  func (_     k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermSubst

section termSubst

open TermSubst

variable (L)

noncomputable def termSubst (w t : V) : V := construction.result L ![w] t

noncomputable def termSubstVec (k w v : V) : V := construction.resultVec L ![w] k v

noncomputable def termSubstGraph : 𝚺₁.Semisentence 3 := (blueprint.result L).rew <| Rew.subst ![#0, #2, #1]

noncomputable def termSubstVecGraph : 𝚺₁.Semisentence 4 := (blueprint.resultVec L).rew <| Rew.subst ![#0, #1, #3, #2]

variable {L}

variable {n m w : V}

@[simp] lemma termSubst_bvar (z) :
    termSubst L w ^#z = w.[z] := by simp [termSubst, construction]

@[simp] lemma termSubst_fvar (x) :
    termSubst L w ^&x = ^&x := by simp [termSubst, construction]

@[simp] lemma termSubst_func {k f v} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termSubst L w (^func k f v) = ^func k f (termSubstVec L k w v) := by
  simp [termSubst, construction, hkf, hv]; rfl

section

instance termSubst.defined : 𝚺₁-Function₂ termSubst (V := V) L via termSubstGraph L := .mk fun v ↦ by
  simpa [termSubstGraph, termSubst, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined.defined ![v 0, v 2, v 1]

instance termSubst.definable : 𝚺₁-Function₂ termSubst (V := V) L := termSubst.defined.to_definable

instance termSubst.definable' : Γ-[k + 1]-Function₂ termSubst (V := V) L := termSubst.definable.of_sigmaOne

instance termSubstVec.defined : 𝚺₁-Function₃ termSubstVec (V := V) L via termSubstVecGraph L := .mk fun v ↦ by
  simpa [termSubstVecGraph, termSubstVec, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.resultVec_defined.defined ![v 0, v 1, v 3, v 2]

instance termSubstVec.definable : 𝚺₁-Function₃ termSubstVec (V := V) L := termSubstVec.defined.to_definable

instance termSubstVec.definable' : Γ-[i + 1]-Function₃ termSubstVec (V := V) L := termSubstVec.definable.of_sigmaOne

end

@[simp] lemma len_termSubstVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termSubstVec L k w ts) = k := construction.resultVec_lh L _ hts

@[simp] lemma nth_termSubstVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termSubstVec L k w ts).[i] = termSubst L w ts.[i] :=
  construction.nth_resultVec L _ hts hi

@[simp] lemma termSubstVec_nil (w : V) : termSubstVec L 0 w 0 = 0 := construction.resultVec_nil L _

lemma termSubstVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termSubstVec L (k + 1) w (t ∷ ts) = termSubst L w t ∷ termSubstVec L k w ts :=
  construction.resultVec_cons L ![w] hts ht

@[simp] lemma termSubstVec_cons₁ {t : V} (ht : IsUTerm L t) :
    termSubstVec L 1 w ?[t] = ?[termSubst L w t] := by
  rw [show (1 : V) = 0 + 1  by simp, termSubstVec_cons] <;> simp [*]

@[simp] lemma termSubstVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termSubstVec L 2 w ?[t₁, t₂] = ?[termSubst L w t₁, termSubst L w t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termSubstVec_cons] <;> simp [*]

@[simp] lemma IsSemitermVec.termSubst {t} (hw : IsSemitermVec L n m w) (ht : IsSemiterm L n t) : IsSemiterm L m (termSubst L w t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simpa using hw.nth hz
  · intro x; simp
  · intro k f v hkf hv ih
    simp only [hkf, hv.isUTerm, termSubst_func, IsSemiterm.func, true_and]
    exact IsSemitermVec.iff.mpr
      ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact ih i hi⟩

@[simp] lemma IsUTermVec.termSubst {t} (hw : IsUTermVec L n w) (ht : IsSemiterm L n t) : IsUTerm L (termSubst L w t) :=
  IsSemitermVec.termSubst hw.isSemitermVec ht |>.isUTerm

@[simp] lemma IsSemitermVec.termSubstVec {k n m v} (hw : IsSemitermVec L n m w) (hv : IsSemitermVec L k n v) :
    IsSemitermVec L k m (termSubstVec L k w v) := IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact hw.termSubst (hv.nth hi)⟩

@[simp] lemma substs_nil {t : V} (ht : IsSemiterm L 0 t) : termSubst L 0 t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    simp only [hf, hv.isUTerm, termSubst_func, qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    simp [nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma termSubst_termSubst {l n w v t : V} (hv : IsSemitermVec L l n v) (ht : IsSemiterm L l t) :
    termSubst L w (termSubst L v t) = termSubst L (termSubstVec L l w v) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar z, termSubst_bvar z, nth_termSubstVec hv.isUTerm hz]
  · intro x; simp
  · intro k f ts hf hts ih
    rw [termSubst_func hf hts.isUTerm,
      termSubst_func hf (hv.termSubstVec hts).isUTerm,
      termSubst_func hf hts.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm]) (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi, nth_termSubstVec hts.isUTerm hi, ih i hi]

lemma termSubst_eq_self {n w t : V} (ht : IsSemiterm L n t) (H : ∀ i < n, w.[i] = ^#i) :
    termSubst L w t = t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, H]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, ih i hi]

end termSubst

namespace TermShift

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. !qqBvarDef y z”
  fvar := .mkSigma “y x. !qqFvarDef y (x + 1)”
  func := .mkSigma “y k f v v'. !qqFuncDef y k f v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z)        := ^#z
  fvar (_ x)        := ^&(x + 1)
  func (_ k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermShift

section termShift

open TermShift

variable (L)

noncomputable def termShift (t : V) : V := construction.result L ![] t

noncomputable def termShiftVec (k v : V) : V := construction.resultVec L ![] k v

noncomputable def termShiftGraph : 𝚺₁.Semisentence 2 := blueprint.result L

noncomputable def termShiftVecGraph : 𝚺₁.Semisentence 3 := blueprint.resultVec L

variable {L}

variable {n : V}

@[simp] lemma termShift_bvar (z : V) :
    termShift L ^#z = ^#z := by simp [termShift, construction]

@[simp] lemma termShift_fvar (x : V) :
    termShift L ^&x = ^&(x + 1) := by simp [termShift, construction]

@[simp] lemma termShift_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termShift L (^func k f v) = ^func k f (termShiftVec L k v) := by
  simp [termShift, construction, hkf, hv]; rfl

section

instance termShift.defined : 𝚺₁-Function₁ termShift (V := V) L via termShiftGraph L := .mk fun v ↦ by
  simpa [termShiftGraph, termShift] using construction.result_defined.defined v

instance termShift.definable : 𝚺₁-Function₁ termShift (V := V) L := termShift.defined.to_definable

instance termShift.definable' : Γ-[i + 1]-Function₁ termShift (V := V) L := termShift.definable.of_sigmaOne

instance termShiftVec.defined : 𝚺₁-Function₂ termShiftVec (V := V) L via termShiftVecGraph L := .mk fun v ↦ by
  simpa [termShiftVecGraph, termShiftVec] using construction.resultVec_defined.defined v

instance termShiftVec.definable : 𝚺₁-Function₂ termShiftVec (V := V) L := termShiftVec.defined.to_definable

instance termShiftVec.definable' : Γ-[i + 1]-Function₂ termShiftVec (V := V) L := termShiftVec.definable.of_sigmaOne

end

@[simp] lemma len_termShiftVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termShiftVec L k ts) = k := construction.resultVec_lh L _ hts

@[simp] lemma nth_termShiftVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termShiftVec L k ts).[i] = termShift L ts.[i] := construction.nth_resultVec L _ hts hi

@[simp] lemma termShiftVec_nil : termShiftVec (V := V) L 0 0 = 0 := construction.resultVec_nil L ![]

lemma termShiftVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termShiftVec L (k + 1) (t ∷ ts) = termShift L t ∷ termShiftVec L k ts :=
  construction.resultVec_cons L ![] hts ht

@[simp] lemma termShiftVec_cons₁ {t₁ : V} (ht₁ : IsUTerm L t₁) :
    termShiftVec L 1 (?[t₁] : V) = ?[termShift L t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termShiftVec_cons] <;> simp [*]

@[simp] lemma termShiftVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termShiftVec L 2 (?[t₁, t₂] : V) = ?[termShift L t₁, termShift L t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termShiftVec_cons] <;> simp [ht₁, ht₂]

@[simp] lemma IsUTerm.termShift {t} (ht : IsUTerm L t) : IsUTerm L (termShift L t : V) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termShift_func, func_iff, true_and]
    exact ⟨by simp [hv], by intro i hi; rw [nth_termShiftVec hv hi]; exact ih i hi⟩

@[simp] lemma IsSemiterm.termShift {t : V} (ht : IsSemiterm L n t) : IsSemiterm L n (termShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv.isUTerm, termShift_func, func, true_and]
    refine IsSemitermVec.iff.mpr ⟨?_, ?_⟩
    · simp [termShiftVec, hv.isUTerm]
    · intro i hi
      rw [nth_termShiftVec hv.isUTerm hi]
      exact ih i hi

@[simp] lemma IsUTermVec.termShiftVec {k v : V} (hv : IsUTermVec L k v) : IsUTermVec L k (termShiftVec L k v) :=
    ⟨by simp [hv], fun i hi ↦ by rw [nth_termShiftVec hv hi]; exact (hv.nth hi).termShift⟩

@[simp] lemma IsSemitermVec.termShiftVec {k n v : V} (hv : IsSemitermVec L k n v) : IsSemitermVec L k n (termShiftVec L k v) :=
  IsSemitermVec.iff.mpr
    ⟨by simp [hv.isUTerm], fun i hi ↦ by
      rw [nth_termShiftVec hv.isUTerm hi]; exact (hv.nth hi).termShift⟩

@[simp] lemma IsUTerm.termBVtermShift {t : V} (ht : IsUTerm L t) : termBV L (Bootstrapping.termShift L t) = termBV L t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · simp
  · simp
  · intro k f v hf hv ih
    rw [termShift_func hf hv,
      termBV_func hf hv.termShiftVec,
      termBV_func hf hv]
    congr 1
    apply nth_ext' k (by simp [*]) (by simp [*])
    intro i hi
    simp [*]

@[simp] lemma IsUTermVec.termBVVectermShiftVec {v : V} (hv : IsUTermVec L k v) :
    termBVVec L k (Bootstrapping.termShiftVec L k v) = termBVVec L k v := by
  apply nth_ext' k (by simp [*]) (by simp [*])
  intro i hi
  simp [*, IsUTerm.termBVtermShift (hv.nth hi)]

end termShift

namespace TermBShift

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. !qqBvarDef y (z + 1)”
  fvar := .mkSigma “y x. !qqFvarDef y x”
  func := .mkSigma “y k f v v'. !qqFuncDef y k f v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z)        := ^#(z + 1)
  fvar (_ x)        := ^&x
  func (_ k f _ v') := ^func k f v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermBShift

section termBShift

open TermBShift

variable (L)

noncomputable def termBShift (t : V) : V := construction.result L ![] t

noncomputable def termBShiftVec (k v : V) : V := construction.resultVec L ![] k v

noncomputable def termBShiftGraph : 𝚺₁.Semisentence 2 := blueprint.result L

noncomputable def termBShiftVecGraph : 𝚺₁.Semisentence 3 := blueprint.resultVec L

variable {L}

@[simp] lemma termBShift_bvar (z : V) :
    termBShift L ^#z = ^#(z + 1) := by simp [termBShift, construction]

@[simp] lemma termBShift_fvar (x : V) :
    termBShift L ^&x = ^&x := by simp [termBShift, construction]

@[simp] lemma termBShift_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termBShift L (^func k f v) = ^func k f (termBShiftVec L k v) := by
  simp [termBShift, construction, hkf, hv]; rfl

section

instance termBShift.defined : 𝚺₁-Function₁ termBShift (V := V) L via termBShiftGraph L := .mk fun v ↦ by
  simpa using construction.result_defined.defined v

instance termBShift.definable : 𝚺₁-Function₁ termBShift (V := V) L := termBShift.defined.to_definable

instance termBShift.definable' : Γ-[i + 1]-Function₁ termBShift (V := V) L := termBShift.definable.of_sigmaOne

instance termBShiftVec.defined : 𝚺₁-Function₂ termBShiftVec (V := V) L via termBShiftVecGraph L := .mk fun v ↦ by
  simpa using construction.resultVec_defined.defined v

instance termBShiftVec.definable : 𝚺₁-Function₂ termBShiftVec (V := V) L := termBShiftVec.defined.to_definable

instance termBShiftVec.definable' : Γ-[i + 1]-Function₂ termBShiftVec (V := V) L := termBShiftVec.definable.of_sigmaOne

end

@[simp] lemma len_termBShiftVec {k ts : V} (hts : IsUTermVec L k ts) :
    len (termBShiftVec L k ts) = k := construction.resultVec_lh L _ hts

@[simp] lemma nth_termBShiftVec {k ts i : V} (hts : IsUTermVec L k ts) (hi : i < k) :
    (termBShiftVec L k ts).[i] = termBShift L ts.[i] :=
  construction.nth_resultVec L _ hts hi

@[simp] lemma termBShiftVec_nil : termBShiftVec (V := V) L 0 0 = 0 :=
  construction.resultVec_nil L ![]

lemma termBShiftVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termBShiftVec L (k + 1) (t ∷ ts) = termBShift L t ∷ termBShiftVec L k ts :=
  construction.resultVec_cons L ![] hts ht

@[simp] lemma termBShiftVec_cons₁ {t₁ : V} (ht₁ : IsUTerm L t₁) :
    termBShiftVec L 1 (?[t₁] : V) = ?[termBShift L t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termBShiftVec_cons] <;> simp [*]

@[simp] lemma termBShiftVec_cons₂ {t₁ t₂ : V} (ht₁ : IsUTerm L t₁) (ht₂ : IsUTerm L t₂) :
    termBShiftVec L 2 (?[t₁, t₂] : V) = ?[termBShift L t₁, termBShift L t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termBShiftVec_cons] <;> simp [*]

@[simp] lemma IsSemiterm.termBShift {t : V} (ht : IsSemiterm L n t) : IsSemiterm L (n + 1) (termBShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv.isUTerm, termBShift_func, func, true_and]
    refine IsSemitermVec.iff.mpr ⟨?_, ?_⟩
    · simp [hv.isUTerm]
    · intro i hi
      rw [nth_termBShiftVec hv.isUTerm hi]
      exact ih i hi

@[simp] lemma IsSemitermVec.termBShiftVec {k n v : V} (hv : IsSemitermVec L k n v) : IsSemitermVec L k (n + 1) (termBShiftVec L k v) :=
  IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm], fun i hi ↦ by
    rw [nth_termBShiftVec hv.isUTerm hi]; exact (hv.nth hi).termBShift⟩

lemma termBShift_termShift {t : V} (ht : IsSemiterm L n t) : termBShift L (termShift L t) = termShift L (termBShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp
  · intro x; simp
  · intro k f v hkf hv ih
    rw [termShift_func hkf hv.isUTerm,
      termBShift_func hkf hv.termShiftVec.isUTerm,
      termBShift_func hkf hv.isUTerm,
      termShift_func hkf hv.termBShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termBShiftVec hv.termShiftVec.isUTerm]) (by rw [len_termShiftVec hv.termBShiftVec.isUTerm])
    intro i hi
    rw [nth_termBShiftVec hv.termShiftVec.isUTerm hi, nth_termShiftVec hv.isUTerm hi,
      nth_termShiftVec hv.termBShiftVec.isUTerm hi, nth_termBShiftVec hv.isUTerm hi, ih i hi]

end termBShift

/-
namespace TermFreeAt

def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z m. (z < m → !qqBvarDef y z) ∧ (¬z < m → !qqFvarDef y 0)”
  fvar := .mkSigma “y x m. !qqFvarDef y (x + 1)”
  func := .mkSigma “y k f v v' m. !qqFuncDef y k f v'”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar param z        := if z < param 0 then ^#z else ^&0
  fvar param x        := ^&(x + 1)
  func param k f _ v' := ^func k f v'
  bvar_defined := by
    intro v
    by_cases C : v 1 < v 2 <;> simp [blueprint, C]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]

end TermFreeAt

section termFreeAt

open TermFreeAt

variable (L)

noncomputable def termFreeAt (m t : V) : V := construction.result L ![m] t

noncomputable def termFreeAtVec (m k v : V) : V := construction.resultVec L ![m] k v

def termFreeAtGraph : 𝚺₁.Semisentence 3 := (blueprint.result L).rew <| Rew.subst ![#0, #2, #1]

def termFreeAtVecGraph : 𝚺₁.Semisentence 4 := (blueprint.resultVec L).rew <| Rew.subst ![#0, #1, #3, #2]

variable {L}

@[simp] lemma termFreeAt_bvar (m z : V) :
    termFreeAt L m ^#z = if z < m then ^#z else ^&0 := by simp [termFreeAt, construction]

@[simp] lemma termFreeAt_fvar (m x : V) :
    termFreeAt L m ^&x = ^&(x + 1) := by simp [termFreeAt, construction]

@[simp] lemma termFreeAt_func {m k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termFreeAt L m (^func k f v) = ^func k f (termFreeAtVec L m k v) := by
  simp [termFreeAt, construction, hkf, hv]; rfl

section

lemma termFreeAt.defined : 𝚺₁-Function₂[V] termFreeAt L via termFreeAtGraph L := by
  intro v
  simpa [termFreeAtGraph, termFreeAt, Matrix.constant_eq_singleton, Matrix.comp_vecCons']
    using construction.result_defined (L := L) ![v 0, v 2, v 1]

end

end termFreeAt
-/
variable (L)

noncomputable def qVec (w : V) : V := ^#0 ∷ termBShiftVec L (len w) w

noncomputable def qVecGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “w' w. ∃ k, !lenDef k w ∧ ∃ sw, !(termBShiftVecGraph L) sw k w ∧ ∃ t, !qqBvarDef t 0 ∧ !adjoinDef w' t sw”

variable {L}

section

instance qVec.defined : 𝚺₁-Function₁[V] qVec L via qVecGraph L := .mk fun v ↦ by simp [qVecGraph]; rfl

instance qVec.definable : 𝚺₁-Function₁[V] qVec L := qVec.defined.to_definable

instance qVec.definable' : Γ-[m + 1]-Function₁[V] qVec L := qVec.definable.of_sigmaOne

end

@[simp] lemma len_qVec {k w : V} (h : IsUTermVec L k w) : len (qVec L w) = k + 1 := by
  rcases h.lh; simp [qVec, h]

lemma IsSemitermVec.qVec {k n w : V} (h : IsSemitermVec L k n w) : IsSemitermVec L (k + 1) (n + 1) (qVec L w) := by
  rcases h.lh
  refine IsSemitermVec.iff.mpr ⟨?_, ?_⟩
  · simp [h.isUTerm, Bootstrapping.qVec]
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [Bootstrapping.qVec]
    · simpa [Bootstrapping.qVec, nth_termBShiftVec h.isUTerm (by simpa using hi)] using
        h.nth (by simpa using hi) |>.termBShift

lemma substs_cons_bShift {u t w : V} (ht : IsSemiterm L n t) :
    termSubst L (u ∷ w) (termBShift L t) = termSubst L w t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [termBShift_func hf hv.isUTerm,
      termSubst_func hf hv.termBShiftVec.isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termSubstVec hv.termBShiftVec.isUTerm])
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      ih i hi]

lemma termShift_termSubsts {n m w t : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termShift L (termSubst L w t) = termSubst L (termShiftVec L n w) (termShift L t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [nth_termShiftVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm,
      termShift_func hf (hw.termSubstVec hv).isUTerm,
      termShift_func hf hv.isUTerm,
      termSubst_func hf hv.termShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi, ih i hi]

lemma bShift_substs {n m w t : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termBShift L (termSubst L w t) = termSubst L (termBShiftVec L n w) t := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [nth_termBShiftVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [termSubst_func hf hv.isUTerm,
      termBShift_func hf (hw.termSubstVec hv).isUTerm,
      termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termBShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    simp [nth_termBShiftVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma substs_qVec_bShift {n t m w : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w) :
    termSubst L (qVec L w) (termBShift L t) = termBShift L (termSubst L w t) := by
  rcases hw.lh
  simp [qVec, substs_cons_bShift ht, bShift_substs ht hw]

lemma termSubstVec_qVec_qVec {l n m : V} (hv : IsSemitermVec L l n v) (hw : IsSemitermVec L n m w) :
    termSubstVec L (l + 1) (qVec L w) (qVec L v) = qVec L (termSubstVec L l w v) := by
  apply nth_ext' (len v + 1)
    (by rw [len_termSubstVec hv.qVec.isUTerm, hv.lh])
    (by rw [len_qVec (hw.termSubstVec hv).isUTerm, hv.lh])
  intro i hi
  unfold qVec
  rcases hv.lh; rcases hw.lh
  rw [(hw.termSubstVec hv).lh]
  rw [termSubstVec_cons (by simp) (by rcases hv.lh; exact hv.termBShiftVec.isUTerm)]
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · have hi : i < len v := by simpa using hi
    simp [nth_termSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      nth_termBShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      substs_cons_bShift (hv.nth hi),
      bShift_substs (hv.nth hi) hw]

lemma termShift_qVec {n m w : V} (hw : IsSemitermVec L n m w) :
    termShiftVec L (n + 1) (qVec L w) = qVec L (termShiftVec L n w) := by
  apply nth_ext' (n + 1)
    (by rw [len_termShiftVec hw.qVec.isUTerm])
    (by rw [len_qVec hw.termShiftVec.isUTerm])
  intro i hi
  rw [nth_termShiftVec hw.qVec.isUTerm hi]
  unfold qVec
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · rcases hw.lh
    rw [nth_adjoin_succ, nth_adjoin_succ,
      nth_termBShiftVec hw.isUTerm (by simpa using hi),
      nth_termBShiftVec (by simp [hw.isUTerm]) (by simpa [hw.isUTerm] using hi),
      nth_termShiftVec hw.isUTerm (by simpa using hi),
      termBShift_termShift (hw.nth (by simpa using hi))]

section fvfree

variable (L)

def IsTermFVFree (n t : V) : Prop := IsSemiterm L n t ∧ termShift L t = t

variable {L}

@[simp] lemma IsTermFVFree.bvar (x : V) : IsTermFVFree L n ^#x ↔ x < n := by
  simp [IsTermFVFree]

@[simp] lemma IsTermFVFree.fvar (x : V) : ¬IsTermFVFree L n ^&x := by
  simp [IsTermFVFree]

end fvfree

end

namespace Arithmetic

protected def zero : ℕ := qqFuncN 0 zeroIndex 0

protected def one : ℕ := qqFuncN 0 oneIndex 0

noncomputable def qqAdd (x y : V) : V := ^func 2 (addIndex : V) ?[x, y]

noncomputable def qqMul (x y : V) : V := ^func 2 (mulIndex : V) ?[x, y]

notation "𝟎" => Arithmetic.zero

notation "𝟏" => Arithmetic.one

infixl:80 " ^+ " => qqAdd

infixl:82 " ^* " => qqMul

section

def qqAddGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “t x y. ∃ v, !mkVec₂Def v x y ∧ !qqFuncDef t 2 ↑addIndex v”

def qqMulGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “t x y. ∃ v, !mkVec₂Def v x y ∧ !qqFuncDef t 2 ↑mulIndex v”

instance qqAdd_defined : 𝚺₁-Function₂ (qqAdd : V → V → V) via qqAddGraph := .mk fun v ↦ by
  simp [qqAddGraph, numeral_eq_natCast, qqAdd]

instance qqMul_defined : 𝚺₁-Function₂ (qqMul : V → V → V) via qqMulGraph := .mk fun v ↦ by
  simp [qqMulGraph, numeral_eq_natCast, qqMul]

instance : Γ-[m + 1]-Function₂ (qqAdd : V → V → V) := .of_sigmaOne qqAdd_defined.to_definable

instance : Γ-[m + 1]-Function₂ (qqMul : V → V → V) := .of_sigmaOne qqMul_defined.to_definable

end

@[simp] lemma lt_qqAdd_left (x y : V) : x < x ^+ y := by
  simpa using nth_lt_qqFunc_of_lt (i := 0) (k := 2) (f := (addIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqAdd_right (x y : V) : y < x ^+ y := by
  simpa using nth_lt_qqFunc_of_lt (i := 1) (k := 2) (f := (addIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqMul_left (x y : V) : x < x ^* y := by
  simpa using nth_lt_qqFunc_of_lt (i := 0) (k := 2) (f := (mulIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqMul_right (x y : V) : y < x ^* y := by
  simpa using nth_lt_qqFunc_of_lt (i := 1) (k := 2) (f := (mulIndex : V)) (v := ?[x, y]) (by simp)

set_option backward.isDefEq.respectTransparency false in
lemma qqFunc_absolute (k f v : ℕ) : ((^func k f v : ℕ) : V) = ^func (k : V) (f : V) (v : V) := by simp [qqFunc, nat_cast_pair]

@[simp] lemma zero_semiterm : IsSemiterm ℒₒᵣ n (𝟎 : V) := by
  simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]

@[simp] lemma one_semiterm : IsSemiterm ℒₒᵣ n (𝟏 : V) := by
  simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]

set_option backward.isDefEq.respectTransparency false in
lemma coe_zero_eq : (𝟎 : V) = (^func 0 ⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ 0) := by
  simp [Arithmetic.zero, qqFuncN_eq_qqFunc, qqFunc, nat_cast_pair]; rfl

set_option backward.isDefEq.respectTransparency false in
lemma coe_one_eq : (𝟏 : V) = (^func 0 ⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ 0) := by
  simp [Arithmetic.one, qqFuncN_eq_qqFunc, qqFunc, nat_cast_pair]; rfl

namespace Numeral

def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = ↑Arithmetic.one”
  succ := .mkSigma “y t n. !qqAddGraph y t ↑Arithmetic.one”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 𝟏
  succ := fun _ _ t ↦ t ^+ 𝟏
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [qqAdd, blueprint, numeral_eq_natCast]

noncomputable def numeralAux (x : V) : V := construction.result ![] x

@[simp] lemma numeralAux_zero : numeralAux (0 : V) = 𝟏 := by simp [numeralAux, construction]

@[simp] lemma numeralAux_succ (x : V) : numeralAux (x + 1) = numeralAux x ^+ 𝟏 := by simp [numeralAux, construction]

section

def numeralAuxGraph : 𝚺₁.Semisentence 2 := blueprint.resultDef

instance numeralAux.defined : 𝚺₁-Function₁ (numeralAux : V → V) via numeralAuxGraph := .mk
  fun v ↦ by simp [construction.result_defined_iff, numeralAuxGraph]; rfl

instance numeralAux.definable : 𝚺-[0 + 1]-Function₁ (numeralAux : V → V) := numeralAux.defined.to_definable

end

@[simp] lemma lt_numeralAux_self (n : V) : n < numeralAux n := by
    induction n using ISigma1.sigma1_succ_induction
    · definability
    case zero => simp [Arithmetic.one, qqFuncN_eq_qqFunc]
    case succ n ih =>
      refine lt_of_lt_of_le ((add_lt_add_iff_right 1).mpr ih) (by simp [succ_le_iff_lt])

@[simp] lemma numeralAux_semiterm (n x : V) : IsSemiterm ℒₒᵣ n (numeralAux x) := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ x ih => simp [qqAdd, ih]

end Numeral

section numeral

open Numeral

noncomputable def numeral (x : V) : V := if x = 0 then 𝟎 else numeralAux (x - 1)

def numeralGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “t x.
    (x = 0 → t = ↑Arithmetic.zero) ∧
    (x ≠ 0 → ∃ x', !subDef x' x 1 ∧ !numeralAuxGraph t x')”

@[simp] lemma numeral_zero : numeral (0 : V) = 𝟎 := by simp [numeral]

@[simp] lemma numeral_one : numeral (1 : V) = 𝟏 := by simp [numeral]

@[simp] lemma numeral_add_two : numeral (n + 1 + 1 : V) = numeral (n + 1) ^+ 𝟏 := by simp [numeral]

lemma numeral_succ_pos (pos : 0 < n) : numeral (n + 1 : V) = numeral n ^+ 𝟏 := by
  rcases zero_or_succ n with (rfl | ⟨n, rfl⟩)
  · simp at pos
  simp [numeral]

@[simp] lemma numeral_semiterm (n x : V) : IsSemiterm ℒₒᵣ n (numeral x) := by
  by_cases hx : x = 0 <;> simp [hx, numeral]

@[simp] lemma numeral_uterm (x : V) : IsUTerm ℒₒᵣ (numeral x) := (numeral_semiterm 0 x).isUTerm

@[simp] lemma le_numeral_self (n : V) : n ≤ numeral n := by
  rcases zero_or_succ n with (rfl | ⟨n, rfl⟩)
  · simp
  · simp [numeral, succ_le_iff_lt]

section

instance numeral_defined : 𝚺₁-Function₁ (numeral : V → V) via numeralGraph := .mk fun v ↦ by
  simp [numeralGraph, numeral_eq_natCast]
  by_cases hv1 : v 1 = 0 <;> simp [hv1, numeral]

instance numeral_definable : 𝚺₁-Function₁ (numeral : V → V) := numeral_defined.to_definable

instance numeral_definable' : Γ-[m + 1]-Function₁ (numeral : V → V) := .of_sigmaOne numeral_definable

end

@[simp] lemma numeral_substs {w : V} (_ : IsSemitermVec ℒₒᵣ n m w) (x : V) :
    termSubst ℒₒᵣ w (numeral x) = numeral x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]
    · simp only [numeral_add_two, qqAdd]
      rw [termSubst_func (L := ℒₒᵣ) (by simp) (by simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc])]
      simp [ih, Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]

@[simp] lemma numeral_shift (x : V) :
    termShift ℒₒᵣ (numeral x) = numeral x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]
    · simp only [numeral_add_two, qqAdd]
      rw [termShift_func (L := ℒₒᵣ) (by simp) (by simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc])]
      simp [ih, Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]

@[simp] lemma numeral_bShift (x : V) :
    termBShift ℒₒᵣ (numeral x) = numeral x := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]
    · simp [qqAdd, ih, Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]

end numeral

end Arithmetic

end LO.FirstOrder.Arithmetic.Bootstrapping
