import Arithmetization.ISigmaOne.Metamath.Term.Basic

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace TermSubst

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 1 where
  bvar := .mkSigma “y z w | !nthDef y w z” (by simp)
  fvar := .mkSigma “y x w | !qqFvarDef y x” (by simp)
  func := .mkSigma “y k f v v' w | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (param z)        := (param 1).[z]
  fvar (_     x)        := ^&x
  func (_     k f _ v') := ^func k f v'
  bvar_defined := by intro v; simp [blueprint]; rfl
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermSubst

section termSubst

open TermSubst

variable (L)

def Language.termSubst (w t : V) : V := (construction L).result ![w] t

def Language.termSubstVec (k w v : V) : V := (construction L).resultVec ![w] k v

variable {L}

variable {n m w : V}

@[simp] lemma Language.termSubst_bvar (z) :
    L.termSubst w ^#z = w.[z] := by simp [Language.termSubst, construction]

@[simp] lemma Language.termSubst_fvar (x) :
    L.termSubst w ^&x = ^&x := by simp [Language.termSubst, construction]

@[simp] lemma Language.termSubst_func {k f v} (hkf : L.Func k f) (hv : L.IsUTermVec k v) :
    L.termSubst w (^func k f v) = ^func k f (L.termSubstVec k w v) := by
  simp [Language.termSubst, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termSubstDef (pL : LDef) : 𝚺₁.Semisentence 3 := (blueprint pL).result.rew <| Rew.substs ![#0, #2, #1]

def _root_.LO.FirstOrder.Arith.LDef.termSubstVecDef (pL : LDef) : 𝚺₁.Semisentence 4 := (blueprint pL).resultVec.rew <| Rew.substs ![#0, #1, #3, #2]

variable (L)

lemma Language.termSubst_defined : 𝚺₁-Function₂ L.termSubst via pL.termSubstDef := by
  intro v; simpa [LDef.termSubstDef, Language.termSubst] using (construction L).result_defined ![v 0, v 2, v 1]

instance Language.termSubst_definable : 𝚺₁-Function₂ L.termSubst := (termSubst_defined L).to_definable

instance Language.termSubst_definable' : Γ-[k + 1]-Function₂ L.termSubst := L.termSubst_definable.of_sigmaOne

lemma Language.termSubstVec_defined : 𝚺₁-Function₃ L.termSubstVec via pL.termSubstVecDef := by
  intro v; simpa [LDef.termSubstVecDef, Language.termSubstVec] using (construction L).resultVec_defined ![v 0, v 1, v 3, v 2]

instance Language.termSubstVec_definable : 𝚺₁-Function₃ L.termSubstVec := L.termSubstVec_defined.to_definable

instance Language.termSubstVec_definable' : Γ-[i + 1]-Function₃ L.termSubstVec := L.termSubstVec_definable.of_sigmaOne

end

@[simp] lemma len_termSubstVec {k ts : V} (hts : L.IsUTermVec k ts) :
    len (L.termSubstVec k w ts) = k := (construction L).resultVec_lh _ hts

@[simp] lemma nth_termSubstVec {k ts i : V} (hts : L.IsUTermVec k ts) (hi : i < k) :
    (L.termSubstVec k w ts).[i] = L.termSubst w ts.[i] :=
  (construction L).nth_resultVec _ hts hi

@[simp] lemma termSubstVec_nil (w : V) : L.termSubstVec 0 w 0 = 0 :=
  (construction L).resultVec_nil _

lemma termSubstVec_cons {k t ts : V} (ht : L.IsUTerm t) (hts : L.IsUTermVec k ts) :
    L.termSubstVec (k + 1) w (t ∷ ts) = L.termSubst w t ∷ L.termSubstVec k w ts :=
  (construction L).resultVec_cons ![w] hts ht

@[simp] lemma termSubstVec_cons₁ {t : V} (ht : L.IsUTerm t) :
    L.termSubstVec 1 w ?[t] = ?[L.termSubst w t] := by
  rw [show (1 : V) = 0 + 1  by simp, termSubstVec_cons] <;> simp [*]

@[simp] lemma termSubstVec_cons₂ {t₁ t₂ : V} (ht₁ : L.IsUTerm t₁) (ht₂ : L.IsUTerm t₂) :
    L.termSubstVec 2 w ?[t₁, t₂] = ?[L.termSubst w t₁, L.termSubst w t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termSubstVec_cons] <;> simp [*]

@[simp] lemma Language.IsSemitermVec.termSubst {t} (hw : L.IsSemitermVec n m w) (ht : L.IsSemiterm n t) : L.IsSemiterm m (L.termSubst w t) := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simpa using hw.nth hz
  · intro x; simp
  · intro k f v hkf hv ih
    simp only [hkf, hv.isUTerm, Language.termSubst_func, Language.IsSemiterm.func, true_and]
    exact Language.IsSemitermVec.iff.mpr
      ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact ih i hi⟩

@[simp] lemma Language.IsUTermVec.termSubst {t} (hw : L.IsUTermVec n w) (ht : L.IsSemiterm n t) : L.IsUTerm (L.termSubst w t) :=
  Language.IsSemitermVec.termSubst hw.isSemitermVec ht |>.isUTerm

@[simp] lemma Language.IsSemitermVec.termSubstVec {k n m v} (hw : L.IsSemitermVec n m w) (hv : L.IsSemitermVec k n v) :
    L.IsSemitermVec k m (L.termSubstVec k w v) := Language.IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm], fun i hi ↦ by rw [nth_termSubstVec hv.isUTerm hi]; exact hw.termSubst (hv.nth hi)⟩

@[simp] lemma substs_nil {t} (ht : L.IsSemiterm 0 t) : L.termSubst 0 t = t := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    simp only [hf, hv.isUTerm, Language.termSubst_func, qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    simp [nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma termSubst_termSubst {l n w v t : V} (hv : L.IsSemitermVec l n v) (ht : L.IsSemiterm l t) :
    L.termSubst w (L.termSubst v t) = L.termSubst (L.termSubstVec l w v) t := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [Language.termSubst_bvar z, Language.termSubst_bvar z, nth_termSubstVec hv.isUTerm hz]
  · intro x; simp [hv]
  · intro k f ts hf hts ih
    rw [Language.termSubst_func hf hts.isUTerm,
      Language.termSubst_func hf (hv.termSubstVec hts).isUTerm,
      Language.termSubst_func hf hts.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm]) (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi, nth_termSubstVec hts.isUTerm hi, ih i hi]

lemma termSubst_eq_self {n w t : V} (ht : L.IsSemiterm n t) (H : ∀ i < n, w.[i] = ^#i) :
    L.termSubst w t = t := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, H]
  · intro x; simp
  · intro k f v hf hv ih
    rw [Language.termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, ih i hi]

end termSubst

namespace TermShift

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 0 where
  bvar := .mkSigma “y z | !qqBvarDef y z” (by simp)
  fvar := .mkSigma “y x | !qqFvarDef y (x + 1)” (by simp)
  func := .mkSigma “y k f v v' | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (_ z)        := ^#z
  fvar (_ x)        := ^&(x + 1)
  func (_ k f _ v') := ^func k f v'
  bvar_defined := by intro v; simp [blueprint]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermShift

section termShift

open TermShift

variable (L)

def Language.termShift (t : V) : V := (construction L).result ![] t

def Language.termShiftVec (k v : V) : V := (construction L).resultVec ![] k v

variable {L}

variable {n : V}

@[simp] lemma Language.termShift_bvar (z) :
    L.termShift ^#z = ^#z := by simp [Language.termShift, construction]

@[simp] lemma Language.termShift_fvar (x) :
    L.termShift ^&x = ^&(x + 1) := by simp [Language.termShift, construction]

@[simp] lemma Language.termShift_func {k f v} (hkf : L.Func k f) (hv : L.IsUTermVec k v) :
    L.termShift (^func k f v) = ^func k f (L.termShiftVec k v) := by
  simp [Language.termShift, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termShiftDef (pL : LDef) : 𝚺₁.Semisentence 2 := (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termShiftVecDef (pL : LDef) : 𝚺₁.Semisentence 3 := (blueprint pL).resultVec

variable (L)

lemma Language.termShift_defined : 𝚺₁-Function₁ L.termShift via pL.termShiftDef := by
  intro v; simpa [LDef.termShiftDef, Language.termShift] using (construction L).result_defined v

instance Language.termShift_definable : 𝚺₁-Function₁ L.termShift := L.termShift_defined.to_definable

instance Language.termShift_definable' : Γ-[i + 1]-Function₁ L.termShift := L.termShift_definable.of_sigmaOne

lemma Language.termShiftVec_defined : 𝚺₁-Function₂ L.termShiftVec via pL.termShiftVecDef := by
  intro v; simpa [LDef.termShiftVecDef, Language.termShiftVec] using (construction L).resultVec_defined v

instance Language.termShiftVec_definable : 𝚺₁-Function₂ L.termShiftVec := L.termShiftVec_defined.to_definable

instance Language.termShiftVec_definable' : Γ-[i + 1]-Function₂ L.termShiftVec := L.termShiftVec_definable.of_sigmaOne

end

@[simp] lemma len_termShiftVec {k ts : V} (hts : L.IsUTermVec k ts) :
    len (L.termShiftVec k ts) = k := (construction L).resultVec_lh _ hts

@[simp] lemma nth_termShiftVec {k ts i : V} (hts : L.IsUTermVec k ts) (hi : i < k) :
    (L.termShiftVec k ts).[i] = L.termShift ts.[i] := (construction L).nth_resultVec _ hts hi

@[simp] lemma termShiftVec_nil : L.termShiftVec 0 0 = 0 := (construction L).resultVec_nil ![]

lemma termShiftVec_cons {k t ts : V} (ht : L.IsUTerm t) (hts : L.IsUTermVec k ts) :
    L.termShiftVec (k + 1) (t ∷ ts) = L.termShift t ∷ L.termShiftVec k ts :=
  (construction L).resultVec_cons ![] hts ht

@[simp] lemma termShiftVec_cons₁ {t₁ : V} (ht₁ : L.IsUTerm t₁) :
    L.termShiftVec 1 ?[t₁] = ?[L.termShift t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termShiftVec_cons] <;> simp [*]

@[simp] lemma termShiftVec_cons₂ {t₁ t₂ : V} (ht₁ : L.IsUTerm t₁) (ht₂ : L.IsUTerm t₂) :
    L.termShiftVec 2 ?[t₁, t₂] = ?[L.termShift t₁, L.termShift t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termShiftVec_cons] <;> simp [ht₁, ht₂]

@[simp] lemma Language.IsUTerm.termShift {t} (ht : L.IsUTerm t) : L.IsUTerm (L.termShift t) := by
  apply Language.IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termShift_func, func_iff, true_and]
    exact ⟨by simp [hv], by intro i hi; rw [nth_termShiftVec hv hi]; exact ih i hi⟩

@[simp] lemma Language.IsSemiterm.termShift {t} (ht : L.IsSemiterm n t) : L.IsSemiterm n (L.termShift t) := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv.isUTerm, termShift_func, func, true_and]
    refine Language.IsSemitermVec.iff.mpr ⟨?_, ?_⟩
    · simp [termShiftVec, hv.isUTerm]
    · intro i hi
      rw [nth_termShiftVec hv.isUTerm hi]
      exact ih i hi

@[simp] lemma Language.IsUTermVec.termShiftVec {k v} (hv : L.IsUTermVec k v) : L.IsUTermVec k (L.termShiftVec k v) :=
    ⟨by simp [termShiftVec, hv], fun i hi ↦ by rw [nth_termShiftVec hv hi]; exact (hv.nth hi).termShift⟩

@[simp] lemma Language.IsSemitermVec.termShiftVec {k n v} (hv : L.IsSemitermVec k n v) : L.IsSemitermVec k n (L.termShiftVec k v) :=
  Language.IsSemitermVec.iff.mpr
    ⟨by simp [termShiftVec, hv.isUTerm], fun i hi ↦ by
      rw [nth_termShiftVec hv.isUTerm hi]; exact (hv.nth hi).termShift⟩

@[simp] lemma Language.IsUTerm.termBVtermShift {t} (ht : L.IsUTerm t) : L.termBV (L.termShift t) = L.termBV t := by
  apply Language.IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
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

@[simp] lemma Language.IsUTermVec.termBVVectermShiftVec {v} (hv : L.IsUTermVec k v) :
    L.termBVVec k (L.termShiftVec k v) = L.termBVVec k v := by
  apply nth_ext' k (by simp [*]) (by simp [*])
  intro i hi
  simp [*, Language.IsUTerm.termBVtermShift (hv.nth hi)]

end termShift

namespace TermBShift

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 0 where
  bvar := .mkSigma “y z | !qqBvarDef y (z + 1)” (by simp)
  fvar := .mkSigma “y x | !qqFvarDef y x” (by simp)
  func := .mkSigma “y k f v v' | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (_ z)        := ^#(z + 1)
  fvar (_ x)        := ^&x
  func (_ k f _ v') := ^func k f v'
  bvar_defined := by intro v; simp [blueprint]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermBShift

section termBShift

open TermBShift

variable (L)

def Language.termBShift (t : V) : V := (construction L).result ![] t

def Language.termBShiftVec (k v : V) : V := (construction L).resultVec ![] k v

variable {L}

@[simp] lemma Language.termBShift_bvar (z) :
    L.termBShift ^#z = ^#(z + 1) := by simp [Language.termBShift, construction]

@[simp] lemma Language.termBShift_fvar (x) :
    L.termBShift ^&x = ^&x := by simp [Language.termBShift, construction]

@[simp] lemma Language.termBShift_func {k f v} (hkf : L.Func k f) (hv : L.IsUTermVec k v) :
    L.termBShift (^func k f v) = ^func k f (L.termBShiftVec k v) := by
  simp [Language.termBShift, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termBShiftDef (pL : LDef) : 𝚺₁.Semisentence 2 := (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termBShiftVecDef (pL : LDef) : 𝚺₁.Semisentence 3 := (blueprint pL).resultVec

variable (L)

lemma Language.termBShift_defined : 𝚺₁-Function₁ L.termBShift via pL.termBShiftDef := by
  intro v; simpa using (construction L).result_defined v

instance Language.termBShift_definable : 𝚺₁-Function₁ L.termBShift := L.termBShift_defined.to_definable

instance Language.termBShift_definable' : Γ-[i + 1]-Function₁ L.termBShift := L.termBShift_definable.of_sigmaOne

lemma Language.termBShiftVec_defined : 𝚺₁-Function₂ L.termBShiftVec via pL.termBShiftVecDef := by
  intro v; simpa using (construction L).resultVec_defined v

instance Language.termBShiftVec_definable : 𝚺₁-Function₂ L.termBShiftVec := L.termBShiftVec_defined.to_definable

instance Language.termBShiftVec_definable' : Γ-[i + 1]-Function₂ L.termBShiftVec := L.termBShiftVec_definable.of_sigmaOne

end

@[simp] lemma len_termBShiftVec {k ts : V} (hts : L.IsUTermVec k ts) :
    len (L.termBShiftVec k ts) = k := (construction L).resultVec_lh _ hts

@[simp] lemma nth_termBShiftVec {k ts i : V} (hts : L.IsUTermVec k ts) (hi : i < k) :
    (L.termBShiftVec k ts).[i] = L.termBShift ts.[i] :=
  (construction L).nth_resultVec _ hts hi

@[simp] lemma termBShiftVec_nil : L.termBShiftVec 0 0 = 0 :=
  (construction L).resultVec_nil ![]

lemma termBShiftVec_cons {k t ts : V} (ht : L.IsUTerm t) (hts : L.IsUTermVec k ts) :
    L.termBShiftVec (k + 1) (t ∷ ts) = L.termBShift t ∷ L.termBShiftVec k ts :=
  (construction L).resultVec_cons ![] hts ht

@[simp] lemma termBShiftVec_cons₁ {t₁ : V} (ht₁ : L.IsUTerm t₁) :
    L.termBShiftVec 1 ?[t₁] = ?[L.termBShift t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termBShiftVec_cons] <;> simp [*]

@[simp] lemma termBShiftVec_cons₂ {t₁ t₂ : V} (ht₁ : L.IsUTerm t₁) (ht₂ : L.IsUTerm t₂) :
    L.termBShiftVec 2 ?[t₁, t₂] = ?[L.termBShift t₁, L.termBShift t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termBShiftVec_cons] <;> simp [*]

@[simp] lemma Language.IsSemiterm.termBShift {t} (ht : L.IsSemiterm n t) : L.IsSemiterm (n + 1) (L.termBShift t) := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv.isUTerm, termBShift_func, func, true_and]
    refine Language.IsSemitermVec.iff.mpr ⟨?_, ?_⟩
    · simp [hv.isUTerm]
    · intro i hi
      rw [nth_termBShiftVec hv.isUTerm hi]
      exact ih i hi

@[simp] lemma Language.IsSemitermVec.termBShiftVec {k n v} (hv : L.IsSemitermVec k n v) : L.IsSemitermVec k (n + 1) (L.termBShiftVec k v) :=
  Language.IsSemitermVec.iff.mpr
  ⟨by simp [hv.isUTerm], fun i hi ↦ by
    rw [nth_termBShiftVec hv.isUTerm hi]; exact (hv.nth hi).termBShift⟩

lemma termBShift_termShift {t} (ht : L.IsSemiterm n t) : L.termBShift (L.termShift t) = L.termShift (L.termBShift t) := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih
    rw [L.termShift_func hkf hv.isUTerm,
      L.termBShift_func hkf hv.termShiftVec.isUTerm,
      L.termBShift_func hkf hv.isUTerm,
      L.termShift_func hkf hv.termBShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termBShiftVec hv.termShiftVec.isUTerm]) (by rw [len_termShiftVec hv.termBShiftVec.isUTerm])
    intro i hi
    rw [nth_termBShiftVec hv.termShiftVec.isUTerm hi, nth_termShiftVec hv.isUTerm hi,
      nth_termShiftVec hv.termBShiftVec.isUTerm hi, nth_termBShiftVec hv.isUTerm hi, ih i hi]

end termBShift

variable (L)

def Language.qVec (w : V) : V := ^#0 ∷ L.termBShiftVec (len w) w

variable {L}

@[simp] lemma len_qVec {k w : V} (h : L.IsUTermVec k w) : len (L.qVec w) = k + 1 := by
  rcases h.lh; simp [Language.qVec, h, h]

lemma Language.IsSemitermVec.qVec {k n w : V} (h : L.IsSemitermVec k n w) : L.IsSemitermVec (k + 1) (n + 1) (L.qVec w) := by
  rcases h.lh
  refine Language.IsSemitermVec.iff.mpr ⟨?_, ?_⟩
  · simp [h.isUTerm, Language.qVec]
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp [Language.qVec]
    · simpa [Language.qVec, nth_termBShiftVec h.isUTerm (by simpa using hi)] using
        h.nth (by simpa using hi) |>.termBShift

lemma substs_cons_bShift {u t w} (ht : L.IsSemiterm n t) :
    L.termSubst (u ∷ w) (L.termBShift t) = L.termSubst w t := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [Language.termBShift_func hf hv.isUTerm,
      Language.termSubst_func hf hv.termBShiftVec.isUTerm,
      Language.termSubst_func hf hv.isUTerm]
    simp [hf, hv.isUTerm]
    apply nth_ext' k
      (by rw [len_termSubstVec hv.termBShiftVec.isUTerm])
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    rw [nth_termSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      ih i hi]

lemma termShift_termSubsts {n m w t} (ht : L.IsSemiterm n t) (hw : L.IsSemitermVec n m w) :
    L.termShift (L.termSubst w t) = L.termSubst (L.termShiftVec n w) (L.termShift t) := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [nth_termShiftVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [L.termSubst_func hf hv.isUTerm,
      L.termShift_func hf (hw.termSubstVec hv).isUTerm,
      L.termShift_func hf hv.isUTerm,
      L.termSubst_func hf hv.termShiftVec.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi, ih i hi]

lemma bShift_substs {n m w t} (ht : L.IsSemiterm n t) (hw : L.IsSemitermVec n m w) :
    L.termBShift (L.termSubst w t) = L.termSubst (L.termBShiftVec n w) t := by
  apply Language.IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, nth_termBShiftVec hw.isUTerm hz]
  · intro x; simp
  · intro k f v hf hv ih
    rw [L.termSubst_func hf hv.isUTerm,
      L.termBShift_func hf (hw.termSubstVec hv).isUTerm,
      L.termSubst_func hf hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (by rw [len_termBShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.isUTerm])
    intro i hi
    simp [nth_termBShiftVec (hw.termSubstVec hv).isUTerm hi, nth_termSubstVec hv.isUTerm hi, ih i hi]

lemma substs_qVec_bShift {n t m w} (ht : L.IsSemiterm n t) (hw : L.IsSemitermVec n m w) :
    L.termSubst (L.qVec w) (L.termBShift t) = L.termBShift (L.termSubst w t) := by
  rcases hw.lh
  simp [Language.qVec]
  rw [substs_cons_bShift ht, bShift_substs ht hw]

lemma termSubstVec_qVec_qVec {l n m : V} (hv : L.IsSemitermVec l n v) (hw : L.IsSemitermVec n m w) :
    L.termSubstVec (l + 1) (L.qVec w) (L.qVec v) = L.qVec (L.termSubstVec l w v) := by
  apply nth_ext' (len v + 1)
    (by rw [len_termSubstVec hv.qVec.isUTerm, hv.lh])
    (by rw [len_qVec (hw.termSubstVec hv).isUTerm, hv.lh])
  intro i hi
  unfold Language.qVec
  rcases hv.lh; rcases hw.lh
  rw [(hw.termSubstVec hv).lh]
  rw [termSubstVec_cons (by simp) (by rcases hv.lh; exact hv.termBShiftVec.isUTerm)]
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · simp
    have hi : i < len v := by simpa using hi
    rw [nth_termSubstVec hv.termBShiftVec.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi,
      nth_termBShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      substs_cons_bShift (hv.nth hi),
      bShift_substs (hv.nth hi) hw]

lemma termShift_qVec {n m w : V} (hw : L.IsSemitermVec n m w) :
    L.termShiftVec (n + 1) (L.qVec w) = L.qVec (L.termShiftVec n w) := by
  apply nth_ext' (n + 1)
    (by rw [len_termShiftVec hw.qVec.isUTerm])
    (by rw [len_qVec hw.termShiftVec.isUTerm])
  intro i hi
  rw [nth_termShiftVec hw.qVec.isUTerm hi]
  unfold Language.qVec
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · rcases hw.lh
    rw [nth_cons_succ, nth_cons_succ,
      nth_termBShiftVec hw.isUTerm (by simpa using hi),
      nth_termBShiftVec (by simpa [hw.isUTerm] using hw.termShiftVec.isUTerm) (by simpa [hw.isUTerm] using hi),
      nth_termShiftVec hw.isUTerm (by simpa using hi),
      termBShift_termShift (hw.nth (by simpa using hi))]

section fvfree

variable (L)

def Language.IsTermFVFree (n t : V) : Prop := L.IsSemiterm n t ∧ L.termShift t = t

variable {L}

@[simp] lemma Language.IsTermFVFree.bvar (x : V) : L.IsTermFVFree n ^#x ↔ x < n := by
  simp [Language.IsTermFVFree]

@[simp] lemma Language.IsTermFVFree.fvar (x : V) : ¬L.IsTermFVFree n ^&x := by
  simp [Language.IsTermFVFree]

end fvfree

end

namespace Formalized

protected def zero : ℕ := ^func 0 zeroIndex 0

protected def one : ℕ := ^func 0 oneIndex 0

def qqAdd (x y : V) := ^func 2 (addIndex : V) ?[x, y]

def qqMul (x y : V) := ^func 2 (mulIndex : V) ?[x, y]

notation "𝟎" => Formalized.zero

notation "𝟏" => Formalized.one

infixl:80 " ^+ " => qqAdd

infixl:82 " ^* " => qqMul

section

def _root_.LO.FirstOrder.Arith.qqAddDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “t x y | ∃ v, !mkVec₂Def v x y ∧ !qqFuncDef t 2 ↑addIndex v” (by simp)

def _root_.LO.FirstOrder.Arith.qqMulDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “t x y | ∃ v, !mkVec₂Def v x y ∧ !qqFuncDef t 2 ↑mulIndex v” (by simp)

lemma qqAdd_defined : 𝚺₁-Function₂ (qqAdd : V → V → V) via qqAddDef := by
  intro v; simp [qqAddDef, numeral_eq_natCast, qqAdd]

lemma qqMul_defined : 𝚺₁-Function₂ (qqMul : V → V → V) via qqMulDef := by
  intro v; simp [qqMulDef, numeral_eq_natCast, qqMul]

instance : Γ-[m + 1]-Function₂ (qqAdd : V → V → V) := .of_sigmaOne qqAdd_defined.to_definable

instance : Γ-[m + 1]-Function₂ (qqMul : V → V → V) := .of_sigmaOne qqMul_defined.to_definable

end

lemma qqFunc_absolute (k f v : ℕ) : ((^func k f v : ℕ) : V) = ^func (k : V) (f : V) (v : V) := by simp [qqFunc, nat_cast_pair]

@[simp] lemma zero_semiterm : ⌜ℒₒᵣ⌝.IsSemiterm n (𝟎 : V) := by
  simp [Formalized.zero, qqFunc_absolute]

@[simp] lemma one_semiterm : ⌜ℒₒᵣ⌝.IsSemiterm n (𝟏 : V) := by
  simp [Formalized.one, qqFunc_absolute]

namespace Numeral

def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y | y = ↑Formalized.one” (by simp)
  succ := .mkSigma “y t n | ∃ p, !mkVec₂Def p t ↑Formalized.one ∧ !qqFuncDef y 2 ↑addIndex p” (by simp)

def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 𝟏
  succ := fun _ _ t ↦ t ^+ 𝟏
  zero_defined := by intro v; simp [blueprint, numeral_eq_natCast]
  succ_defined := by intro v; simp [qqAdd, blueprint, numeral_eq_natCast]

def numeralAux (x : V) : V := construction.result ![] x

@[simp] lemma numeralAux_zero : numeralAux (0 : V) = 𝟏 := by simp [numeralAux, construction]

@[simp] lemma numeralAux_succ (x : V) : numeralAux (x + 1) = numeralAux x ^+ 𝟏 := by simp [numeralAux, construction]

section

def numeralAuxDef : 𝚺₁.Semisentence 2 := blueprint.resultDef

lemma numeralAux_defined : 𝚺₁-Function₁ (numeralAux : V → V) via numeralAuxDef :=
  fun v ↦ by simp [construction.result_defined_iff, numeralAuxDef]; rfl

@[simp] lemma eval_numeralAuxDef (v) :
    Semiformula.Evalbm V v numeralAuxDef.val ↔ v 0 = numeralAux (v 1) := numeralAux_defined.df.iff v

instance seqExp_definable : 𝚺-[0 + 1]-Function₁ (numeralAux : V → V) := numeralAux_defined.to_definable

end

@[simp] lemma numeralAux_semiterm (n x : V) : ⌜ℒₒᵣ⌝.IsSemiterm n (numeralAux x) := by
  induction x using induction_sigma1
  · definability
  case zero => simp
  case succ x ih => simp [qqAdd, ih]

end Numeral

section numeral

open Numeral

def numeral (x : V) : V := if x = 0 then 𝟎 else numeralAux (x - 1)

@[simp] lemma numeral_zero : numeral (0 : V) = 𝟎 := by simp [numeral]

@[simp] lemma numeral_one : numeral (1 : V) = 𝟏 := by simp [numeral]

@[simp] lemma numeral_add_two : numeral (n + 1 + 1 : V) = numeral (n + 1) ^+ 𝟏 := by simp [numeral, ←add_assoc]

lemma numeral_succ_pos (pos : 0 < n) : numeral (n + 1 : V) = numeral n ^+ 𝟏 := by
  rcases zero_or_succ n with (rfl | ⟨n, rfl⟩)
  · simp at pos
  simp [numeral, ←one_add_one_eq_two, ←add_assoc]

@[simp] lemma numeral_semiterm (n x : V) : ⌜ℒₒᵣ⌝.IsSemiterm n (numeral x) := by
  by_cases hx : x = 0 <;> simp [hx, numeral]

@[simp] lemma numeral_uterm (x : V) : ⌜ℒₒᵣ⌝.IsUTerm (numeral x) := (numeral_semiterm 0 x).isUTerm

section

def _root_.LO.FirstOrder.Arith.numeralDef : 𝚺₁.Semisentence 2 := .mkSigma
  “t x |
    (x = 0 → t = ↑Formalized.zero) ∧
    (x ≠ 0 → ∃ x', !subDef x' x 1 ∧ !numeralAuxDef t x')”
  (by simp)

lemma numeral_defined : 𝚺₁-Function₁ (numeral : V → V) via numeralDef := fun v ↦ by
  simp [numeralDef, numeral_eq_natCast]
  by_cases hv1 : v 1 = 0 <;> simp [hv1, numeral]

@[simp] lemma eval_numeralDef (v) :
    Semiformula.Evalbm V v numeralDef.val ↔ v 0 = numeral (v 1) := numeral_defined.df.iff v

instance numeral_definable : 𝚺₁-Function₁ (numeral : V → V) := numeral_defined.to_definable

instance numeral_definable' : Γ-[m + 1]-Function₁ (numeral : V → V) := .of_sigmaOne numeral_definable

end

@[simp] lemma numeral_substs {w : V} (hw : ⌜ℒₒᵣ⌝.IsSemitermVec n m w) (x : V) :
    ⌜ℒₒᵣ⌝.termSubst w (numeral x) = numeral x := by
  induction x using induction_sigma1
  · definability
  case zero => simp [hw, Formalized.zero, qqFunc_absolute]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [hw, Formalized.one, qqFunc_absolute]
    · simp only [numeral_add_two, qqAdd, LOR_func_addIndex]
      rw [Language.termSubst_func (by simp) (by simp [Formalized.one, qqFunc_absolute])]
      simp [ih, Formalized.one, qqFunc_absolute]

@[simp] lemma numeral_shift (x : V) :
    ⌜ℒₒᵣ⌝.termShift (numeral x) = numeral x := by
  induction x using induction_sigma1
  · definability
  case zero => simp [Formalized.zero, qqFunc_absolute]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Formalized.one, qqFunc_absolute]
    · simp only [numeral_add_two, qqAdd, LOR_func_addIndex]
      rw [Language.termShift_func (by simp) (by simp [Formalized.one, qqFunc_absolute])]
      simp [ih, Formalized.one, qqFunc_absolute]

@[simp] lemma numeral_bShift (x : V) :
    ⌜ℒₒᵣ⌝.termBShift (numeral x) = numeral x := by
  induction x using induction_sigma1
  · definability
  case zero => simp [Formalized.zero, qqFunc_absolute]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Formalized.one, qqFunc_absolute]
    · simp [qqAdd, ih, Formalized.one, qqFunc_absolute]

end numeral

end Formalized

end LO.Arith

end
