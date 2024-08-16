import Arithmetization.ISigmaOne.Metamath.Term.Basic

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

section

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace TermSubst

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 2 where
  bvar := .mkSigma “y n z m w | !nthDef y w z” (by simp)
  fvar := .mkSigma “y n x m w | !qqFvarDef y x” (by simp)
  func := .mkSigma “y n k f v v' m w | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (param _ z)        := (param 1).[z]
  fvar (_     _ x)        := ^&x
  func (_     _ k f _ v') := ^func k f v'
  bvar_defined := by intro v; simp [blueprint]; rfl
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermSubst

section termSubst

open TermSubst

variable (L)

def Language.termSubst (n m w t : V) : V := (construction L).result ![m, w] n t

def Language.termSubstVec (k n m w v : V) : V := (construction L).resultVec ![m, w] k n v

variable {L}

variable {n m w : V}

@[simp] lemma termSubst_bvar {z} (hz : z < n) :
    L.termSubst n m w ^#z = w.[z] := by simp [Language.termSubst, hz, construction]

@[simp] lemma termSubst_fvar (x) :
    L.termSubst n m w ^&x = ^&x := by simp [Language.termSubst, construction]

@[simp] lemma termSubst_func {k f v} (hkf : L.Func k f) (hv : L.SemitermVec k n v) :
    L.termSubst n m w (^func k f v) = ^func k f (L.termSubstVec k n m w v) := by
  simp [Language.termSubst, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termSubstDef (pL : LDef) : 𝚺₁.Semisentence 5 := (blueprint pL).result.rew <| Rew.substs ![#0, #1, #4, #2, #3]

def _root_.LO.FirstOrder.Arith.LDef.termSubstVecDef (pL : LDef) : 𝚺₁.Semisentence 6 := (blueprint pL).resultVec.rew <| Rew.substs ![#0, #1, #2, #5, #3, #4]

variable (L)

lemma termSubst_defined : 𝚺₁.DefinedFunction (fun v ↦ L.termSubst (v 0) (v 1) (v 2) (v 3)) pL.termSubstDef := by
  intro v; simpa [LDef.termSubstDef, Language.termSubst] using (construction L).result_defined ![v 0, v 1, v 4, v 2, v 3]

@[simp] lemma eval_termSubstDef (v : Fin 5 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termSubstDef ↔ v 0 = L.termSubst (v 1) (v 2) (v 3) (v 4) := (termSubst_defined L).df.iff v

instance termSubst_definable : 𝚺₁.BoldfaceFunction (fun v : Fin 4 → V ↦ L.termSubst (v 0) (v 1) (v 2) (v 3)) :=
  (termSubst_defined L).to_definable

instance termSubst_definable₂ (n m : V) : 𝚺₁-Function₂ (L.termSubst n m) := by
  simpa using HierarchySymbol.BoldfaceFunction.retractiont (n := 2) (termSubst_definable L) ![&n, &m, #0, #1]

@[simp, definability] instance termSubst_definable₂' (Γ k) (n m : V) : Γ-[k + 1]-Function₂ (L.termSubst n m) :=
  .of_sigmaOne (termSubst_definable₂ L n m) _ _

lemma termSubstVec_defined : 𝚺₁.DefinedFunction (fun v ↦ L.termSubstVec (v 0) (v 1) (v 2) (v 3) (v 4)) pL.termSubstVecDef := by
  intro v; simpa [LDef.termSubstVecDef, Language.termSubstVec] using (construction L).resultVec_defined ![v 0, v 1, v 2, v 5, v 3, v 4]

@[simp] lemma eval_termSubstVecDef (v : Fin 6 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termSubstVecDef ↔ v 0 = L.termSubstVec (v 1) (v 2) (v 3) (v 4) (v 5) := (termSubstVec_defined L).df.iff v

instance termSubstVec_definable : 𝚺₁.BoldfaceFunction (fun v : Fin 5 → V ↦ L.termSubstVec (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (termSubstVec_defined L).to_definable

instance termSubstVec_definable₂ (k n m : V) : 𝚺₁-Function₂ (L.termSubstVec k n m) := by
  simpa using HierarchySymbol.BoldfaceFunction.retractiont (n := 2) (termSubstVec_definable L) ![&k, &n, &m, #0, #1]

@[simp, definability] instance termSubstVec_definable₂' (Γ i) (k n m : V) : Γ-[i + 1]-Function₂ (L.termSubstVec k n m) :=
  .of_sigmaOne (termSubstVec_definable₂ L k n m) _ _

end

@[simp] lemma len_termSubstVec {k n ts : V} (hts : L.SemitermVec k n ts) :
    len (L.termSubstVec k n m w ts) = k := (construction L).resultVec_lh _ hts

@[simp] lemma nth_termSubstVec {k n ts i : V} (hts : L.SemitermVec k n ts) (hi : i < k) :
    (L.termSubstVec k n m w ts).[i] = L.termSubst n m w ts.[i] :=
  (construction L).nth_resultVec _ hts hi

@[simp] lemma termSubstVec_nil (n : V) : L.termSubstVec 0 n m w 0 = 0 :=
  (construction L).resultVec_nil _ _

lemma termSubstVec_cons {k n t ts : V} (ht : L.Semiterm n t) (hts : L.SemitermVec k n ts) :
    L.termSubstVec (k + 1) n m w (t ∷ ts) = L.termSubst n m w t ∷ L.termSubstVec k n m w ts :=
  (construction L).resultVec_cons ![m, w] hts ht

@[simp] lemma termSubstVec_cons₁ {n t : V} (ht : L.Semiterm n t) :
    L.termSubstVec 1 n m w ?[t] = ?[L.termSubst n m w t] := by
  rw [show (1 : V) = 0 + 1  by simp, termSubstVec_cons] <;> simp [*]

@[simp] lemma termSubstVec_cons₂ {n t₁ t₂ : V} (ht₁ : L.Semiterm n t₁) (ht₂ : L.Semiterm n t₂) :
    L.termSubstVec 2 n m w ?[t₁, t₂] = ?[L.termSubst n m w t₁, L.termSubst n m w t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termSubstVec_cons] <;> simp [*]

@[simp] lemma termSubst_rng_semiterm {t} (hw : L.SemitermVec n m w) (ht : L.Semiterm n t) : L.Semiterm m (L.termSubst n m w t) := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, hw.prop hz]
  · intro x; simp
  · intro k f v hkf hv ih
    simp only [hkf, hv, termSubst_func, Language.Semiterm.func_iff, true_and]
    exact ⟨by simp [Language.termSubstVec, hv], fun i hi ↦ by
      rw [nth_termSubstVec hv hi]
      exact ih i hi⟩

@[simp] lemma Language.SemitermVec.termSubstVec {k n m v} (hw : L.SemitermVec n m w) (hv : L.SemitermVec k n v) :
    L.SemitermVec k m (L.termSubstVec k n m w v) :=
  ⟨by simp [Language.termSubstVec, hv], fun i hi ↦ by
    rw [nth_termSubstVec hv hi]
    exact termSubst_rng_semiterm hw (hv.prop hi)⟩

@[simp] lemma substs_nil {t} (ht : L.Semiterm 0 t) : L.termSubst 0 0 0 t = t := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    simp only [hf, hv, termSubst_func, qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hv]) (by simp [hv.1])
    intro i hi
    simp [nth_termSubstVec hv hi, ih i hi]

lemma termSubst_termSubst {l n m w v t : V} (hv : L.SemitermVec l n v) (ht : L.Semiterm l t) :
    L.termSubst n m w (L.termSubst l n v t) = L.termSubst l m (L.termSubstVec l n m w v) t := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, hv]
  · intro x; simp [hv]
  · intro k f ts hf hts ih
    simp only [termSubst_func, Language.SemitermVec.termSubstVec, qqFunc_inj, true_and, hf, hts, hv]
    apply nth_ext' k (by simp [hv, hts]) (by simp [hts])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts) hi, nth_termSubstVec hts hi, nth_termSubstVec hts hi, ih i hi]

lemma termSubst_eq_self {n m w t : V} (ht : L.Semiterm n t) (H : ∀ i < n, w.[i] = ^#i) :
    L.termSubst n m w t = t := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, H]
  · intro x; simp
  · intro k f v hf hv ih
    simp only [termSubst_func, qqFunc_inj, true_and, hf, hv]
    apply nth_ext' k (by simp [*]) (by simp [hv.1])
    intro i hi
    rw [nth_termSubstVec hv hi, ih i hi]

end termSubst

namespace TermShift

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 0 where
  bvar := .mkSigma “y n z m w | !qqBvarDef y z” (by simp)
  fvar := .mkSigma “y n x m w | !qqFvarDef y (x + 1)” (by simp)
  func := .mkSigma “y n k f v v' m w | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (_ _ z)        := ^#z
  fvar (_ _ x)        := ^&(x + 1)
  func (_ _ k f _ v') := ^func k f v'
  bvar_defined := by intro v; simp [blueprint]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermShift

section termShift

open TermShift

variable (L)

def Language.termShift (n t : V) : V := (construction L).result ![] n t

def Language.termShiftVec (k n v : V) : V := (construction L).resultVec ![] k n v

variable {L}

variable {n : V}

@[simp] lemma termShift_bvar {z} (hz : z < n) :
    L.termShift n ^#z = ^#z := by simp [Language.termShift, hz, construction]

@[simp] lemma termShift_fvar (x) :
    L.termShift n ^&x = ^&(x + 1) := by simp [Language.termShift, construction]

@[simp] lemma termShift_func {k f v} (hkf : L.Func k f) (hv : L.SemitermVec k n v) :
    L.termShift n (^func k f v) = ^func k f (L.termShiftVec k n v) := by
  simp [Language.termShift, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termShiftDef (pL : LDef) : 𝚺₁.Semisentence 3 :=
  (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termShiftVecDef (pL : LDef) : 𝚺₁.Semisentence 4 := (blueprint pL).resultVec

variable (L)

lemma termShift_defined : 𝚺₁-Function₂ L.termShift via pL.termShiftDef := by
  intro v; simpa [LDef.termShiftDef, Language.termShift] using (construction L).result_defined v

@[simp] lemma eval_termShiftDef (v : Fin 3 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termShiftDef ↔ v 0 = L.termShift (v 1) (v 2) := (termShift_defined L).df.iff v

instance termShift_definable : 𝚺₁-Function₂ L.termShift :=
  (termShift_defined L).to_definable

@[definability, simp] instance termShift_definable' (Γ i) : Γ-[i + 1]-Function₂ L.termShift := .of_sigmaOne (termShift_definable L) _ _

lemma termShiftVec_defined : 𝚺₁-Function₃ L.termShiftVec via pL.termShiftVecDef := by
  intro v; simpa [LDef.termShiftVecDef, Language.termShiftVec] using (construction L).resultVec_defined v

@[simp] lemma eval_termShiftVecDef (v : Fin 4 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termShiftVecDef ↔ v 0 = L.termShiftVec (v 1) (v 2) (v 3) := (termShiftVec_defined L).df.iff v

instance termShiftVec_definable : 𝚺₁-Function₃ L.termShiftVec :=
  (termShiftVec_defined L).to_definable

@[simp, definability] instance termShiftVec_definable' (Γ i) : Γ-[i + 1]-Function₃ L.termShiftVec :=
  .of_sigmaOne (termShiftVec_definable L) _ _

end

@[simp] lemma len_termShiftVec {k n ts : V} (hts : L.SemitermVec k n ts) :
    len (L.termShiftVec k n ts) = k := (construction L).resultVec_lh _ hts

@[simp] lemma nth_termShiftVec {k n ts i : V} (hts : L.SemitermVec k n ts) (hi : i < k) :
    (L.termShiftVec k n ts).[i] = L.termShift n ts.[i] :=
  (construction L).nth_resultVec _ hts hi

@[simp] lemma termShiftVec_nil (n : V) : L.termShiftVec 0 n 0 = 0 :=
  (construction L).resultVec_nil ![] _

lemma termShiftVec_cons {k n t ts : V} (ht : L.Semiterm n t) (hts : L.SemitermVec k n ts) :
    L.termShiftVec (k + 1) n (t ∷ ts) = L.termShift n t ∷ L.termShiftVec k n ts :=
  (construction L).resultVec_cons ![] hts ht

@[simp] lemma termShiftVec_cons₁ {n t₁ : V} (ht₁ : L.Semiterm n t₁) :
    L.termShiftVec 1 n ?[t₁] = ?[L.termShift n t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termShiftVec_cons] <;> simp [*]

@[simp] lemma termShiftVec_cons₂ {n t₁ t₂ : V} (ht₁ : L.Semiterm n t₁) (ht₂ : L.Semiterm n t₂) :
    L.termShiftVec 2 n ?[t₁, t₂] = ?[L.termShift n t₁, L.termShift n t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termShiftVec_cons] <;> simp [*]

@[simp] lemma Language.Semiterm.termShift {t} (ht : L.Semiterm n t) : L.Semiterm n (L.termShift n t) := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termShift_func, Language.Semiterm.func_iff, true_and]
    exact ⟨by simp [Language.termShiftVec, hv], fun i hi ↦ by
      rw [nth_termShiftVec hv hi]
      exact ih i hi⟩

@[simp] lemma Language.SemitermVec.termShiftVec {k n v} (hv : L.SemitermVec k n v) : L.SemitermVec k n (L.termShiftVec k n v) :=
  ⟨by simp [Language.termShiftVec, hv], fun i hi ↦ by
    rw [nth_termShiftVec hv hi]
    exact (hv.prop hi).termShift⟩

end termShift

namespace TermBShift

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 0 where
  bvar := .mkSigma “y n z m w | !qqBvarDef y (z + 1)” (by simp)
  fvar := .mkSigma “y n x m w | !qqFvarDef y x” (by simp)
  func := .mkSigma “y n k f v v' m w | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (_ _ z)        := ^#(z + 1)
  fvar (_ _ x)        := ^&x
  func (_ _ k f _ v') := ^func k f v'
  bvar_defined := by intro v; simp [blueprint]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermBShift

section termBShift

open TermBShift

variable (L)

def Language.termBShift (n t : V) : V := (construction L).result ![] n t

def Language.termBShiftVec (k n v : V) : V := (construction L).resultVec ![] k n v

variable {L}

variable {n : V}

@[simp] lemma termBShift_bvar {z} (hz : z < n) :
    L.termBShift n ^#z = ^#(z + 1) := by simp [Language.termBShift, hz, construction]

@[simp] lemma termBShift_fvar (x) :
    L.termBShift n ^&x = ^&x := by simp [Language.termBShift, construction]

@[simp] lemma termBShift_func {k f v} (hkf : L.Func k f) (hv : L.SemitermVec k n v) :
    L.termBShift n (^func k f v) = ^func k f (L.termBShiftVec k n v) := by
  simp [Language.termBShift, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termBShiftDef (pL : LDef) : 𝚺₁.Semisentence 3 :=
  (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termBShiftVecDef (pL : LDef) : 𝚺₁.Semisentence 4 := (blueprint pL).resultVec

variable (L)

lemma termBShift_defined : 𝚺₁-Function₂ L.termBShift via pL.termBShiftDef := by
  intro v; simpa using (construction L).result_defined v

@[simp] lemma eval_termBShiftDef (v : Fin 3 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termBShiftDef ↔ v 0 = L.termBShift (v 1) (v 2) := (termBShift_defined L).df.iff v

instance termBShift_definable : 𝚺₁-Function₂ L.termBShift :=
  (termBShift_defined L).to_definable

@[definability, simp] instance termBShift_definable' (Γ i) : Γ-[i + 1]-Function₂ L.termBShift := .of_sigmaOne (termBShift_definable L) _ _

lemma termBShiftVec_defined : 𝚺₁-Function₃ L.termBShiftVec via pL.termBShiftVecDef := by
  intro v; simpa using (construction L).resultVec_defined v

@[simp] lemma eval_termBShiftVecDef (v : Fin 4 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termBShiftVecDef ↔ v 0 = L.termBShiftVec (v 1) (v 2) (v 3) := (termBShiftVec_defined L).df.iff v

instance termBShiftVec_definable : 𝚺₁-Function₃ L.termBShiftVec :=
  (termBShiftVec_defined L).to_definable

@[simp, definability] instance termBShiftVec_definable' (Γ i) : Γ-[i + 1]-Function₃ L.termBShiftVec :=
  .of_sigmaOne (termBShiftVec_definable L) _ _

end

@[simp] lemma len_termBShiftVec {k n ts : V} (hts : L.SemitermVec k n ts) :
    len (L.termBShiftVec k n ts) = k := (construction L).resultVec_lh _ hts

@[simp] lemma nth_termBShiftVec {k n ts i : V} (hts : L.SemitermVec k n ts) (hi : i < k) :
    (L.termBShiftVec k n ts).[i] = L.termBShift n ts.[i] :=
  (construction L).nth_resultVec _ hts hi

@[simp] lemma termBShiftVec_nil (n : V) : L.termBShiftVec 0 n 0 = 0 :=
  (construction L).resultVec_nil ![] _

lemma termBShiftVec_cons {k n t ts : V} (ht : L.Semiterm n t) (hts : L.SemitermVec k n ts) :
    L.termBShiftVec (k + 1) n (t ∷ ts) = L.termBShift n t ∷ L.termBShiftVec k n ts :=
  (construction L).resultVec_cons ![] hts ht

@[simp] lemma termBShiftVec_cons₁ {n t₁ : V} (ht₁ : L.Semiterm n t₁) :
    L.termBShiftVec 1 n ?[t₁] = ?[L.termBShift n t₁] := by
  rw [show (1 : V) = 0 + 1  by simp, termBShiftVec_cons] <;> simp [*]

@[simp] lemma termBShiftVec_cons₂ {n t₁ t₂ : V} (ht₁ : L.Semiterm n t₁) (ht₂ : L.Semiterm n t₂) :
    L.termBShiftVec 2 n ?[t₁, t₂] = ?[L.termBShift n t₁, L.termBShift n t₂] := by
  rw [show (2 : V) = 0 + 1 + 1  by simp [one_add_one_eq_two], termBShiftVec_cons] <;> simp [*]

@[simp] lemma Language.Semiterm.termBShift {t} (ht : L.Semiterm n t) : L.Semiterm (n + 1) (L.termBShift n t) := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termBShift_func, Language.Semiterm.func_iff, true_and]
    exact ⟨by simp [Language.termBShiftVec, hv], fun i hi ↦ by
      rw [nth_termBShiftVec hv hi]
      exact ih i hi⟩

@[simp] lemma Language.SemitermVec.termBShiftVec {k n v} (hv : L.SemitermVec k n v) : L.SemitermVec k (n + 1) (L.termBShiftVec k n v) :=
  ⟨by simp [Language.termBShiftVec, hv], fun i hi ↦ by
    rw [nth_termBShiftVec hv hi]
    exact (hv.prop hi).termBShift⟩

lemma termBShift_termShift {t} (ht : L.Semiterm n t) : L.termBShift n (L.termShift n t) = L.termShift (n + 1) (L.termBShift n t) := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih
    simp only [termShift_func, Language.SemitermVec.termShiftVec, termBShift_func,
      Language.SemitermVec.termBShiftVec, qqFunc_inj, true_and, hkf, hv]
    apply nth_ext' k (by simp [hv]) (by simp [hv])
    intro i hi
    rw [nth_termBShiftVec hv.termShiftVec hi, nth_termShiftVec hv hi,
      nth_termShiftVec hv.termBShiftVec hi, nth_termBShiftVec hv hi, ih i hi]

end termBShift

variable (L)

def Language.qVec (k n w : V) : V := ^#0 ∷ L.termBShiftVec k n w

variable {L}

@[simp] lemma len_qVec {k n w : V} (h : L.SemitermVec k n w) : len (L.qVec k n w) = k + 1 := by simp [Language.qVec, h]

lemma Language.SemitermVec.qVec {k n w : V} (h : L.SemitermVec k n w) : L.SemitermVec (k + 1) (n + 1) (L.qVec k n w) :=
  ⟨by simp [h], by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [Language.qVec]
      · simpa [Language.qVec, nth_termBShiftVec h (by simpa using hi)] using
          h.prop (by simpa using hi) |>.termBShift⟩

lemma substs_cons_bShift {n m u t w} (ht : L.Semiterm n t) (hw : L.SemitermVec n m w) :
    L.termSubst (n + 1) m (u ∷ w) (L.termBShift n t) = L.termSubst n m w t := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hf hv ih
    simp [hf, hv]
    apply nth_ext' k (by simp [hv, hw]) (by simp [hv, hw])
    intro i hi
    simp [nth_termSubstVec hv.termBShiftVec hi, nth_termSubstVec hv hi, nth_termBShiftVec hv hi, ih i hi]

lemma termShift_termSubsts {n m w t} (ht : L.Semiterm n t) (hw : L.SemitermVec n m w) :
    L.termShift m (L.termSubst n m w t) = L.termSubst n m (L.termShiftVec n m w) (L.termShift n t) := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, nth_termShiftVec hw hz]
  · intro x; simp
  · intro k f v hf hv ih
    simp only [termSubst_func, Language.SemitermVec.termSubstVec, termShift_func,
      Language.SemitermVec.termShiftVec, qqFunc_inj, true_and, hf, hv, hw]
    apply nth_ext' k (by simp [hw, hv]) (by simp [hv])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv) hi,
      nth_termSubstVec hv hi,
      nth_termSubstVec hv.termShiftVec hi,
      nth_termShiftVec hv hi, ih i hi]

lemma bShift_substs {n m w t} (ht : L.Semiterm n t) (hw : L.SemitermVec n m w) :
    L.termBShift m (L.termSubst n m w t) = L.termSubst n (m + 1) (L.termBShiftVec n m w) t := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, nth_termBShiftVec hw hz]
  · intro x; simp
  · intro k f v hf hv ih
    simp only [hf, hv, termSubst_func, hw.termSubstVec hv, termBShift_func, qqFunc_inj, true_and]
    apply nth_ext' k (by simp [hw, hv]) (by simp [hv])
    intro i hi
    simp [nth_termBShiftVec (hw.termSubstVec hv) hi, nth_termSubstVec hv hi, ih i hi]

lemma substs_qVec_bShift {n t m w} (ht : L.Semiterm n t) (hw : L.SemitermVec n m w) :
    L.termSubst (n + 1) (m + 1) (L.qVec n m w) (L.termBShift n t) = L.termBShift m (L.termSubst n m w t) := by
  simp [Language.qVec, substs_cons_bShift ht hw.termBShiftVec, bShift_substs ht hw]

lemma termSubstVec_qVec_qVec {l n m : V} (hv : L.SemitermVec l n v) (hw : L.SemitermVec n m w) :
    L.termSubstVec (l + 1) (n + 1) (m + 1) (L.qVec n m w) (L.qVec l n v) = L.qVec l m (L.termSubstVec l n m w v) := by
  apply nth_ext' (l + 1) (by rw[len_termSubstVec hv.qVec]) (by simp [hw, hv])
  intro i hi
  unfold Language.qVec
  rw [termSubstVec_cons (by simp) hv.termBShiftVec]
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · simp
    have hi : i < l := by simpa using hi
    rw [nth_termSubstVec hv.termBShiftVec hi,
      nth_termBShiftVec hv hi,
      nth_termBShiftVec (hw.termSubstVec hv) hi,
      nth_termSubstVec hv hi,
      substs_cons_bShift (hv.2 i hi) hw.termBShiftVec,
      bShift_substs (hv.2 i hi) hw]

lemma termShift_qVec {n m w : V} (hw : L.SemitermVec n m w) :
    L.termShiftVec (n + 1) (m + 1) (L.qVec n m w) = L.qVec n m (L.termShiftVec n m w) := by
  apply nth_ext' (n + 1) (by rw [len_termShiftVec hw.qVec]) (by simp [hw])
  intro i hi
  rw [nth_termShiftVec hw.qVec hi]
  unfold Language.qVec
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp
  · rw [nth_cons_succ, nth_cons_succ,
      nth_termBShiftVec hw (by simpa using hi),
      nth_termBShiftVec hw.termShiftVec (by simpa using hi),
      nth_termShiftVec hw (by simpa using hi),
      termBShift_termShift (hw.2 i (by simpa using hi))]

section fvfree

variable (L)

def Language.IsTermFVFree (n t : V) : Prop := L.Semiterm n t ∧ L.termShift n t = t

variable {L}

@[simp] lemma Language.IsTermFVFree.bvar (x : V) : L.IsTermFVFree n ^#x ↔ x < n := by
  simp [Language.IsTermFVFree]
  intro h; simp [h]

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

lemma qqFunc_absolute (k f v : ℕ) : ((^func k f v : ℕ) : V) = ^func (k : V) (f : V) (v : V) := by simp [qqFunc, nat_cast_pair]

@[simp] lemma zero_semiterm : ⌜ℒₒᵣ⌝.Semiterm n (𝟎 : V) := by
  simp [Formalized.zero, qqFunc_absolute]

@[simp] lemma one_semiterm : ⌜ℒₒᵣ⌝.Semiterm n (𝟏 : V) := by
  simp [Formalized.one, qqFunc_absolute]

namespace Numeral

def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y | y = !!(Semiterm.Operator.numeral ℒₒᵣ Formalized.one)” (by simp)
  succ := .mkSigma “y t n | ∃ p,
    !mkVec₂Def p t !!(Semiterm.Operator.numeral ℒₒᵣ Formalized.one) ∧
    !qqFuncDef y 2 !!(Semiterm.Operator.numeral ℒₒᵣ addIndex) p” (by simp)

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

@[simp] lemma numeralAux_semiterm (n x : V) : ⌜ℒₒᵣ⌝.Semiterm n (numeralAux x) := by
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

@[simp] lemma numeral_semiterm (n x : V) : ⌜ℒₒᵣ⌝.Semiterm n (numeral x) := by
  by_cases hx : x = 0 <;> simp [hx, numeral]

section

def _root_.LO.FirstOrder.Arith.numeralDef : 𝚺₁.Semisentence 2 := .mkSigma
  “t x |
    (x = 0 → t = !!(Semiterm.Operator.numeral ℒₒᵣ Formalized.zero)) ∧
    (x ≠ 0 → ∃ x', !subDef x' x 1 ∧ !numeralAuxDef t x')”
  (by simp)

lemma numeral_defined : 𝚺₁-Function₁ (numeral : V → V) via numeralDef := fun v ↦ by
  simp [numeralDef, numeral_eq_natCast]
  by_cases hv1 : v 1 = 0 <;> simp [hv1, numeral]

@[simp] lemma eval_numeralDef (v) :
    Semiformula.Evalbm V v numeralDef.val ↔ v 0 = numeral (v 1) := numeral_defined.df.iff v

@[simp] instance numeral_definable : 𝚺₁-Function₁ (numeral : V → V) := numeral_defined.to_definable

@[simp] instance numeral_definable' (Γ m) : Γ-[m + 1]-Function₁ (numeral : V → V) := .of_sigmaOne numeral_definable _ _

end

@[simp] lemma numeral_substs {w : V} (hw : ⌜ℒₒᵣ⌝.SemitermVec n m w) (x : V) :
    ⌜ℒₒᵣ⌝.termSubst n m w (numeral x) = numeral x := by
  induction x using induction_sigma1
  · definability
  case zero => simp [hw, Formalized.zero, qqFunc_absolute]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [hw, Formalized.one, qqFunc_absolute]
    · simp [qqAdd, hw, ih, Formalized.one, qqFunc_absolute]

@[simp] lemma numeral_shift (x : V) :
    ⌜ℒₒᵣ⌝.termShift n (numeral x) = numeral x := by
  induction x using induction_sigma1
  · definability
  case zero => simp [Formalized.zero, qqFunc_absolute]
  case succ x ih =>
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [Formalized.one, qqFunc_absolute]
    · simp [qqAdd, ih, Formalized.one, qqFunc_absolute]

@[simp] lemma numeral_bShift (x : V) :
    ⌜ℒₒᵣ⌝.termBShift n (numeral x) = numeral x := by
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
