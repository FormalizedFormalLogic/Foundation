import Arithmetization.ISigmaOne.Metamath.Term.Basic

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

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

def _root_.LO.FirstOrder.Arith.LDef.termSubstDef (pL : LDef) : 𝚺₁-Semisentence 5 := (blueprint pL).result.rew <| Rew.substs ![#0, #1, #4, #2, #3]

def _root_.LO.FirstOrder.Arith.LDef.termSubstVecDef (pL : LDef) : 𝚺₁-Semisentence 6 := (blueprint pL).resultVec.rew <| Rew.substs ![#0, #1, #2, #5, #3, #4]

variable (L)

lemma termSubst_defined : Arith.DefinedFunction (fun v ↦ L.termSubst (v 0) (v 1) (v 2) (v 3)) pL.termSubstDef := by
  intro v; simpa [LDef.termSubstDef, Language.termSubst] using (construction L).result_defined ![v 0, v 1, v 4, v 2, v 3]

@[simp] lemma eval_termSubstDef (v : Fin 5 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termSubstDef ↔ v 0 = L.termSubst (v 1) (v 2) (v 3) (v 4) := (termSubst_defined L).df.iff v

instance termSubst_definable : Arith.DefinableFunction ℒₒᵣ 𝚺₁ (fun v : Fin 4 → V ↦ L.termSubst (v 0) (v 1) (v 2) (v 3)) :=
  Defined.to_definable _ (termSubst_defined L)

instance termSubst_definable₂ (n m : V) : 𝚺₁-Function₂ (L.termSubst n m) := by
  simpa using DefinableFunction.retractiont (n := 2) (termSubst_definable L) ![&n, &m, #0, #1]

@[simp, definability] instance termSubst_definable₂' (Γ k) (n m : V) : (Γ, k + 1)-Function₂ (L.termSubst n m) :=
  .of_sigmaOne (termSubst_definable₂ L n m) _ _

lemma termSubstVec_defined : Arith.DefinedFunction (fun v ↦ L.termSubstVec (v 0) (v 1) (v 2) (v 3) (v 4)) pL.termSubstVecDef := by
  intro v; simpa [LDef.termSubstVecDef, Language.termSubstVec] using (construction L).resultVec_defined ![v 0, v 1, v 2, v 5, v 3, v 4]

@[simp] lemma eval_termSubstVecDef (v : Fin 6 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termSubstVecDef ↔ v 0 = L.termSubstVec (v 1) (v 2) (v 3) (v 4) (v 5) := (termSubstVec_defined L).df.iff v

instance termSubstVec_definable : Arith.DefinableFunction ℒₒᵣ 𝚺₁ (fun v : Fin 5 → V ↦ L.termSubstVec (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  Defined.to_definable _ (termSubstVec_defined L)

instance termSubstVec_definable₂ (k n m : V) : 𝚺₁-Function₂ (L.termSubstVec k n m) := by
  simpa using DefinableFunction.retractiont (n := 2) (termSubstVec_definable L) ![&k, &n, &m, #0, #1]

@[simp, definability] instance termSubstVec_definable₂' (Γ i) (k n m : V) : (Γ, i + 1)-Function₂ (L.termSubstVec k n m) :=
  .of_sigmaOne (termSubstVec_definable₂ L k n m) _ _

end

lemma nth_termSubstVec {k n ts i : V} (hts : L.SemitermVec k n ts) (hi : i < k) :
    (L.termSubstVec k n m w ts).[i] = L.termSubst n m w ts.[i] :=
  (construction L).nth_resultVec _ hts hi

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

def _root_.LO.FirstOrder.Arith.LDef.termShiftDef (pL : LDef) : 𝚺₁-Semisentence 3 :=
  (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termShiftVecDef (pL : LDef) : 𝚺₁-Semisentence 4 := (blueprint pL).resultVec

variable (L)

lemma termShift_defined : 𝚺₁-Function₂ L.termShift via pL.termShiftDef := by
  intro v; simpa [LDef.termShiftDef, Language.termShift] using (construction L).result_defined v

@[simp] lemma eval_termShiftDef (v : Fin 3 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termShiftDef ↔ v 0 = L.termShift (v 1) (v 2) := (termShift_defined L).df.iff v

instance termShift_definable : 𝚺₁-Function₂ L.termShift :=
  Defined.to_definable _ (termShift_defined L)

@[definability, simp] instance termShift_definable' (Γ i) : (Γ, i + 1)-Function₂ L.termShift := .of_sigmaOne (termShift_definable L) _ _

lemma termShiftVec_defined : 𝚺₁-Function₃ L.termShiftVec via pL.termShiftVecDef := by
  intro v; simpa [LDef.termShiftVecDef, Language.termShiftVec] using (construction L).resultVec_defined v

@[simp] lemma eval_termShiftVecDef (v : Fin 4 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termShiftVecDef ↔ v 0 = L.termShiftVec (v 1) (v 2) (v 3) := (termShiftVec_defined L).df.iff v

instance termShiftVec_definable : 𝚺₁-Function₃ L.termShiftVec :=
  Defined.to_definable _ (termShiftVec_defined L)

@[simp, definability] instance termShiftVec_definable' (Γ i) : (Γ, i + 1)-Function₃ L.termShiftVec :=
  .of_sigmaOne (termShiftVec_definable L) _ _

end

lemma nth_termShiftVec {k n ts i : V} (hts : L.SemitermVec k n ts) (hi : i < k) :
    (L.termShiftVec k n ts).[i] = L.termShift n ts.[i] :=
  (construction L).nth_resultVec _ hts hi

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

def _root_.LO.FirstOrder.Arith.LDef.termBShiftDef (pL : LDef) : 𝚺₁-Semisentence 3 :=
  (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termBShiftVecDef (pL : LDef) : 𝚺₁-Semisentence 4 := (blueprint pL).resultVec

variable (L)

lemma termBShift_defined : 𝚺₁-Function₂ L.termBShift via pL.termBShiftDef := by
  intro v; simpa using (construction L).result_defined v

@[simp] lemma eval_termBShiftDef (v : Fin 3 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termBShiftDef ↔ v 0 = L.termBShift (v 1) (v 2) := (termBShift_defined L).df.iff v

instance termBShift_definable : 𝚺₁-Function₂ L.termBShift :=
  Defined.to_definable _ (termBShift_defined L)

@[definability, simp] instance termBShift_definable' (Γ i) : (Γ, i + 1)-Function₂ L.termBShift := .of_sigmaOne (termBShift_definable L) _ _

lemma termBShiftVec_defined : 𝚺₁-Function₃ L.termBShiftVec via pL.termBShiftVecDef := by
  intro v; simpa using (construction L).resultVec_defined v

@[simp] lemma eval_termBShiftVecDef (v : Fin 4 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termBShiftVecDef ↔ v 0 = L.termBShiftVec (v 1) (v 2) (v 3) := (termBShiftVec_defined L).df.iff v

instance termBShiftVec_definable : 𝚺₁-Function₃ L.termBShiftVec :=
  Defined.to_definable _ (termBShiftVec_defined L)

@[simp, definability] instance termBShiftVec_definable' (Γ i) : (Γ, i + 1)-Function₃ L.termBShiftVec :=
  .of_sigmaOne (termBShiftVec_definable L) _ _

end

lemma nth_termBShiftVec {k n ts i : V} (hts : L.SemitermVec k n ts) (hi : i < k) :
    (L.termBShiftVec k n ts).[i] = L.termBShift n ts.[i] :=
  (construction L).nth_resultVec _ hts hi

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

end termBShift

end

namespace Formalized

protected def zero : ℕ := ^func 0 zeroIndex 0

protected def one : ℕ := ^func 0 oneIndex 0

abbrev qqAdd (x y : V) := ^func 2 (addIndex : V) ?[x, y]

abbrev qqMul (x y : V) := ^func 2 (mulIndex : V) ?[x, y]

notation "𝟎" => Formalized.zero

notation "𝟏" => Formalized.one

infixl:60 " ^+ " => qqAdd

infixl:80 " ^* " => qqMul

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
  succ_defined := by intro v; simp [blueprint, numeral_eq_natCast]

def numeralAux (x : V) : V := construction.result ![] x

@[simp] lemma numeralAux_zero : numeralAux (0 : V) = 𝟏 := by simp [numeralAux, construction]

@[simp] lemma numeralAux_succ (x : V) : numeralAux (x + 1) = numeralAux x ^+ 𝟏 := by simp [numeralAux, construction]

section

def numeralAuxDef : 𝚺₁-Semisentence 2 := blueprint.resultDef

lemma numeralAux_defined : 𝚺₁-Function₁ (numeralAux : V → V) via numeralAuxDef :=
  fun v ↦ by simp [construction.result_defined_iff, numeralAuxDef]; rfl

@[simp] lemma eval_numeralAuxDef (v) :
    Semiformula.Evalbm V v numeralAuxDef.val ↔ v 0 = numeralAux (v 1) := numeralAux_defined.df.iff v

@[definability, simp] instance seqExp_definable : 𝚺₁-Function₁ (numeralAux : V → V) := Defined.to_definable _ numeralAux_defined

end

@[simp] lemma numeralAux_semiterm (n x : V) : ⌜ℒₒᵣ⌝.Semiterm n (numeralAux x) := by
  induction x using induction_iSigmaOne
  · definability
  case zero => simp
  case succ x ih => simp [ih]

end Numeral

section numeral

open Numeral

def numeral (x : V) : V := if x = 0 then 𝟎 else numeralAux (x - 1)

@[simp] lemma numeral_zero : numeral (0 : V) = 𝟎 := by simp [numeral]

@[simp] lemma numeral_semiterm (n x : V) : ⌜ℒₒᵣ⌝.Semiterm n (numeral x) := by
  by_cases hx : x = 0 <;> simp [hx, numeral]

section

def numeralDef : 𝚺₁-Semisentence 2 := .mkSigma
  “t x |
    (x = 0 → t = !!(Semiterm.Operator.numeral ℒₒᵣ Formalized.zero)) ∧
    (x ≠ 0 → ∃ x', !subDef x' x 1 ∧ !numeralAuxDef t x')”
  (by simp)

lemma numeral_defined : 𝚺₁-Function₁ (numeral : V → V) via numeralDef := fun v ↦ by
  simp [numeralDef, numeral_eq_natCast]
  by_cases hv1 : v 1 = 0 <;> simp [hv1, numeral]

@[simp] lemma eval_numeralDef (v) :
    Semiformula.Evalbm V v numeralDef.val ↔ v 0 = numeral (v 1) := numeral_defined.df.iff v

@[simp] instance numeral_definable : 𝚺₁-Function₁ (numeral : V → V) := Defined.to_definable _ numeral_defined

@[simp] instance numeral_definable' (Γ m) : (Γ, m + 1)-Function₁ (numeral : V → V) := .of_sigmaOne numeral_definable _ _

end

end numeral

end Formalized

end LO.Arith

end
