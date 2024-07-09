import Arithmetization.ISigmaOne.Metamath.Term.Basic

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

section

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace TermSubst

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 2 where
  bvar := .mkSigma “y n z m w | !znthDef y w z” (by simp)
  fvar := .mkSigma “y n x m w | !qqFvarDef y x” (by simp)
  func := .mkSigma “y n k f v v' m w | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (param _ z)        := znth (param 1) z
  fvar (_     _ x)        := &̂x
  func (_     _ k f _ v') := f̂unc k f v'
  bvar_defined := by intro v; simp [blueprint]; rfl
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermSubst

section termSubst

open TermSubst

variable (L)

def Language.termSubst (n m w t : V) : V := (construction L).result ![m, w] n t

def Language.termSubstSeq (k n m w v : V) : V := (construction L).resultSeq ![m, w] k n v

variable {L}

variable {n m w : V}

@[simp] lemma termSubst_bvar {z} (hz : z < n) :
    L.termSubst n m w #̂z = znth w z := by simp [Language.termSubst, hz, construction]

@[simp] lemma termSubst_fvar (x) :
    L.termSubst n m w &̂x = &̂x := by simp [Language.termSubst, construction]

@[simp] lemma termSubst_func {k f v} (hkf : L.Func k f) (hv : L.SemitermSeq k n v) :
    L.termSubst n m w (f̂unc k f v) = f̂unc k f (L.termSubstSeq k n m w v) := by
  simp [Language.termSubst, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termSubstDef (pL : LDef) : 𝚺₁-Semisentence 5 := (blueprint pL).result.rew <| Rew.substs ![#0, #1, #4, #2, #3]

def _root_.LO.FirstOrder.Arith.LDef.termSubstSeqDef (pL : LDef) : 𝚺₁-Semisentence 6 := (blueprint pL).resultSeq.rew <| Rew.substs ![#0, #1, #2, #5, #3, #4]

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

lemma termSubstSeq_defined : Arith.DefinedFunction (fun v ↦ L.termSubstSeq (v 0) (v 1) (v 2) (v 3) (v 4)) pL.termSubstSeqDef := by
  intro v; simpa [LDef.termSubstSeqDef, Language.termSubstSeq] using (construction L).resultSeq_defined ![v 0, v 1, v 2, v 5, v 3, v 4]

@[simp] lemma eval_termSubstSeqDef (v : Fin 6 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termSubstSeqDef ↔ v 0 = L.termSubstSeq (v 1) (v 2) (v 3) (v 4) (v 5) := (termSubstSeq_defined L).df.iff v

instance termSubstSeq_definable : Arith.DefinableFunction ℒₒᵣ 𝚺₁ (fun v : Fin 5 → V ↦ L.termSubstSeq (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  Defined.to_definable _ (termSubstSeq_defined L)

instance termSubstSeq_definable₂ (k n m : V) : 𝚺₁-Function₂ (L.termSubstSeq k n m) := by
  simpa using DefinableFunction.retractiont (n := 2) (termSubstSeq_definable L) ![&k, &n, &m, #0, #1]

@[simp, definability] instance termSubstSeq_definable₂' (Γ i) (k n m : V) : (Γ, i + 1)-Function₂ (L.termSubstSeq k n m) :=
  .of_sigmaOne (termSubstSeq_definable₂ L k n m) _ _

end

lemma termSubst_rng_semiterm {t} (hw : L.SemitermSeq n m w) (ht : L.Semiterm n t) : L.Semiterm m (L.termSubst n m w t) := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz, hw.prop_znth]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termSubst_func, Language.Semiterm.func_iff, true_and]
    exact ⟨by simp [Language.termSubstSeq, hv], by simp [Language.termSubstSeq, hv], fun i z hiz ↦ by
      rcases (construction L).resultSeq_prop' _ hv hiz with ⟨u, hiu, rfl⟩
      exact ih _ _ hiu⟩

@[simp] lemma Language.SemitermSeq.termSubstSeq {k n m v} (hw : L.SemitermSeq n m w) (hv : L.SemitermSeq k n v) : L.SemitermSeq k m (L.termSubstSeq k n m w v) :=
  ⟨by simp [Language.termSubstSeq, hv], by simp [Language.termSubstSeq, hv], fun i u hiu ↦ by
    rcases (construction L).resultSeq_prop' _ hv hiu with ⟨u', hiu', rfl⟩
    exact termSubst_rng_semiterm hw (hv.prop _ _ hiu')⟩

end termSubst

namespace TermShift

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 0 where
  bvar := .mkSigma “y n z m w | !qqBvarDef y z” (by simp)
  fvar := .mkSigma “y n x m w | !qqFvarDef y (x + 1)” (by simp)
  func := .mkSigma “y n k f v v' m w | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (_ _ z)        := #̂z
  fvar (_ _ x)        := &̂(x + 1)
  func (_ _ k f _ v') := f̂unc k f v'
  bvar_defined := by intro v; simp [blueprint]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermShift

section termShift

open TermShift

variable (L)

def Language.termShift (n t : V) : V := (construction L).result ![] n t

def Language.termShiftSeq (k n v : V) : V := (construction L).resultSeq ![] k n v

variable {L}

variable {n : V}

@[simp] lemma termShift_bvar {z} (hz : z < n) :
    L.termShift n #̂z = #̂z := by simp [Language.termShift, hz, construction]

@[simp] lemma termShift_fvar (x) :
    L.termShift n &̂x = &̂(x + 1) := by simp [Language.termShift, construction]

@[simp] lemma termShift_func {k f v} (hkf : L.Func k f) (hv : L.SemitermSeq k n v) :
    L.termShift n (f̂unc k f v) = f̂unc k f (L.termShiftSeq k n v) := by
  simp [Language.termShift, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termShiftDef (pL : LDef) : 𝚺₁-Semisentence 3 :=
  (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termShiftSeqDef (pL : LDef) : 𝚺₁-Semisentence 4 := (blueprint pL).resultSeq

variable (L)

lemma termShift_defined : 𝚺₁-Function₂ L.termShift via pL.termShiftDef := by
  intro v; simpa [LDef.termShiftDef, Language.termShift] using (construction L).result_defined v

@[simp] lemma eval_termShiftDef (v : Fin 3 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termShiftDef ↔ v 0 = L.termShift (v 1) (v 2) := (termShift_defined L).df.iff v

instance termShift_definable : 𝚺₁-Function₂ L.termShift :=
  Defined.to_definable _ (termShift_defined L)

@[definability, simp] instance termShift_definable' (Γ i) : (Γ, i + 1)-Function₂ L.termShift := .of_sigmaOne (termShift_definable L) _ _

lemma termShiftSeq_defined : 𝚺₁-Function₃ L.termShiftSeq via pL.termShiftSeqDef := by
  intro v; simpa [LDef.termShiftSeqDef, Language.termShiftSeq] using (construction L).resultSeq_defined v

@[simp] lemma eval_termShiftSeqDef (v : Fin 4 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termShiftSeqDef ↔ v 0 = L.termShiftSeq (v 1) (v 2) (v 3) := (termShiftSeq_defined L).df.iff v

instance termShiftSeq_definable : 𝚺₁-Function₃ L.termShiftSeq :=
  Defined.to_definable _ (termShiftSeq_defined L)

@[simp, definability] instance termShiftSeq_definable' (Γ i) : (Γ, i + 1)-Function₃ L.termShiftSeq :=
  .of_sigmaOne (termShiftSeq_definable L) _ _

end

@[simp] lemma Language.Semiterm.termShift {t} (ht : L.Semiterm n t) : L.Semiterm n (L.termShift n t) := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termShift_func, Language.Semiterm.func_iff, true_and]
    exact ⟨by simp [Language.termShiftSeq, hv], by simp [Language.termShiftSeq, hv], fun i z hiz ↦ by
      rcases (construction L).resultSeq_prop' _ hv hiz with ⟨u, hiu, rfl⟩
      exact ih _ _ hiu⟩

@[simp] lemma Language.SemitermSeq.termShiftSeq {k n v} (hv : L.SemitermSeq k n v) : L.SemitermSeq k n (L.termShiftSeq k n v) :=
  ⟨by simp [Language.termShiftSeq, hv], by simp [Language.termShiftSeq, hv], fun i u hiu ↦ by
    rcases (construction L).resultSeq_prop' _ hv hiu with ⟨u', hiu', rfl⟩
    exact (hv.prop _ _ hiu').termShift⟩

end termShift

namespace TermBShift

def blueprint (pL : LDef) : Language.TermRec.Blueprint pL 0 where
  bvar := .mkSigma “y n z m w | !qqBvarDef y (z + 1)” (by simp)
  fvar := .mkSigma “y n x m w | !qqFvarDef y x” (by simp)
  func := .mkSigma “y n k f v v' m w | !qqFuncDef y k f v'” (by simp)

variable (L)

def construction : Language.TermRec.Construction V L (blueprint pL) where
  bvar (_ _ z)        := #̂(z + 1)
  fvar (_ _ x)        := &̂x
  func (_ _ k f _ v') := f̂unc k f v'
  bvar_defined := by intro v; simp [blueprint]
  fvar_defined := by intro v; simp [blueprint]
  func_defined := by intro v; simp [blueprint]; rfl

end TermBShift

section termBShift

open TermBShift

variable (L)

def Language.termBShift (n t : V) : V := (construction L).result ![] n t

def Language.termBShiftSeq (k n v : V) : V := (construction L).resultSeq ![] k n v

variable {L}

variable {n : V}

@[simp] lemma termBShift_bvar {z} (hz : z < n) :
    L.termBShift n #̂z = #̂(z + 1) := by simp [Language.termBShift, hz, construction]

@[simp] lemma termBShift_fvar (x) :
    L.termBShift n &̂x = &̂x := by simp [Language.termBShift, construction]

@[simp] lemma termBShift_func {k f v} (hkf : L.Func k f) (hv : L.SemitermSeq k n v) :
    L.termBShift n (f̂unc k f v) = f̂unc k f (L.termBShiftSeq k n v) := by
  simp [Language.termBShift, construction, hkf, hv]; rfl

section

def _root_.LO.FirstOrder.Arith.LDef.termBShiftDef (pL : LDef) : 𝚺₁-Semisentence 3 :=
  (blueprint pL).result

def _root_.LO.FirstOrder.Arith.LDef.termBShiftSeqDef (pL : LDef) : 𝚺₁-Semisentence 4 := (blueprint pL).resultSeq

variable (L)

lemma termBShift_defined : 𝚺₁-Function₂ L.termBShift via pL.termBShiftDef := by
  intro v; simpa using (construction L).result_defined v

@[simp] lemma eval_termBShiftDef (v : Fin 3 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termBShiftDef ↔ v 0 = L.termBShift (v 1) (v 2) := (termBShift_defined L).df.iff v

instance termBShift_definable : 𝚺₁-Function₂ L.termBShift :=
  Defined.to_definable _ (termBShift_defined L)

@[definability, simp] instance termBShift_definable' (Γ i) : (Γ, i + 1)-Function₂ L.termBShift := .of_sigmaOne (termBShift_definable L) _ _

lemma termBShiftSeq_defined : 𝚺₁-Function₃ L.termBShiftSeq via pL.termBShiftSeqDef := by
  intro v; simpa using (construction L).resultSeq_defined v

@[simp] lemma eval_termBShiftSeqDef (v : Fin 4 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.termBShiftSeqDef ↔ v 0 = L.termBShiftSeq (v 1) (v 2) (v 3) := (termBShiftSeq_defined L).df.iff v

instance termBShiftSeq_definable : 𝚺₁-Function₃ L.termBShiftSeq :=
  Defined.to_definable _ (termBShiftSeq_defined L)

@[simp, definability] instance termBShiftSeq_definable' (Γ i) : (Γ, i + 1)-Function₃ L.termBShiftSeq :=
  .of_sigmaOne (termBShiftSeq_definable L) _ _

end

@[simp] lemma Language.Semiterm.termBShift {t} (ht : L.Semiterm n t) : L.Semiterm (n + 1) (L.termBShift n t) := by
  apply Language.Semiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz; simp [hz]
  · intro x; simp
  · intro k f v hkf hv ih;
    simp only [hkf, hv, termBShift_func, Language.Semiterm.func_iff, true_and]
    exact ⟨by simp [Language.termBShiftSeq, hv], by simp [Language.termBShiftSeq, hv], fun i z hiz ↦ by
      rcases (construction L).resultSeq_prop' _ hv hiz with ⟨u, hiu, rfl⟩
      exact ih _ _ hiu⟩

@[simp] lemma Language.SemitermSeq.termBShiftSeq {k n v} (hv : L.SemitermSeq k n v) : L.SemitermSeq k (n + 1) (L.termBShiftSeq k n v) :=
  ⟨by simp [Language.termBShiftSeq, hv], by simp [Language.termBShiftSeq, hv], fun i u hiu ↦ by
    rcases (construction L).resultSeq_prop' _ hv hiu with ⟨u', hiu', rfl⟩
    exact (hv.prop _ _ hiu').termBShift⟩

end termBShift

end

namespace Formalized

abbrev LOR : Arith.Language V := Language.codeIn ℒₒᵣ V

notation "⌜ℒₒᵣ⌝" => LOR

def zeroIndex : ℕ := Encodable.encode (Language.Zero.zero : (ℒₒᵣ : FirstOrder.Language).Func 0)

def oneIndex : ℕ := Encodable.encode (Language.One.one : (ℒₒᵣ : FirstOrder.Language).Func 0)

def addIndex : ℕ := Encodable.encode (Language.Add.add : (ℒₒᵣ : FirstOrder.Language).Func 2)

def mulIndex : ℕ := Encodable.encode (Language.Mul.mul : (ℒₒᵣ : FirstOrder.Language).Func 2)

def eqIndex : ℕ := Encodable.encode (Language.Eq.eq : (ℒₒᵣ : FirstOrder.Language).Rel 2)

def ltIndex : ℕ := Encodable.encode (Language.LT.lt : (ℒₒᵣ : FirstOrder.Language).Rel 2)

protected def zero : ℕ := f̂unc 0 zeroIndex ∅

protected def one : ℕ := f̂unc 0 oneIndex ∅

abbrev qqAdd (x y : V) := f̂unc 2 (addIndex : V) !⟦x, y⟧

abbrev qqMul (x y : V) := f̂unc 2 (mulIndex : V) !⟦x, y⟧

notation "𝟎" => Formalized.zero

notation "𝟏" => Formalized.one

infixl:60 " +̂  " => qqAdd

infixl:80 " *̂ " => qqMul

lemma qqFunc_absolute (k f v : ℕ) : ((f̂unc k f v : ℕ) : V) = f̂unc (k : V) (f : V) (v : V) := by simp [qqFunc, nat_cast_pair]

@[simp] lemma LOR_func_zeroIndex : ⌜ℒₒᵣ⌝.Func 0 (zeroIndex : V) := by
  simpa using codeIn_func_encode (M := V) (L := ℒₒᵣ) 0 Language.Zero.zero

@[simp] lemma LOR_func_oneIndex : ⌜ℒₒᵣ⌝.Func 0 (oneIndex : V) := by
  simpa using codeIn_func_encode (M := V) (L := ℒₒᵣ) 0 Language.One.one

@[simp] lemma LOR_func_addIndex : ⌜ℒₒᵣ⌝.Func 2 (addIndex : V) := by
  simpa using codeIn_func_encode (M := V) (L := ℒₒᵣ) 2 Language.Add.add

@[simp] lemma LOR_func_mulIndex : ⌜ℒₒᵣ⌝.Func 2 (mulIndex : V) := by
  simpa using codeIn_func_encode (M := V) (L := ℒₒᵣ) 2 Language.Mul.mul

@[simp] lemma LOR_rel_eqIndex : ⌜ℒₒᵣ⌝.Rel 2 (eqIndex : V) := by
  simpa using codeIn_rel_encode (M := V) (L := ℒₒᵣ) 2 Language.Eq.eq

@[simp] lemma LOR_rel_ltIndex : ⌜ℒₒᵣ⌝.Rel 2 (ltIndex : V) := by
  simpa using codeIn_rel_encode (M := V) (L := ℒₒᵣ) 2 Language.LT.lt

@[simp] lemma zero_semiterm : ⌜ℒₒᵣ⌝.Semiterm n (𝟎 : V) := by
  simp [Formalized.zero, qqFunc_absolute]

@[simp] lemma one_semiterm : ⌜ℒₒᵣ⌝.Semiterm n (𝟏 : V) := by
  simp [Formalized.one, qqFunc_absolute]

namespace Numeral

def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y | y = !!(Semiterm.Operator.numeral ℒₒᵣ Formalized.one)” (by simp)
  succ := .mkSigma “y t n | ∃ p,
    !mkSeq₂Def p t !!(Semiterm.Operator.numeral ℒₒᵣ Formalized.one) ∧
    !qqFuncDef y 2 !!(Semiterm.Operator.numeral ℒₒᵣ addIndex) p” (by simp)

def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 𝟏
  succ := fun _ _ t ↦ t +̂ 𝟏
  zero_defined := by intro v; simp [blueprint, numeral_eq_natCast]
  succ_defined := by intro v; simp [blueprint, numeral_eq_natCast]

def numeralAux (x : V) : V := construction.result ![] x

@[simp] lemma numeralAux_zero : numeralAux (0 : V) = 𝟏 := by simp [numeralAux, construction]

@[simp] lemma numeralAux_succ (x : V) : numeralAux (x + 1) = numeralAux x +̂ 𝟏 := by simp [numeralAux, construction]

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

@[definability, simp] instance numeral_definable : 𝚺₁-Function₁ (numeral : V → V) := Defined.to_definable _ numeral_defined

@[definability, simp] instance numeral_definable' (Γ m) : (Γ, m + 1)-Function₁ (numeral : V → V) := .of_sigmaOne numeral_definable _ _

end

end numeral

end Formalized

end LO.Arith

end
