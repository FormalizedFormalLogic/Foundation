import Arithmetization.ISigmaOne.Metamath.Formula.Functions


noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace QQConj

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y n | !qqVerumDef y n” (by simp)
  cons := .mkSigma “y p ps ih n | !qqAndDef y n p ih” (by simp)

def construction : VecRec.Construction V blueprint where
  nil (param) := ^⊤[param 0]
  cons (param) p _ ih := p ^⋏[param 0] ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]; rfl

end QQConj

section qqConj

open QQConj

def qqConj (n ps : V) : V := construction.result ![n] ps

scoped notation:65 "^⋀[" n "] " ps:66 => qqConj n ps

scoped notation:65 "^⋀ " ps:66 => qqConj 0 ps

@[simp] lemma qqConj_nil (n : V) : ^⋀[n] 0 = ^⊤[n] := by simp [qqConj, construction]

@[simp] lemma qqConj_cons (n p ps : V) : ^⋀[n] (p ∷ ps) = p ^⋏[n] (^⋀[n] ps) := by simp [qqConj, construction]

section

def _root_.LO.FirstOrder.Arith.qqConjDef : 𝚺₁.Semisentence 3 := blueprint.resultDef.rew (Rew.substs ![#0, #2, #1])

lemma qqConj_defined : 𝚺₁-Function₂ (qqConj : V → V → V) via qqConjDef := by
  intro v; simpa [qqConjDef] using construction.result_defined ![v 0, v 2, v 1]

@[simp] lemma eval_qqConj (v) :
    Semiformula.Evalbm V v qqConjDef.val ↔ v 0 = qqConj (v 1) (v 2) := qqConj_defined.df.iff v

instance qqConj_definable : 𝚺₁-Function₂ (qqConj : V → V → V) := Defined.to_definable _ qqConj_defined

instance qqConj_definable' (Γ) : Γ-[m + 1]-Function₂ (qqConj : V → V → V) := .of_sigmaOne qqConj_definable _ _

end

@[simp]
lemma qqConj_semiformula {n ps : V} :
    L.Semiformula n (^⋀[n] ps) ↔ (∀ i < len ps, L.Semiformula n ps.[i]) := by
  induction ps using cons_induction_sigma₁
  · definability
  case nil => simp
  case cons p ps ih =>
    simp [ih]
    constructor
    · rintro ⟨hp, hps⟩ i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simpa using hp
      · simpa using hps i (by simpa using hi)
    · intro h
      exact ⟨
        by simpa using h 0 (by simp),
        fun i hi ↦ by simpa using h (i + 1) (by simpa using hi)⟩

@[simp] lemma len_le_conj (n ps : V) : len ps ≤ ^⋀[n] ps := by
  induction ps using cons_induction_sigma₁
  · definability
  case nil => simp [qqVerum]
  case cons p ps ih =>
    simp only [len_cons, qqConj_cons, succ_le_iff_lt]
    exact lt_of_le_of_lt ih (by simp)

end qqConj

namespace QQDisj

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y n | !qqFalsumDef y n” (by simp)
  cons := .mkSigma “y p ps ih n | !qqOrDef y n p ih” (by simp)

def construction : VecRec.Construction V blueprint where
  nil (param) := ^⊥[param 0]
  cons (param) p _ ih := p ^⋎[param 0] ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]; rfl

end QQDisj

section qqDisj

open QQDisj

def qqDisj (n ps : V) : V := construction.result ![n] ps

scoped notation:65 "^⋁[" n "] " ps:66 => qqDisj n ps

scoped notation:65 "^⋁ " ps:66 => qqDisj 0 ps

@[simp] lemma qqDisj_nil (n : V) : ^⋁[n] 0 = ^⊥[n] := by simp [qqDisj, construction]

@[simp] lemma qqDisj_cons (n p ps : V) : ^⋁[n] (p ∷ ps) = p ^⋎[n] (^⋁[n] ps) := by simp [qqDisj, construction]

section

def _root_.LO.FirstOrder.Arith.qqDisjDef : 𝚺₁.Semisentence 3 := blueprint.resultDef.rew (Rew.substs ![#0, #2, #1])

lemma qqDisj_defined : 𝚺₁-Function₂ (qqDisj : V → V → V) via qqDisjDef := by
  intro v; simpa [qqDisjDef] using construction.result_defined ![v 0, v 2, v 1]

@[simp] lemma eval_qqDisj (v) :
    Semiformula.Evalbm V v qqDisjDef.val ↔ v 0 = qqDisj (v 1) (v 2) := qqDisj_defined.df.iff v

instance qqDisj_definable : 𝚺₁-Function₂ (qqDisj : V → V → V) := Defined.to_definable _ qqDisj_defined

instance qqDisj_definable' (Γ) : Γ-[m + 1]-Function₂ (qqDisj : V → V → V) := .of_sigmaOne qqDisj_definable _ _

end

@[simp]
lemma qqDisj_semiformula {n ps : V} :
    L.Semiformula n (^⋁[n] ps) ↔ (∀ i < len ps, L.Semiformula n ps.[i]) := by
  induction ps using cons_induction_sigma₁
  · definability
  case nil => simp
  case cons p ps ih =>
    simp [ih]
    constructor
    · rintro ⟨hp, hps⟩ i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simpa using hp
      · simpa using hps i (by simpa using hi)
    · intro h
      exact ⟨
        by simpa using h 0 (by simp),
        fun i hi ↦ by simpa using h (i + 1) (by simpa using hi)⟩

end qqDisj

namespace Formalized

section substItr

namespace SubstItr

def blueprint : PR.Blueprint 3 where
  zero := .mkSigma “y n w p | y = 0” (by simp)
  succ := .mkSigma “y ih k n w p | ∃ numeral, !numeralDef numeral k ∧ ∃ v, !consDef v numeral w ∧
    ∃ sp, !(Language.lDef ℒₒᵣ).substsDef sp n v p ∧ !consDef y sp ih” (by simp)

def construction : PR.Construction V blueprint where
  zero _ := 0
  succ param k ih := (⌜ℒₒᵣ⌝.substs (param 0) (numeral k ∷ param 1) (param 2)) ∷ ih
  zero_defined := by intro v; simp [blueprint]
  succ_defined := by intro v; simp [blueprint, (substs_defined ⌜ℒₒᵣ⌝).df.iff]; rfl

end SubstItr

open SubstItr

def substItr (n w p k : V) : V := construction.result ![n, w, p] k

@[simp] lemma substItr_zero (n w p : V) : substItr n w p 0 = 0 := by simp [substItr, construction]

@[simp] lemma substItr_succ (n w p k : V) : substItr n w p (k + 1) = ⌜ℒₒᵣ⌝.substs n (numeral k ∷ w) p ∷ substItr n w p k := by simp [substItr, construction]

section

def _root_.LO.FirstOrder.Arith.substItrDef : 𝚺₁.Semisentence 5 := blueprint.resultDef |>.rew (Rew.substs ![#0, #4, #1, #2, #3])

lemma substItr_defined : 𝚺₁-Function₄ (substItr : V → V → V → V → V) via substItrDef :=
  fun v ↦ by simp [construction.result_defined_iff, substItrDef]; rfl

@[simp] lemma substItr_defined_iff (v) :
    Semiformula.Evalbm V v substItrDef.val ↔ v 0 = substItr (v 1) (v 2) (v 3) (v 4) := substItr_defined.df.iff v

instance substItr_definable : 𝚺₁-Function₄ (substItr : V → V → V → V → V) := Defined.to_definable _ substItr_defined

@[simp, definability] instance substItr_definable' (Γ m) : Γ-[m + 1]-Function₄ (substItr : V → V → V → V → V) :=
  .of_sigmaOne substItr_definable _ _

instance substItr_definable₁ (n w p : V) : 𝚺₁-Function₁ (substItr n w p) := by
  simpa using substItr_definable.retractiont ![&n, &w, &p, #0]

instance substItr_definable₁' (n w p : V) (Γ m) : Γ-[m + 1]-Function₁ (substItr n w p) :=
  .of_sigmaOne (substItr_definable₁ n w p) _ _

end

@[simp] lemma len_substItr (n w p k : V) : len (substItr n w p k) = k := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih => simp [ih]

@[simp] lemma substItr_nth (n w p k : V) {i} (hi : i < k) :
    (substItr n w p k).[i] = ⌜ℒₒᵣ⌝.substs n (numeral (k - (i + 1)) ∷ w) p := by
  induction k using induction_sigma1 generalizing i
  · definability
  case zero => simp at hi
  case succ k ih =>
    simp only [substItr_succ]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using hi)]

lemma neg_conj_substItr {n w p k : V} (hp : ⌜ℒₒᵣ⌝.Semiformula (n + 1) p) (hw : ⌜ℒₒᵣ⌝.SemitermVec n m w) :
    ⌜ℒₒᵣ⌝.neg (^⋀[m] (substItr m w p k)) = ^⋁[m] (substItr m w (⌜ℒₒᵣ⌝.neg p) k) := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih =>
    simp [hw]
    rw [neg_and, ←substs_neg hp, ih]
    · simp [hw]
    · apply Language.Semiformula.substs hp (by simp [hw])
    · simp only [qqConj_semiformula, len_substItr]
      intro i hi
      simp only [gt_iff_lt, hi, substItr_nth]
      apply Language.Semiformula.substs hp (by simp [hw])

lemma neg_disj_substItr {n w p k : V} (hp : ⌜ℒₒᵣ⌝.Semiformula (n + 1) p) (hw : ⌜ℒₒᵣ⌝.SemitermVec n m w) :
    ⌜ℒₒᵣ⌝.neg (^⋁[m] (substItr m w p k)) = ^⋀[m] (substItr m w (⌜ℒₒᵣ⌝.neg p) k) := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih =>
    simp [hw]
    rw [neg_or, ←substs_neg hp, ih]
    · simp [hw]
    · apply Language.Semiformula.substs hp (by simp [hw])
    · simp only [qqDisj_semiformula, len_substItr]
      intro i hi
      simp only [gt_iff_lt, hi, substItr_nth]
      apply Language.Semiformula.substs hp (by simp [hw])

lemma substs_conj_substItr {n m l w p k : V} (hp : ⌜ℒₒᵣ⌝.Semiformula (n + 1) p) (hw : ⌜ℒₒᵣ⌝.SemitermVec n m w) (hv : ⌜ℒₒᵣ⌝.SemitermVec m l v) :
    ⌜ℒₒᵣ⌝.substs l v (^⋀[m] (substItr m w p k)) = ^⋀[l] (substItr l (⌜ℒₒᵣ⌝.termSubstVec n m l v w) p k) := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : ⌜ℒₒᵣ⌝.SemitermVec (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : ⌜ℒₒᵣ⌝.Semiformula m (^⋀[m] substItr m w p k) := by
      simp only [qqConj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.substs (hw.cons (by simp))
    simp only [substItr_succ, qqConj_cons]
    rw [substs_and (hp.substs hkw) ha,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw,
      numeral_substs hv]
    simp [ih]

lemma substs_disj_substItr {n m l w p k : V} (hp : ⌜ℒₒᵣ⌝.Semiformula (n + 1) p) (hw : ⌜ℒₒᵣ⌝.SemitermVec n m w) (hv : ⌜ℒₒᵣ⌝.SemitermVec m l v) :
    ⌜ℒₒᵣ⌝.substs l v (^⋁[m] (substItr m w p k)) = ^⋁[l] (substItr l (⌜ℒₒᵣ⌝.termSubstVec n m l v w) p k) := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : ⌜ℒₒᵣ⌝.SemitermVec (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : ⌜ℒₒᵣ⌝.Semiformula m (^⋁[m] substItr m w p k) := by
      simp only [qqDisj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.substs (hw.cons (by simp))
    simp only [substItr_succ, qqDisj_cons]
    rw [substs_or (hp.substs hkw) ha,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw,
      numeral_substs hv]
    simp [ih]

end substItr

end Formalized

section verums

def qqVerums (n k : V) : V := ^⋀[n] repeatVec (^⊤[n]) k

@[simp] lemma le_qqVerums (n k : V) : k ≤ qqVerums n k := by
  simpa [qqVerums] using len_le_conj n (repeatVec ^⊤[n] k)

section

def _root_.LO.FirstOrder.Arith.qqVerumsDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y n k | ∃ verum, !qqVerumDef verum n ∧ ∃ vs, !repeatVecDef vs verum k ∧ !qqConjDef y n vs” (by simp)

lemma qqVerums_defined : 𝚺₁-Function₂ (qqVerums : V → V → V) via qqVerumsDef :=
  fun v ↦ by simp [qqVerumsDef]; rfl

@[simp] lemma qqVerums_repeatVec (v) :
    Semiformula.Evalbm V v qqVerumsDef.val ↔ v 0 = qqVerums (v 1) (v 2) := qqVerums_defined.df.iff v

instance qqVerums_definable : 𝚺₁-Function₂ (qqVerums : V → V → V) := Defined.to_definable _ qqVerums_defined

@[simp] instance qqVerums_definable' (Γ) : Γ-[m + 1]-Function₂ (qqVerums : V → V → V) :=
  .of_sigmaOne qqVerums_definable _ _

end

end verums

end LO.Arith

end
