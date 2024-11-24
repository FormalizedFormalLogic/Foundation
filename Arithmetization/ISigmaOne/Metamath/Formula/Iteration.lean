import Arithmetization.ISigmaOne.Metamath.Formula.Functions

namespace LO.FirstOrder.Semiformula

variable {L : Language} {ξ : Type*} {n : ℕ}

def replicate (p : Semiformula L ξ n) : ℕ → Semiformula L ξ n
  | 0     => p
  | k + 1 => p ⋏ p.replicate k

lemma replicate_zero (p : Semiformula L ξ n) : p.replicate 0 = p := by simp [replicate]

lemma replicate_succ (p : Semiformula L ξ n) (k : ℕ) : p.replicate (k + 1) = p ⋏ p.replicate k := by simp [replicate]

def weight (k : ℕ) : Semiformula L ξ n := (List.replicate k ⊤).conj

end LO.FirstOrder.Semiformula

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace QQConj

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. !qqVerumDef y” (by simp)
  cons := .mkSigma “y p ps ih. !qqAndDef y p ih” (by simp)

def construction : VecRec.Construction V blueprint where
  nil _ := ^⊤
  cons _ p _ ih := p ^⋏ ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]

end QQConj

section qqConj

open QQConj

def qqConj (ps : V) : V := construction.result ![] ps

scoped notation:65 "^⋀ " ps:66 => qqConj ps

@[simp] lemma qqConj_nil : ^⋀ (0 : V) = ^⊤ := by simp [qqConj, construction]

@[simp] lemma qqConj_cons (p ps : V) : ^⋀ (p ∷ ps) = p ^⋏ (^⋀ ps) := by simp [qqConj, construction]

section

def _root_.LO.FirstOrder.Arith.qqConjDef : 𝚺₁.Semisentence 2 := blueprint.resultDef

lemma qqConj_defined : 𝚺₁-Function₁ (qqConj : V → V) via qqConjDef := construction.result_defined

@[simp] lemma eval_qqConj (v) :
    Semiformula.Evalbm V v qqConjDef.val ↔ v 0 = qqConj (v 1) := qqConj_defined.df.iff v

instance qqConj_definable : 𝚺₁-Function₁ (qqConj : V → V) := qqConj_defined.to_definable

instance qqConj_definable' : Γ-[m + 1]-Function₁ (qqConj : V → V) := .of_sigmaOne qqConj_definable

end

@[simp]
lemma qqConj_semiformula {n ps : V} :
    L.IsSemiformula n (^⋀ ps) ↔ (∀ i < len ps, L.IsSemiformula n ps.[i]) := by
  induction ps using cons_induction_sigma1
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

@[simp] lemma len_le_conj (ps : V) : len ps ≤ ^⋀ ps := by
  induction ps using cons_induction_sigma1
  · definability
  case nil => simp [qqVerum]
  case cons p ps ih =>
    simp only [len_cons, qqConj_cons, succ_le_iff_lt]
    exact lt_of_le_of_lt ih (by simp)

end qqConj

namespace QQDisj

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. !qqFalsumDef y” (by simp)
  cons := .mkSigma “y p ps ih. !qqOrDef y p ih” (by simp)

def construction : VecRec.Construction V blueprint where
  nil _ := ^⊥
  cons _ p _ ih := p ^⋎ ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]

end QQDisj

section qqDisj

open QQDisj

def qqDisj (ps : V) : V := construction.result ![] ps

scoped notation:65 "^⋁ " ps:66 => qqDisj ps

@[simp] lemma qqDisj_nil : ^⋁ (0 : V) = ^⊥ := by simp [qqDisj, construction]

@[simp] lemma qqDisj_cons (p ps : V) : ^⋁ (p ∷ ps) = p ^⋎ (^⋁ ps) := by simp [qqDisj, construction]

section

def _root_.LO.FirstOrder.Arith.qqDisjDef : 𝚺₁.Semisentence 2 := blueprint.resultDef

lemma qqDisj_defined : 𝚺₁-Function₁ (qqDisj : V → V) via qqDisjDef := construction.result_defined

@[simp] lemma eval_qqDisj (v) :
    Semiformula.Evalbm V v qqDisjDef.val ↔ v 0 = qqDisj (v 1) := qqDisj_defined.df.iff v

instance qqDisj_definable : 𝚺₁-Function₁ (qqDisj : V → V) := qqDisj_defined.to_definable

instance qqDisj_definable' (Γ) : Γ-[m + 1]-Function₁ (qqDisj : V → V) := .of_sigmaOne qqDisj_definable

end

@[simp]
lemma qqDisj_semiformula {ps : V} :
    L.IsSemiformula n (^⋁ ps) ↔ (∀ i < len ps, L.IsSemiformula n ps.[i]) := by
  induction ps using cons_induction_sigma1
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

def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y w p. y = 0” (by simp)
  succ := .mkSigma “y ih k w p. ∃ numeral, !numeralDef numeral k ∧ ∃ v, !consDef v numeral w ∧
    ∃ sp, !(Language.lDef ℒₒᵣ).substsDef sp v p ∧ !consDef y sp ih” (by simp)

def construction : PR.Construction V blueprint where
  zero _ := 0
  succ param k ih := (⌜ℒₒᵣ⌝.substs (numeral k ∷ param 0) (param 1)) ∷ ih
  zero_defined := by intro v; simp [blueprint]
  succ_defined := by intro v; simp [blueprint, ⌜ℒₒᵣ⌝.substs_defined.df.iff]; rfl

end SubstItr

open SubstItr

def substItr (w p k : V) : V := construction.result ![w, p] k

@[simp] lemma substItr_zero (w p : V) : substItr w p 0 = 0 := by simp [substItr, construction]

@[simp] lemma substItr_succ (w p k : V) : substItr w p (k + 1) = ⌜ℒₒᵣ⌝.substs (numeral k ∷ w) p ∷ substItr w p k := by simp [substItr, construction]

section

def _root_.LO.FirstOrder.Arith.substItrDef : 𝚺₁.Semisentence 4 := blueprint.resultDef |>.rew (Rew.substs ![#0, #3, #1, #2])

lemma substItr_defined : 𝚺₁-Function₃ (substItr : V → V → V → V) via substItrDef :=
  fun v ↦ by simp [construction.result_defined_iff, substItrDef, substItr]

@[simp] lemma substItr_defined_iff (v) :
    Semiformula.Evalbm V v substItrDef.val ↔ v 0 = substItr (v 1) (v 2) (v 3) := substItr_defined.df.iff v

instance substItr_definable : 𝚺₁-Function₃ (substItr : V → V → V → V) := substItr_defined.to_definable

instance substItr_definable' : Γ-[m + 1]-Function₃ (substItr : V → V → V → V) := .of_sigmaOne substItr_definable

end

@[simp] lemma len_substItr (w p k : V) : len (substItr w p k) = k := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih => simp [ih]

@[simp] lemma substItr_nth (w p k : V) {i} (hi : i < k) :
    (substItr w p k).[i] = ⌜ℒₒᵣ⌝.substs (numeral (k - (i + 1)) ∷ w) p := by
  induction k using induction_sigma1 generalizing i
  · definability
  case zero => simp at hi
  case succ k ih =>
    simp only [substItr_succ]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using hi)]

lemma neg_conj_substItr {n w p k : V} (hp : ⌜ℒₒᵣ⌝.IsSemiformula (n + 1) p) (hw : ⌜ℒₒᵣ⌝.IsSemitermVec n m w) :
    ⌜ℒₒᵣ⌝.neg (^⋀ (substItr w p k)) = ^⋁ (substItr w (⌜ℒₒᵣ⌝.neg p) k) := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih =>
    simp [hw]
    rw [neg_and, ←substs_neg hp (m := m), ih]
    · simp [hw]
    · exact Language.IsSemiformula.isUFormula <| hp.substs (by simpa [hw])
    · apply Language.IsSemiformula.isUFormula
      simp only [qqConj_semiformula, len_substItr]
      intro i hi
      simp only [gt_iff_lt, hi, substItr_nth]
      apply hp.substs (by simpa [hw])

lemma neg_disj_substItr {n w p k : V} (hp : ⌜ℒₒᵣ⌝.IsSemiformula (n + 1) p) (hw : ⌜ℒₒᵣ⌝.IsSemitermVec n m w) :
    ⌜ℒₒᵣ⌝.neg (^⋁ (substItr w p k)) = ^⋀ (substItr w (⌜ℒₒᵣ⌝.neg p) k) := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih =>
    simp [hw]
    rw [neg_or, ←substs_neg hp (m := m), ih]
    · simp [hw]
    · apply Language.IsSemiformula.isUFormula <| hp.substs (by simpa [hw])
    · apply Language.IsSemiformula.isUFormula
      simp only [qqDisj_semiformula, len_substItr]
      intro i hi
      simp only [gt_iff_lt, hi, substItr_nth]
      apply hp.substs (by simpa [hw])

lemma substs_conj_substItr {n m l w p k : V} (hp : ⌜ℒₒᵣ⌝.IsSemiformula (n + 1) p) (hw : ⌜ℒₒᵣ⌝.IsSemitermVec n m w) (hv : ⌜ℒₒᵣ⌝.IsSemitermVec m l v) :
    ⌜ℒₒᵣ⌝.substs v (^⋀ (substItr w p k)) = ^⋀ (substItr (⌜ℒₒᵣ⌝.termSubstVec n v w) p k) := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : ⌜ℒₒᵣ⌝.IsSemitermVec (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : ⌜ℒₒᵣ⌝.IsSemiformula m (^⋀ substItr w p k) := by
      simp only [qqConj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.substs (hw.cons (by simp))
    simp only [substItr_succ, qqConj_cons]
    rw [substs_and (hp.substs hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm,
      numeral_substs hv]
    simp [ih]

lemma substs_disj_substItr {n m l w p k : V} (hp : ⌜ℒₒᵣ⌝.IsSemiformula (n + 1) p) (hw : ⌜ℒₒᵣ⌝.IsSemitermVec n m w) (hv : ⌜ℒₒᵣ⌝.IsSemitermVec m l v) :
    ⌜ℒₒᵣ⌝.substs v (^⋁ (substItr w p k)) = ^⋁ (substItr (⌜ℒₒᵣ⌝.termSubstVec n v w) p k) := by
  induction k using induction_sigma1
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : ⌜ℒₒᵣ⌝.IsSemitermVec (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : ⌜ℒₒᵣ⌝.IsSemiformula m (^⋁ substItr w p k) := by
      simp only [qqDisj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.substs (hw.cons (by simp))
    simp only [substItr_succ, qqDisj_cons]
    rw [substs_or (hp.substs hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm,
      numeral_substs hv]
    simp [ih]

end substItr

end Formalized

section verums

def qqVerums (k : V) : V := ^⋀ repeatVec ^⊤ k

@[simp] lemma le_qqVerums (k : V) : k ≤ qqVerums k := by
  simpa [qqVerums] using len_le_conj (repeatVec ^⊤ k)

section

def _root_.LO.FirstOrder.Arith.qqVerumsDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y k. ∃ verum, !qqVerumDef verum ∧ ∃ vs, !repeatVecDef vs verum k ∧ !qqConjDef y vs” (by simp)

lemma qqVerums_defined : 𝚺₁-Function₁ (qqVerums : V → V) via qqVerumsDef :=
  fun v ↦ by simp [qqVerumsDef]; rfl

@[simp] lemma qqVerums_repeatVec (v) :
    Semiformula.Evalbm V v qqVerumsDef.val ↔ v 0 = qqVerums (v 1) := qqVerums_defined.df.iff v

instance qqVerums_definable : 𝚺₁-Function₁ (qqVerums : V → V) := qqVerums_defined.to_definable

instance qqVerums_definable' : Γ-[m + 1]-Function₁ (qqVerums : V → V) := .of_sigmaOne qqVerums_definable

end

@[simp] protected lemma Language.IsSemiformula.qqVerums (k : V) : L.IsSemiformula n (qqVerums k) := by
  simp [qqVerums]
  intro i hi; simp [nth_repeatVec _ _ hi]

@[simp] lemma qqVerums_zero : qqVerums (0 : V) = ^⊤ := by simp [qqVerums]

@[simp] lemma qqVerums_succ (k : V) : qqVerums (k + 1) = ^⊤ ^⋏ qqVerums k := by simp [qqVerums]

end verums

end LO.Arith

end
