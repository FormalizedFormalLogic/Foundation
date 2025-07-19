import Foundation.FirstOrder.Internal.Syntax.Formula.Functions

namespace LO.FirstOrder.Semiformula

variable {L : Language} {ξ : Type*} {n : ℕ}

def replicate (p : Semiformula L ξ n) : ℕ → Semiformula L ξ n
  |     0 => p
  | k + 1 => p ⋏ p.replicate k

lemma replicate_zero (p : Semiformula L ξ n) : p.replicate 0 = p := by simp [replicate]

lemma replicate_succ (p : Semiformula L ξ n) (k : ℕ) : p.replicate (k + 1) = p ⋏ p.replicate k := by simp [replicate]

def weight (k : ℕ) : Semiformula L ξ n := (List.replicate k ⊤).conj

end LO.FirstOrder.Semiformula

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace QQConj

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. !qqVerumDef y”
  cons := .mkSigma “y p ps ih. !qqAndDef y p ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := ^⊤
  cons _ p _ ih := p ^⋏ ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]

end QQConj

section qqConj

open QQConj

noncomputable def qqConj (ps : V) : V := construction.result ![] ps

def qqConjGraph : 𝚺₁.Semisentence 2 := blueprint.resultDef

scoped notation:65 "^⋀ " ps:66 => qqConj ps

@[simp] lemma qqConj_nil : ^⋀ (0 : V) = ^⊤ := by simp [qqConj, construction]

@[simp] lemma qqConj_cons (p ps : V) : ^⋀ (p ∷ ps) = p ^⋏ (^⋀ ps) := by simp [qqConj, construction]

section

lemma qqConj.defined : 𝚺₁-Function₁[V] qqConj via qqConjGraph := construction.result_defined

@[simp] lemma qqConj.eval (v) :
    Semiformula.Evalbm V v qqConjGraph.val ↔ v 0 = qqConj (v 1) := qqConj.defined.df.iff v

instance qqConj.definable : 𝚺₁-Function₁ (qqConj : V → V) := qqConj.defined.to_definable

instance qqConj.definable' : Γ-[m + 1]-Function₁ (qqConj : V → V) := .of_sigmaOne qqConj.definable

end

@[simp]
lemma qqConj_semiformula {n ps : V} :
    IsSemiformula L n (^⋀ ps) ↔ (∀ i < len ps, IsSemiformula L n ps.[i]) := by
  induction ps using cons_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case cons p ps ih =>
    simp only [qqConj_cons, IsSemiformula.and, ih, len_cons]
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
  induction ps using cons_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp [qqVerum]
  case cons p ps ih =>
    simp only [len_cons, qqConj_cons, succ_le_iff_lt]
    exact lt_of_le_of_lt ih (by simp)

end qqConj

namespace QQDisj

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. !qqFalsumDef y”
  cons := .mkSigma “y p ps ih. !qqOrDef y p ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := ^⊥
  cons _ p _ ih := p ^⋎ ih
  nil_defined := by intro v; simp [blueprint]
  cons_defined := by intro v; simp [blueprint]

end QQDisj

section qqDisj

open QQDisj

noncomputable def qqDisj (ps : V) : V := construction.result ![] ps

def qqDisjGraph : 𝚺₁.Semisentence 2 := blueprint.resultDef

scoped notation:65 "^⋁ " ps:66 => qqDisj ps

@[simp] lemma qqDisj_nil : ^⋁ (0 : V) = ^⊥ := by simp [qqDisj, construction]

@[simp] lemma qqDisj_cons (p ps : V) : ^⋁ (p ∷ ps) = p ^⋎ (^⋁ ps) := by simp [qqDisj, construction]

section

lemma qqDisj.defined : 𝚺₁-Function₁[V] qqDisj via qqDisjGraph := construction.result_defined

@[simp] lemma qqDisj.eval (v) :
    Semiformula.Evalbm V v qqDisjGraph.val ↔ v 0 = qqDisj (v 1) := qqDisj.defined.df.iff v

instance qqDisj.definable : 𝚺₁-Function₁[V] qqDisj := qqDisj.defined.to_definable

instance qqDisj.definable'  : Γ-[m + 1]-Function₁[V] qqDisj := .of_sigmaOne qqDisj.definable

end

@[simp]
lemma qqDisj_semiformula {ps : V} :
    IsSemiformula L n (^⋁ ps) ↔ (∀ i < len ps, IsSemiformula L n ps.[i]) := by
  induction ps using cons_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case cons p ps ih =>
    simp only [qqDisj_cons, IsSemiformula.or, ih, len_cons]
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

namespace InternalArithmetic

/-! ### Disjunction of sequential substution

`disjSeqSubst w p k = substs (k ∷ w) p ^⋎ ⋯ ^⋎ substs (0 ∷ w) p ^⋎ ⊥`

 -/

-- TOFO: remove
section disjSeqSubst

namespace DisjSeqSubst

def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y w p. !qqFalsumDef y”
  succ := .mkSigma “y ih k w p. ∃ numeral, !numeralGraph numeral k ∧ ∃ v, !consDef v numeral w ∧
    ∃ q, !(substsGraph ℒₒᵣ) q v p ∧ !qqOrDef y q ih”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := ^⊥
  succ param k ih := (substs ℒₒᵣ (numeral k ∷ param 0) (param 1)) ^⋎ ih
  zero_defined := by intro v; simp [blueprint]
  succ_defined := by intro v; simp [blueprint, substs.defined.df.iff]

end DisjSeqSubst

open DisjSeqSubst

noncomputable def disjSeqSubst (w p k : V) : V := construction.result ![w, p] k

@[simp] lemma disjSeqSubst_zero (w p : V) : disjSeqSubst w p 0 = ^⊥ := by simp [disjSeqSubst, construction]

@[simp] lemma disjSeqSubst_succ (w p k : V) :
    disjSeqSubst w p (k + 1) = substs ℒₒᵣ (numeral k ∷ w) p ^⋎ disjSeqSubst w p k := by simp [disjSeqSubst, construction]

def disjSeqSubstGraph : 𝚺₁.Semisentence 4 := blueprint.resultDef |>.rew (Rew.substs ![#0, #3, #1, #2])

section

lemma disjSeqSubst.defined : 𝚺₁-Function₃[V] disjSeqSubst via disjSeqSubstGraph :=
  fun v ↦ by simp [construction.result_defined_iff, disjSeqSubstGraph, disjSeqSubst, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

@[simp] lemma disjSeqSubst.eval (v) :
    Semiformula.Evalbm V v disjSeqSubstGraph.val ↔ v 0 = disjSeqSubst (v 1) (v 2) (v 3) := disjSeqSubst.defined.df.iff v

instance disjSeqSubst.definable : 𝚺₁-Function₃[V] disjSeqSubst := disjSeqSubst.defined.to_definable

instance disjSeqSubst.definable' : Γ-[m + 1]-Function₃[V] disjSeqSubst := .of_sigmaOne disjSeqSubst.definable

end

lemma _root_.LO.ISigma1.Metamath.IsSemiformula.disjSeqSubst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hp : IsSemiformula ℒₒᵣ (n + 1) p) (k : V) :
    IsSemiformula ℒₒᵣ m (disjSeqSubst w p k) := by
  induction k using sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    simpa [ih] using hp.substs <| hw.cons (numeral_semiterm m k)

lemma substs_conj_disjSeqSubst {n m l v w p : V}
    (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (hv : IsSemitermVec ℒₒᵣ m l v) (k : V) :
    substs ℒₒᵣ v (disjSeqSubst w p k) = disjSeqSubst (termSubstVec ℒₒᵣ n v w) p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : IsSemitermVec ℒₒᵣ (n + 1) m (numeral k ∷ w) := hw.cons (numeral_semiterm m k)
    have ha : IsSemiformula ℒₒᵣ m (disjSeqSubst w p k) := hp.disjSeqSubst hw k
    rw [disjSeqSubst_succ,
      substs_or (hp.substs hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm,
      numeral_substs hv]
    simp [ih]

end disjSeqSubst

section substItr

namespace SubstItr

def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y w p. y = 0”
  succ := .mkSigma “y ih k w p. ∃ numeral, !numeralGraph numeral k ∧ ∃ v, !consDef v numeral w ∧
    ∃ sp, !(substsGraph ℒₒᵣ) sp v p ∧ !consDef y sp ih”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ param k ih := (substs ℒₒᵣ (numeral k ∷ param 0) (param 1)) ∷ ih
  zero_defined := by intro v; simp [blueprint]
  succ_defined := by intro v; simp [blueprint, substs.defined.df.iff]

end SubstItr

open SubstItr

noncomputable def substItr (w p k : V) : V := construction.result ![w, p] k

@[simp] lemma substItr_zero (w p : V) : substItr w p 0 = 0 := by simp [substItr, construction]

@[simp] lemma substItr_succ (w p k : V) : substItr w p (k + 1) = substs ℒₒᵣ (numeral k ∷ w) p ∷ substItr w p k := by simp [substItr, construction]

section

def substItrGraph : 𝚺₁.Semisentence 4 := blueprint.resultDef |>.rew (Rew.substs ![#0, #3, #1, #2])

lemma substItr.defined : 𝚺₁-Function₃ (substItr : V → V → V → V) via substItrGraph :=
  fun v ↦ by simp [construction.result_defined_iff, substItrGraph, substItr, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

@[simp] lemma substItr.eval (v) :
    Semiformula.Evalbm V v substItrGraph.val ↔ v 0 = substItr (v 1) (v 2) (v 3) := substItr.defined.df.iff v

instance substItr.definable : 𝚺₁-Function₃ (substItr : V → V → V → V) := substItr.defined.to_definable

instance substItr.definable' : Γ-[m + 1]-Function₃ (substItr : V → V → V → V) := .of_sigmaOne substItr.definable

end

@[simp] lemma len_substItr (w p k : V) : len (substItr w p k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

@[simp] lemma substItr_nth (w p k : V) {i} (hi : i < k) :
    (substItr w p k).[i] = substs ℒₒᵣ (numeral (k - (i + 1)) ∷ w) p := by
  induction k using ISigma1.sigma1_succ_induction generalizing i
  · definability
  case zero => simp at hi
  case succ k ih =>
    simp only [substItr_succ]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using hi)]

lemma _root_.LO.ISigma1.Metamath.IsSemiformula.substItrConj
    {m n w p : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (k : V) :
    IsSemiformula ℒₒᵣ m (^⋀ substItr w p k) := by
  simp only [qqConj_semiformula, len_substItr]
  intro i hi
  simp only [hi, substItr_nth]
  apply hp.substs (by simp [hw])

lemma _root_.LO.ISigma1.Metamath.IsSemiformula.substItrDisj
    {m n w p : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (k : V) :
    IsSemiformula ℒₒᵣ m (^⋁ substItr w p k) := by
  simp only [qqDisj_semiformula, len_substItr]
  intro i hi
  simp only [hi, substItr_nth]
  apply hp.substs (by simp [hw])

lemma neg_conj_substItr {n w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) :
    neg ℒₒᵣ (^⋀ (substItr w p k)) = ^⋁ (substItr w (neg ℒₒᵣ p) k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqConj_cons, qqDisj_cons]
    rw [neg_and (L := ℒₒᵣ), ←substs_neg hp (m := m), ih]
    · simp [hw]
    · exact IsSemiformula.isUFormula <| hp.substs (by simpa [hw])
    · exact IsSemiformula.isUFormula <| hp.substItrConj hw k

lemma neg_disj_substItr {n w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) :
    neg ℒₒᵣ (^⋁ (substItr w p k)) = ^⋀ (substItr w (neg ℒₒᵣ p) k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqDisj_cons, qqConj_cons]
    rw [neg_or (L := ℒₒᵣ), ←substs_neg hp (m := m), ih]
    · simp [hw]
    · apply IsSemiformula.isUFormula <| hp.substs (by simpa [hw])
    · apply IsSemiformula.isUFormula <| hp.substItrDisj hw k

lemma shift_conj_substItr {n w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) :
    shift ℒₒᵣ (^⋀ (substItr w p k)) = ^⋀ (substItr (termShiftVec ℒₒᵣ n w) (shift ℒₒᵣ p) k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqConj_cons]
    rw [shift_and (L := ℒₒᵣ), shift_substs hp (m := m), ih, termShiftVec_cons (L := ℒₒᵣ), numeral_shift]
    · simp
    · exact hw.isUTerm
    · exact hw.cons (numeral_semiterm m k)
    · exact IsSemiformula.isUFormula <| hp.substs (by simpa [hw])
    · exact IsSemiformula.isUFormula <| hp.substItrConj hw k

lemma shift_disj_substItr {n w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) :
    shift ℒₒᵣ (^⋁ (substItr w p k)) = ^⋁ (substItr (termShiftVec ℒₒᵣ n w) (shift ℒₒᵣ p) k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqDisj_cons]
    rw [shift_or (L := ℒₒᵣ), shift_substs hp (m := m), ih, termShiftVec_cons (L := ℒₒᵣ), numeral_shift]
    · simp
    · exact hw.isUTerm
    · exact hw.cons (numeral_semiterm m k)
    · exact IsSemiformula.isUFormula <| hp.substs (by simpa [hw])
    · exact IsSemiformula.isUFormula <| hp.substItrDisj hw k

lemma substs_conj_substItr {n m l w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (hv : IsSemitermVec ℒₒᵣ m l v) :
    substs ℒₒᵣ v (^⋀ (substItr w p k)) = ^⋀ (substItr (termSubstVec ℒₒᵣ n v w) p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : IsSemitermVec ℒₒᵣ (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : IsSemiformula ℒₒᵣ m (^⋀ substItr w p k) := by
      simp only [qqConj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.substs (hw.cons (by simp))
    simp only [substItr_succ, qqConj_cons]
    rw [substs_and (hp.substs hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm,
      numeral_substs hv]
    simp [ih]

lemma substs_disj_substItr {n m l w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (hv : IsSemitermVec ℒₒᵣ m l v) :
    substs ℒₒᵣ v (^⋁ (substItr w p k)) = ^⋁ (substItr (termSubstVec ℒₒᵣ n v w) p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : IsSemitermVec ℒₒᵣ (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : IsSemiformula ℒₒᵣ m (^⋁ substItr w p k) := by
      simp only [qqDisj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.substs (hw.cons (by simp))
    simp only [substItr_succ, qqDisj_cons]
    rw [substs_or (hp.substs hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm,
      numeral_substs hv]
    simp [ih]

end substItr

end InternalArithmetic

section verums

noncomputable def qqVerums (k : V) : V := ^⋀ repeatVec ^⊤ k

def qqVerumsGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y k. ∃ verum, !qqVerumDef verum ∧ ∃ vs, !repeatVecDef vs verum k ∧ !qqConjGraph y vs”

@[simp] lemma le_qqVerums (k : V) : k ≤ qqVerums k := by
  simpa [qqVerums] using len_le_conj (repeatVec ^⊤ k)

section

lemma qqVerums.defined : 𝚺₁-Function₁[V] qqVerums via qqVerumsGraph :=
  fun v ↦ by simp [qqVerumsGraph]; rfl

@[simp] lemma qqVerums.repeatVec (v) :
    Semiformula.Evalbm V v qqVerumsGraph.val ↔ v 0 = qqVerums (v 1) := qqVerums.defined.df.iff v

instance qqVerums.definable : 𝚺₁-Function₁[V] qqVerums := qqVerums.defined.to_definable

instance qqVerums.definable' : Γ-[m + 1]-Function₁[V] qqVerums := .of_sigmaOne qqVerums.definable

end

@[simp] protected lemma IsSemiformula.qqVerums (k : V) : IsSemiformula L n (qqVerums k) := by
  simp only [qqVerums, qqConj_semiformula, len_repeatVec]
  intro i hi; simp [nth_repeatVec _ _ hi]

@[simp] lemma qqVerums_zero : qqVerums (0 : V) = ^⊤ := by simp [qqVerums]

@[simp] lemma qqVerums_succ (k : V) : qqVerums (k + 1) = ^⊤ ^⋏ qqVerums k := by simp [qqVerums]

end verums

end LO.ISigma1.Metamath
