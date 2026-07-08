module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Functions

@[expose] public section
namespace LO.FirstOrder.Semiformula

variable {L : Language} {ξ : Type*} {n : ℕ}

def replicate (p : Semiformula L ξ n) : ℕ → Semiformula L ξ n
  |     0 => p
  | k + 1 => p ⋏ p.replicate k

lemma replicate_zero (p : Semiformula L ξ n) : p.replicate 0 = p := by simp [replicate]

lemma replicate_succ (p : Semiformula L ξ n) (k : ℕ) : p.replicate (k + 1) = p ⋏ p.replicate k := by simp [replicate]

def weight (k : ℕ) : Semiformula L ξ n := (List.replicate k ⊤).conj

end LO.FirstOrder.Semiformula

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace QQConj

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. !qqVerumDef y”
  adjoin := .mkSigma “y p ps ih. !qqAndDef y p ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := ^⊤
  adjoin _ p _ ih := p ^⋏ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end QQConj

section qqConj

open QQConj

noncomputable def qqConj (ps : V) : V := construction.result ![] ps

def qqConjGraph : 𝚺₁.Semisentence 2 := blueprint.resultDef

scoped notation:65 "^⋀ " ps:66 => qqConj ps

@[simp] lemma qqConj_nil : ^⋀ (0 : V) = ^⊤ := by simp [qqConj, construction]

@[simp] lemma qqConj_cons (p ps : V) : ^⋀ (p ∷ ps) = p ^⋏ (^⋀ ps) := by simp [qqConj, construction]

section

instance qqConj.defined : 𝚺₁-Function₁[V] qqConj via qqConjGraph := construction.result_defined

instance qqConj.definable : 𝚺₁-Function₁ (qqConj : V → V) := qqConj.defined.to_definable

instance qqConj.definable' : Γ-[m + 1]-Function₁ (qqConj : V → V) := .of_sigmaOne qqConj.definable

end

@[simp]
lemma qqConj_semiformula {n ps : V} :
    IsSemiformula L n (^⋀ ps) ↔ (∀ i < len ps, IsSemiformula L n ps.[i]) := by
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin p ps ih =>
    simp only [qqConj_cons, IsSemiformula.and, ih, len_adjoin]
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
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp [qqVerum]
  case adjoin p ps ih =>
    simp only [len_adjoin, qqConj_cons, succ_le_iff_lt]
    exact lt_of_le_of_lt ih (by simp)

end qqConj

namespace QQDisj

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. !qqFalsumDef y”
  adjoin := .mkSigma “y p ps ih. !qqOrDef y p ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := ^⊥
  adjoin _ p _ ih := p ^⋎ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end QQDisj

section qqDisj

open QQDisj

noncomputable def qqDisj (ps : V) : V := construction.result ![] ps

def qqDisjGraph : 𝚺₁.Semisentence 2 := blueprint.resultDef

scoped notation:65 "^⋁ " ps:66 => qqDisj ps

@[simp] lemma qqDisj_nil : ^⋁ (0 : V) = ^⊥ := by simp [qqDisj, construction]

@[simp] lemma qqDisj_cons (p ps : V) : ^⋁ (p ∷ ps) = p ^⋎ (^⋁ ps) := by simp [qqDisj, construction]

section

instance qqDisj.defined : 𝚺₁-Function₁[V] qqDisj via qqDisjGraph := construction.result_defined

instance qqDisj.definable : 𝚺₁-Function₁[V] qqDisj := qqDisj.defined.to_definable

instance qqDisj.definable'  : Γ-[m + 1]-Function₁[V] qqDisj := .of_sigmaOne qqDisj.definable

end

@[simp]
lemma qqDisj_semiformula {ps : V} :
    IsSemiformula L n (^⋁ ps) ↔ (∀ i < len ps, IsSemiformula L n ps.[i]) := by
  induction ps using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin p ps ih =>
    simp only [qqDisj_cons, IsSemiformula.or, ih, len_adjoin]
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

namespace Arithmetic

/-! ### Disjunction of sequential substution

`disjSeqSubst w p k = subst (k ∷ w) p ^⋎ ⋯ ^⋎ subst (0 ∷ w) p ^⋎ ⊥`

 -/

-- TOFO: remove
section disjSeqSubst

namespace DisjSeqSubst

noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y w p. !qqFalsumDef y”
  succ := .mkSigma “y ih k w p. ∃ numeral, !numeralGraph numeral k ∧ ∃ v, !adjoinDef v numeral w ∧
    ∃ q, !(substsGraph ℒₒᵣ) q v p ∧ !qqOrDef y q ih”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := ^⊥
  succ param k ih := (subst ℒₒᵣ (numeral k ∷ param 0) (param 1)) ^⋎ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end DisjSeqSubst

open DisjSeqSubst

noncomputable def disjSeqSubst (w p k : V) : V := construction.result ![w, p] k

@[simp] lemma disjSeqSubst_zero (w p : V) : disjSeqSubst w p 0 = ^⊥ := by simp [disjSeqSubst, construction]

@[simp] lemma disjSeqSubst_succ (w p k : V) :
    disjSeqSubst w p (k + 1) = subst ℒₒᵣ (numeral k ∷ w) p ^⋎ disjSeqSubst w p k := by simp [disjSeqSubst, construction]

noncomputable def disjSeqSubstGraph : 𝚺₁.Semisentence 4 := blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

section

instance disjSeqSubst.defined : 𝚺₁-Function₃[V] disjSeqSubst via disjSeqSubstGraph := .mk fun v ↦ by
  simp [construction.result_defined_iff, disjSeqSubstGraph, disjSeqSubst, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

instance disjSeqSubst.definable : 𝚺₁-Function₃[V] disjSeqSubst := disjSeqSubst.defined.to_definable

instance disjSeqSubst.definable' : Γ-[m + 1]-Function₃[V] disjSeqSubst := .of_sigmaOne disjSeqSubst.definable

end

lemma _root_.LO.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula.disjSeqSubst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hp : IsSemiformula ℒₒᵣ (n + 1) p) (k : V) :
    IsSemiformula ℒₒᵣ m (disjSeqSubst w p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    simpa [ih] using hp.subst <| hw.adjoin (numeral_semiterm m k)

lemma substs_conj_disjSeqSubst {n m l v w p : V}
    (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (hv : IsSemitermVec ℒₒᵣ m l v) (k : V) :
    subst ℒₒᵣ v (disjSeqSubst w p k) = disjSeqSubst (termSubstVec ℒₒᵣ n v w) p k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : IsSemitermVec ℒₒᵣ (n + 1) m (numeral k ∷ w) := hw.adjoin (numeral_semiterm m k)
    have ha : IsSemiformula ℒₒᵣ m (disjSeqSubst w p k) := hp.disjSeqSubst hw k
    rw [disjSeqSubst_succ,
      substs_or (hp.subst hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm,
      numeral_substs hv]
    simp [ih]

end disjSeqSubst

section substItr

namespace SubstItr

noncomputable def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “y w p. y = 0”
  succ := .mkSigma “y ih k w p. ∃ numeral, !numeralGraph numeral k ∧ ∃ v, !adjoinDef v numeral w ∧
    ∃ sp, !(substsGraph ℒₒᵣ) sp v p ∧ !adjoinDef y sp ih”

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ param k ih := (subst ℒₒᵣ (numeral k ∷ param 0) (param 1)) ∷ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]

end SubstItr

open SubstItr

noncomputable def substItr (w p k : V) : V := construction.result ![w, p] k

@[simp] lemma substItr_zero (w p : V) : substItr w p 0 = 0 := by simp [substItr, construction]

@[simp] lemma substItr_succ (w p k : V) : substItr w p (k + 1) = subst ℒₒᵣ (numeral k ∷ w) p ∷ substItr w p k := by simp [substItr, construction]

section

noncomputable def substItrGraph : 𝚺₁.Semisentence 4 := blueprint.resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance substItr.defined : 𝚺₁-Function₃[V] substItr via substItrGraph := .mk fun v ↦ by
  simp [construction.result_defined_iff, substItrGraph, substItr, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

instance substItr.definable : 𝚺₁-Function₃ (substItr : V → V → V → V) := substItr.defined.to_definable

instance substItr.definable' : Γ-[m + 1]-Function₃ (substItr : V → V → V → V) := .of_sigmaOne substItr.definable

end

@[simp] lemma len_substItr (w p k : V) : len (substItr w p k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]

@[simp] lemma substItr_nth (w p k : V) {i} (hi : i < k) :
    (substItr w p k).[i] = subst ℒₒᵣ (numeral (k - (i + 1)) ∷ w) p := by
  induction k using ISigma1.sigma1_succ_induction generalizing i
  · definability
  case zero => simp at hi
  case succ k ih =>
    simp only [substItr_succ]
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using hi)]

lemma _root_.LO.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula.substItrConj
    {m n w p : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (k : V) :
    IsSemiformula ℒₒᵣ m (^⋀ substItr w p k) := by
  simp only [qqConj_semiformula, len_substItr]
  intro i hi
  simp only [hi, substItr_nth]
  apply hp.subst (by simp [hw])

lemma _root_.LO.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula.substItrDisj
    {m n w p : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (k : V) :
    IsSemiformula ℒₒᵣ m (^⋁ substItr w p k) := by
  simp only [qqDisj_semiformula, len_substItr]
  intro i hi
  simp only [hi, substItr_nth]
  apply hp.subst (by simp [hw])

lemma neg_conj_substItr {n w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) :
    neg ℒₒᵣ (^⋀ (substItr w p k)) = ^⋁ (substItr w (neg ℒₒᵣ p) k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    simp only [substItr_succ, qqConj_cons, qqDisj_cons]
    rw [neg_and (L := ℒₒᵣ), ←substs_neg hp (m := m), ih]
    · simp [hw]
    · exact IsSemiformula.isUFormula <| hp.subst (by simpa [hw])
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
    · apply IsSemiformula.isUFormula <| hp.subst (by simpa [hw])
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
    · exact hw.adjoin (numeral_semiterm m k)
    · exact IsSemiformula.isUFormula <| hp.subst (by simpa [hw])
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
    · exact hw.adjoin (numeral_semiterm m k)
    · exact IsSemiformula.isUFormula <| hp.subst (by simpa [hw])
    · exact IsSemiformula.isUFormula <| hp.substItrDisj hw k

lemma substs_conj_substItr {n m l w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (hv : IsSemitermVec ℒₒᵣ m l v) :
    subst ℒₒᵣ v (^⋀ (substItr w p k)) = ^⋀ (substItr (termSubstVec ℒₒᵣ n v w) p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : IsSemitermVec ℒₒᵣ (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : IsSemiformula ℒₒᵣ m (^⋀ substItr w p k) := by
      simp only [qqConj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.subst (hw.adjoin (by simp))
    simp only [substItr_succ, qqConj_cons]
    rw [substs_and (hp.subst hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm,
      numeral_substs hv]
    simp [ih]

lemma substs_disj_substItr {n m l w p k : V} (hp : IsSemiformula ℒₒᵣ (n + 1) p) (hw : IsSemitermVec ℒₒᵣ n m w) (hv : IsSemitermVec ℒₒᵣ m l v) :
    subst ℒₒᵣ v (^⋁ (substItr w p k)) = ^⋁ (substItr (termSubstVec ℒₒᵣ n v w) p k) := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih =>
    have hkw : IsSemitermVec ℒₒᵣ (n + 1) m (numeral k ∷ w) := by simp [hw]
    have ha : IsSemiformula ℒₒᵣ m (^⋁ substItr w p k) := by
      simp only [qqDisj_semiformula, len_substItr]
      intro i hi; simpa [hi] using hp.subst (hw.adjoin (by simp))
    simp only [substItr_succ, qqDisj_cons]
    rw [substs_or (hp.subst hkw).isUFormula ha.isUFormula,
      substs_substs hp hv hkw,
      termSubstVec_cons (by simp) hw.isUTerm,
      numeral_substs hv]
    simp [ih]

end substItr

end Arithmetic

section verums

noncomputable def qqVerums (k : V) : V := ^⋀ repeatVec ^⊤ k

def qqVerumsGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y k. ∃ verum, !qqVerumDef verum ∧ ∃ vs, !repeatVecDef vs verum k ∧ !qqConjGraph y vs”

@[simp] lemma le_qqVerums (k : V) : k ≤ qqVerums k := by
  simpa [qqVerums] using len_le_conj (repeatVec ^⊤ k)

section

instance qqVerums.defined : 𝚺₁-Function₁[V] qqVerums via qqVerumsGraph := .mk fun v ↦ by simp [qqVerumsGraph]; rfl

instance qqVerums.definable : 𝚺₁-Function₁[V] qqVerums := qqVerums.defined.to_definable

instance qqVerums.definable' : Γ-[m + 1]-Function₁[V] qqVerums := .of_sigmaOne qqVerums.definable

end

@[simp] protected lemma IsSemiformula.qqVerums (k : V) : IsSemiformula L n (qqVerums k) := by
  simp only [qqVerums, qqConj_semiformula, len_repeatVec]
  intro i hi; simp [nth_repeatVec _ _ hi]

@[simp] lemma qqVerums_zero : qqVerums (0 : V) = ^⊤ := by simp [qqVerums]

@[simp] lemma qqVerums_succ (k : V) : qqVerums (k + 1) = ^⊤ ^⋏ qqVerums k := by simp [qqVerums]

end verums

end LO.FirstOrder.Arithmetic.Bootstrapping
