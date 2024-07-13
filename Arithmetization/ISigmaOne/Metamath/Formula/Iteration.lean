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

def _root_.LO.FirstOrder.Arith.qqConjDef : 𝚺₁-Semisentence 3 := blueprint.resultDef.rew (Rew.substs ![#0, #2, #1])

lemma qqConj_defined : 𝚺₁-Function₂ (qqConj : V → V → V) via qqConjDef := by
  intro v; simpa [qqConjDef] using construction.result_defined ![v 0, v 2, v 1]

@[simp] lemma eval_qqConj (v) :
    Semiformula.Evalbm V v qqConjDef.val ↔ v 0 = qqConj (v 1) (v 2) := qqConj_defined.df.iff v

instance qqConj_definable : 𝚺₁-Function₂ (qqConj : V → V → V) := Defined.to_definable _ qqConj_defined

instance qqConj_definable' (Γ) : (Γ, m + 1)-Function₂ (qqConj : V → V → V) := .of_sigmaOne qqConj_definable _ _

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

def _root_.LO.FirstOrder.Arith.qqDisjDef : 𝚺₁-Semisentence 3 := blueprint.resultDef.rew (Rew.substs ![#0, #2, #1])

lemma qqDisj_defined : 𝚺₁-Function₂ (qqDisj : V → V → V) via qqDisjDef := by
  intro v; simpa [qqDisjDef] using construction.result_defined ![v 0, v 2, v 1]

@[simp] lemma eval_qqDisj (v) :
    Semiformula.Evalbm V v qqDisjDef.val ↔ v 0 = qqDisj (v 1) (v 2) := qqDisj_defined.df.iff v

instance qqDisj_definable : 𝚺₁-Function₂ (qqDisj : V → V → V) := Defined.to_definable _ qqDisj_defined

instance qqDisj_definable' (Γ) : (Γ, m + 1)-Function₂ (qqDisj : V → V → V) := .of_sigmaOne qqDisj_definable _ _

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

end LO.Arith

end
