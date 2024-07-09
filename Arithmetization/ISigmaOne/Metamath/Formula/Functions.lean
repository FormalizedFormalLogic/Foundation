import Arithmetization.ISigmaOne.Metamath.Formula.Basic
import Arithmetization.ISigmaOne.Metamath.Term.Functions

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

namespace Negation

def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel := .mkSigma “y param n k R v | !qqNRelDef y n k R v” (by simp)
  nrel := .mkSigma “y param n k R v | !qqRelDef y n k R v” (by simp)
  verum := .mkSigma “y param n | !qqFalsumDef y n” (by simp)
  falsum := .mkSigma “y param n | !qqVerumDef y n” (by simp)
  and := .mkSigma “y param n p₁ p₂ y₁ y₂ | !qqOrDef y n y₁ y₂” (by simp)
  or := .mkSigma “y param n p₁ p₂ y₁ y₂ | !qqAndDef y n y₁ y₂” (by simp)
  all := .mkSigma “y param n p₁ y₁ | !qqExDef y n y₁” (by simp)
  ex := .mkSigma “y param n p₁ y₁ | !qqAllDef y n y₁” (by simp)
  allChanges := .mkSigma “param' param n | param' = 0” (by simp)
  exChanges := .mkSigma “param' param n | param' = 0” (by simp)

variable (L)

def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel {_} := fun n k R v ↦ ^nrel n k R v
  nrel {_} := fun n k R v ↦ ^rel n k R v
  verum {_} := fun n ↦ ^⊥[n]
  falsum {_} := fun n ↦ ^⊤[n]
  and {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋎[n] y₂
  or {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋏[n] y₂
  all {_} := fun n _ y₁ ↦ ^∃[n] y₁
  ex {_} := fun n _ y₁ ↦ ^∀[n] y₁
  allChanges := fun _ _ ↦ 0
  exChanges := fun _ _ ↦ 0
  rel_defined := by intro v; simp [blueprint]; rfl
  nrel_defined := by intro v; simp [blueprint]; rfl
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]; rfl
  or_defined := by intro v; simp [blueprint]; rfl
  all_defined := by intro v; simp [blueprint]; rfl
  ex_defined := by intro v; simp [blueprint]; rfl
  allChanges_defined := by intro v; simp [blueprint]
  exChanges_defined := by intro v; simp [blueprint]

end Negation

section negation

open Negation

variable (L)

def Language.neg (p : V) : V := (construction L).result 0 p

variable {L}

@[simp] lemma neg_rel {n k R v} (hR : L.Rel k R) (hv : L.SemitermSeq k n v) :
    L.neg (^rel n k R v) = ^nrel n k R v := by simp [Language.neg, hR, hv, construction]

@[simp] lemma neg_nrel {n k R v} (hR : L.Rel k R) (hv : L.SemitermSeq k n v) :
    L.neg (^nrel n k R v) = ^rel n k R v := by simp [Language.neg, hR, hv, construction]

@[simp] lemma neg_verum (n) :
    L.neg ^⊤[n] = ^⊥[n] := by simp [Language.neg, construction]

@[simp] lemma neg_falsum (n) :
    L.neg ^⊥[n] = ^⊤[n] := by simp [Language.neg, construction]

@[simp] lemma neg_and {n p q} (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    L.neg (p ^⋏[n] q) = L.neg p ^⋎[n] L.neg q := by simp [Language.neg, hp, hq, construction]

@[simp] lemma neg_or {n p q} (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    L.neg (p ^⋎[n] q) = L.neg p ^⋏[n] L.neg q := by simp [Language.neg, hp, hq, construction]

@[simp] lemma neg_all {n p} (hp : L.Semiformula (n + 1) p) :
    L.neg (^∀[n] p) = ^∃[n] (L.neg p) := by simp [Language.neg, hp, construction]

@[simp] lemma neg_ex {n p} (hp : L.Semiformula (n + 1) p) :
    L.neg (^∃[n] p) = ^∀[n] (L.neg p) := by simp [Language.neg, hp, construction]

section

def _root_.LO.FirstOrder.Arith.LDef.negDef (pL : LDef) : 𝚺₁-Semisentence 2 := (blueprint pL).result.rew (Rew.substs ![#0, ‘0’, #1])

variable (L)

lemma neg_defined : 𝚺₁-Function₁ L.neg via pL.negDef := fun v ↦ by
  simpa [LDef.negDef] using (construction L).result_defined ![v 0, 0, v 1]

@[simp] lemma neg_defined_iff (v : Fin 2 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.negDef ↔ v 0 = L.neg (v 1) := (neg_defined L).df.iff v

instance neg_definable : 𝚺₁-Function₁ L.neg :=
  Defined.to_definable _ (neg_defined L)

@[simp, definability] instance neg_definable' (Γ) : (Γ, m + 1)-Function₁ L.neg :=
  .of_sigmaOne (neg_definable L) _ _

end

@[simp] lemma Language.Semiformula.neg {p : V} : L.Semiformula n p → L.Semiformula n (L.neg p) := by
  apply Language.Semiformula.induction_sigma₁
  · definability
  · intro n k r v hr hv; simp [hr, hv]
  · intro n k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro n p hp ihp; simp [hp, ihp]
  · intro n p hp ihp; simp [hp, ihp]

@[simp] lemma neg_neg {p : V} : L.Semiformula n p → L.neg (L.neg p) = p := by
  apply Language.Semiformula.induction_sigma₁
  · definability
  · intro n k r v hr hv; simp [hr, hv]
  · intro n k r v hr hv; simp [hr, hv]
  · intro n; simp
  · intro n; simp
  · intro n p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro n p hp ihp; simp [hp, ihp]
  · intro n p hp ihp; simp [hp, ihp]

end negation

section substs

variable (L)

def Language.qSeq (k n w : V) : V := #̂0 `⁀ L.termBShiftSeq k n w

variable {L}

lemma Language.SemitermSeq.qSeq {k n w : V} (h : L.SemitermSeq k n w) : L.SemitermSeq (k + 1) (n + 1) (L.qSeq k n w) :=
  ⟨Seq.seqPop _ h.termBShiftSeq.seq,
    by simp [Language.qSeq, h.termBShiftSeq.seq.seqPop_lh, ←h.termBShiftSeq.lh], by
      simp [Language.qSeq]
      intro i t hit
      rcases h.termBShiftSeq.seq.seqPop_iff.mp hit with (⟨rfl, rfl⟩ | ⟨i, rfl, ht⟩)
      · simp
      · exact h.termBShiftSeq.prop _ _ ht⟩

section

variable (L)

def _root_.LO.FirstOrder.Arith.LDef.qSeqDef (pL : LDef) : 𝚺₁-Semisentence 4 := .mkSigma
  “w' k n w | ∃ sw, !pL.termBShiftSeqDef sw k n w ∧ ∃ t, !qqBvarDef t 0 ∧ !seqPopDef w' t sw” (by simp)

lemma qSeq_defined : 𝚺₁-Function₃ L.qSeq via pL.qSeqDef := by
  intro v; simp [LDef.qSeqDef, eval_termBShiftSeqDef L]; rfl

instance qSeq_definable : 𝚺₁-Function₃ L.qSeq := Defined.to_definable _ (qSeq_defined L)

@[simp, definability] instance qSeq_definable' (Γ m) : (Γ, m + 1)-Function₃ L.qSeq := .of_sigmaOne (qSeq_definable L) _ _

end

namespace Substs

def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel    := .mkSigma “y param n k R v m w | ∃ v', !pL.termSubstSeqDef k n m w v v' ∧ !qqRelDef y m k R v'” (by simp)
  nrel   := .mkSigma “y param n k R v m w | ∃ v', !pL.termSubstSeqDef k n m w v v' ∧ !qqNRelDef y m k R v'” (by simp)
  verum  := .mkSigma “y param n m w | !qqVerumDef y m” (by simp)
  falsum := .mkSigma “y param n m w | !qqFalsumDef y m” (by simp)
  and    := .mkSigma “y param n p₁ p₂ y₁ y₂ m w | !qqAndDef y m y₁ y₂” (by simp)
  or     := .mkSigma “y param n p₁ p₂ y₁ y₂ m w | !qqOrDef y m y₁ y₂” (by simp)
  all    := .mkSigma “y param n p₁ y₁ m w | !qqAllDef y m y₁” (by simp)
  ex     := .mkSigma “y param n p₁ y₁ m w | !qqExDef y m y₁” (by simp)
  allChanges := .mkSigma “w' w n | ” (by simp)

/--/
variable (L)

def construction : Language.UformulaRec.Construction V L (blueprint pL) where
  rel    {param} := fun n k R v ↦ ^rel (param 0) k R (L.termSubstSeq k n (param 0) (param 1) v)
  nrel   {param} := fun n k R v ↦ ^nrel (param 0) k R (L.termSubstSeq k n (param 0) (param 1) v)
  verum  {param} := fun n ↦ ^⊤[param 0]
  falsum {param} := fun n ↦ ^⊥[param 0]
  and    {param} := fun n _ _ y₁ y₂ ↦ y₁ ^⋎[param 0] y₂
  or     {param} := fun n _ _ y₁ y₂ ↦ y₁ ^⋏[param 0] y₂
  all    {param} := fun n _ y₁ ↦ ^∀[param 0] y₁
  ex     {param} := fun n _ y₁ ↦ ^∃[param 0] y₁

  nrel {_} := fun n k R v ↦ ^rel n k R v
  verum {_} := fun n ↦ ^⊥[n]
  falsum {_} := fun n ↦ ^⊤[n]
  and {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋎[n] y₂
  or {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋏[n] y₂
  all {_} := fun n _ y₁ ↦ ^∃[n] y₁
  ex {_} := fun n _ y₁ ↦ ^∀[n] y₁
  rel_defined := by intro v; simp [blueprint]; rfl
  nrel_defined := by intro v; simp [blueprint]; rfl
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]; rfl
  or_defined := by intro v; simp [blueprint]; rfl
  all_defined := by intro v
-/



end substs

end LO.Arith

end
