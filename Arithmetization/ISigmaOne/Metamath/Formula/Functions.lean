import Arithmetization.ISigmaOne.Metamath.Formula.Basic
import Arithmetization.ISigmaOne.Metamath.Term.Functions

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section negation

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

open Negation

variable (L)

def Language.neg (p : V) : V := (construction L).result 0 p

variable {L}

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

section shift

namespace Shift

def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel := .mkSigma “y param n k R v | ∃ v', !pL.termShiftSeqDef v' k n v ∧ !qqRelDef y n k R v'” (by simp)
  nrel := .mkSigma “y param n k R v | ∃ v', !pL.termShiftSeqDef v' k n v ∧ !qqNRelDef y n k R v'” (by simp)
  verum := .mkSigma “y param n | !qqVerumDef y n” (by simp)
  falsum := .mkSigma “y param n | !qqFalsumDef y n” (by simp)
  and := .mkSigma “y param n p₁ p₂ y₁ y₂ | !qqAndDef y n y₁ y₂” (by simp)
  or := .mkSigma “y param n p₁ p₂ y₁ y₂ | !qqOrDef y n y₁ y₂” (by simp)
  all := .mkSigma “y param n p₁ y₁ | !qqAllDef y n y₁” (by simp)
  ex := .mkSigma “y param n p₁ y₁ | !qqExDef y n y₁” (by simp)
  allChanges := .mkSigma “param' param n | param' = 0” (by simp)
  exChanges := .mkSigma “param' param n | param' = 0” (by simp)

variable (L)

def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel {_} := fun n k R v ↦ ^rel n k R (L.termShiftSeq k n v)
  nrel {_} := fun n k R v ↦ ^nrel n k R (L.termShiftSeq k n v)
  verum {_} := fun n ↦ ^⊤[n]
  falsum {_} := fun n ↦ ^⊥[n]
  and {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋏[n] y₂
  or {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋎[n] y₂
  all {_} := fun n _ y₁ ↦ ^∀[n] y₁
  ex {_} := fun n _ y₁ ↦ ^∃[n] y₁
  allChanges := fun _ _ ↦ 0
  exChanges := fun _ _ ↦ 0
  rel_defined := by intro v; simp [blueprint, (termShiftSeq_defined L).df.iff]; rfl
  nrel_defined := by intro v; simp [blueprint, (termShiftSeq_defined L).df.iff]; rfl
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]; rfl
  or_defined := by intro v; simp [blueprint]; rfl
  all_defined := by intro v; simp [blueprint]; rfl
  ex_defined := by intro v; simp [blueprint]; rfl
  allChanges_defined := by intro v; simp [blueprint]
  exChanges_defined := by intro v; simp [blueprint]

end Shift

open Shift

variable (L)

def Language.shift (p : V) : V := (construction L).result 0 p

variable {L}

section

def _root_.LO.FirstOrder.Arith.LDef.shiftDef (pL : LDef) : 𝚺₁-Semisentence 2 := (blueprint pL).result.rew (Rew.substs ![#0, ‘0’, #1])

variable (L)

lemma shift_defined : 𝚺₁-Function₁ L.shift via pL.shiftDef := fun v ↦ by
  simpa [LDef.shiftDef] using (construction L).result_defined ![v 0, 0, v 1]

@[simp] lemma eval_shiftDef (v : Fin 2 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.shiftDef ↔ v 0 = L.shift (v 1) := (shift_defined L).df.iff v

instance shift_definable : 𝚺₁-Function₁ L.shift :=
  Defined.to_definable _ (shift_defined L)

@[simp, definability] instance shift_definable' (Γ) : (Γ, m + 1)-Function₁ L.shift :=
  .of_sigmaOne (shift_definable L) _ _

end

@[simp] lemma shift_rel {n k R v} (hR : L.Rel k R) (hv : L.SemitermSeq k n v) :
    L.shift (^rel n k R v) = ^rel n k R (L.termShiftSeq k n v) := by simp [Language.shift, hR, hv, construction]

@[simp] lemma shift_nrel {n k R v} (hR : L.Rel k R) (hv : L.SemitermSeq k n v) :
    L.shift (^nrel n k R v) = ^nrel n k R (L.termShiftSeq k n v) := by simp [Language.shift, hR, hv, construction]

@[simp] lemma shift_verum (n) :
    L.shift ^⊤[n] = ^⊤[n] := by simp [Language.shift, construction]

@[simp] lemma shift_falsum (n) :
    L.shift ^⊥[n] = ^⊥[n] := by simp [Language.shift, construction]

@[simp] lemma shift_and {n p q} (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    L.shift (p ^⋏[n] q) = L.shift p ^⋏[n] L.shift q := by simp [Language.shift, hp, hq, construction]

@[simp] lemma shift_or {n p q} (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    L.shift (p ^⋎[n] q) = L.shift p ^⋎[n] L.shift q := by simp [Language.shift, hp, hq, construction]

@[simp] lemma shift_all {n p} (hp : L.Semiformula (n + 1) p) :
    L.shift (^∀[n] p) = ^∀[n] (L.shift p) := by simp [Language.shift, hp, construction]

@[simp] lemma shift_ex {n p} (hp : L.Semiformula (n + 1) p) :
    L.shift (^∃[n] p) = ^∃[n] (L.shift p) := by simp [Language.shift, hp, construction]

@[simp] lemma Language.Semiformula.shift {p : V} : L.Semiformula n p → L.Semiformula n (L.shift p) := by
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

end shift

section substs

variable (L)

def Language.qSeq (k n w : V) : V := ^#0 `⁀ L.termBShiftSeq k n w

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
  rel    := .mkSigma “y param n k R v | ∃ m, !pi₁Def m param ∧ ∃ w, !pi₂Def w param ∧ ∃ v', !pL.termSubstSeqDef v' k n m w v ∧ !qqRelDef y m k R v'” (by simp)
  nrel   := .mkSigma “y param n k R v | ∃ m, !pi₁Def m param ∧ ∃ w, !pi₂Def w param ∧ ∃ v', !pL.termSubstSeqDef v' k n m w v ∧ !qqNRelDef y m k R v'” (by simp)
  verum  := .mkSigma “y param n | ∃ m, !pi₁Def m param ∧ !qqVerumDef y m” (by simp)
  falsum := .mkSigma “y param n | ∃ m, !pi₁Def m param ∧ !qqFalsumDef y m” (by simp)
  and    := .mkSigma “y param n p₁ p₂ y₁ y₂ | ∃ m, !pi₁Def m param ∧ !qqAndDef y m y₁ y₂” (by simp)
  or     := .mkSigma “y param n p₁ p₂ y₁ y₂ | ∃ m, !pi₁Def m param ∧ !qqOrDef y m y₁ y₂” (by simp)
  all    := .mkSigma “y param n p₁ y₁ | ∃ m, !pi₁Def m param ∧ !qqAllDef y m y₁” (by simp)
  ex     := .mkSigma “y param n p₁ y₁ | ∃ m, !pi₁Def m param ∧ !qqExDef y m y₁” (by simp)
  allChanges := .mkSigma “param' param n | ∃ m, !pi₁Def m param ∧ ∃ w, !pi₂Def w param ∧ ∃ qseq, !pL.qSeqDef qseq n m w ∧ !pairDef param' (m + 1) qseq” (by simp)
  exChanges := .mkSigma “param' param n | ∃ m, !pi₁Def m param ∧ ∃ w, !pi₂Def w param ∧ ∃ qseq, !pL.qSeqDef qseq n m w ∧ !pairDef param' (m + 1) qseq” (by simp)

variable (L)

def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel (param) := fun n k R v ↦ ^rel (π₁ param) k R (L.termSubstSeq k n (π₁ param) (π₂ param) v)
  nrel (param) := fun n k R v ↦ ^nrel (π₁ param) k R (L.termSubstSeq k n (π₁ param) (π₂ param) v)
  verum (param) := fun _ ↦ ^⊤[π₁ param]
  falsum (param) := fun _ ↦ ^⊥[π₁ param]
  and (param) := fun _ _ _ y₁ y₂ ↦ y₁ ^⋏[π₁ param] y₂
  or (param) := fun _ _ _ y₁ y₂ ↦ y₁ ^⋎[π₁ param] y₂
  all (param) := fun _ _ y₁ ↦ ^∀[π₁ param] y₁
  ex (param) := fun _ _ y₁ ↦ ^∃[π₁ param] y₁
  allChanges (param n) := ⟪π₁ param + 1, L.qSeq n (π₁ param) (π₂ param)⟫
  exChanges (param n) := ⟪π₁ param + 1, L.qSeq n (π₁ param) (π₂ param)⟫
  rel_defined := by intro v; simp [blueprint, (termSubstSeq_defined L).df.iff]; rfl
  nrel_defined := by intro v; simp [blueprint, (termSubstSeq_defined L).df.iff]; rfl
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]; rfl
  or_defined := by intro v; simp [blueprint]; rfl
  all_defined := by intro v; simp [blueprint]; rfl
  ex_defined := by intro v; simp [blueprint]; rfl
  allChanges_defined := by intro v; simp [blueprint, (qSeq_defined L).df.iff]
  exChanges_defined := by intro v; simp [blueprint, (qSeq_defined L).df.iff]

end Substs

open Substs

variable (L)

def Language.substs (m w p : V) : V := (construction L).result ⟪m, w⟫ p

variable {L}

section

def _root_.LO.FirstOrder.Arith.LDef.substsDef (pL : LDef) : 𝚺₁-Semisentence 4 := .mkSigma
  “q m w p | ∃ mw, !pairDef mw m w ∧ !(blueprint pL).result q mw p” (by simp)

variable (L)

lemma substs_defined : 𝚺₁-Function₃ L.substs via pL.substsDef := fun v ↦ by
  simp [LDef.substsDef, (construction L).result_defined.df.iff]; rfl

@[simp] lemma eval_substsDef (v : Fin 4 → V) :
    Semiformula.Evalbm (L := ℒₒᵣ) V v pL.substsDef ↔ v 0 = L.substs (v 1) (v 2) (v 3) := (substs_defined L).df.iff v

instance substs_definable : 𝚺₁-Function₃ L.substs :=
  Defined.to_definable _ (substs_defined L)

@[simp, definability] instance substs_definable' (Γ) : (Γ, m + 1)-Function₃ L.substs :=
  .of_sigmaOne (substs_definable L) _ _

end

variable {m w : V}

@[simp] lemma substs_rel {n k R v} (hR : L.Rel k R) (hv : L.SemitermSeq k n v) :
    L.substs m w (^rel n k R v) = ^rel m k R (L.termSubstSeq k n m w v) := by simp [Language.substs, hR, hv, construction]

@[simp] lemma substs_nrel {n k R v} (hR : L.Rel k R) (hv : L.SemitermSeq k n v) :
    L.substs m w (^nrel n k R v) = ^nrel m k R (L.termSubstSeq k n m w v) := by simp [Language.substs, hR, hv, construction]

@[simp] lemma substs_verum (n) :
    L.substs m w ^⊤[n] = ^⊤[m] := by simp [Language.substs, construction]

@[simp] lemma substs_falsum (n) :
    L.substs m w ^⊥[n] = ^⊥[m] := by simp [Language.substs, construction]

@[simp] lemma substs_and {n p q} (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    L.substs m w (p ^⋏[n] q) = L.substs m w p ^⋏[m] L.substs m w q := by simp [Language.substs, hp, hq, construction]

@[simp] lemma substs_or {n p q} (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    L.substs m w (p ^⋎[n] q) = L.substs m w p ^⋎[m] L.substs m w q := by simp [Language.substs, hp, hq, construction]

@[simp] lemma substs_all {n p} (hp : L.Semiformula (n + 1) p) :
    L.substs m w (^∀[n] p) = ^∀[m] (L.substs (m + 1) (L.qSeq n m w) p) := by simp [Language.substs, hp, construction]

@[simp] lemma substs_ex {n p} (hp : L.Semiformula (n + 1) p) :
    L.substs m w (^∃[n] p) = ^∃[m] (L.substs (m + 1) (L.qSeq n m w) p) := by simp [Language.substs, hp, construction]

lemma semiformula_subst_induction {P : V → V → V → V → V → Prop} (hP : 𝚺₁-Relation₅ P)
    (hRel : ∀ n m w k R v, L.Rel k R → L.SemitermSeq k n v → P n m w (^rel n k R v) (^rel m k R (L.termSubstSeq k n m w v)))
    (hNRel : ∀ n m w k R v, L.Rel k R → L.SemitermSeq k n v → P n m w (^nrel n k R v) (^nrel m k R (L.termSubstSeq k n m w v)))
    (hverum : ∀ n m w, P n m w (^⊤[n]) (^⊤[m]))
    (hfalsum : ∀ n m w, P n m w (^⊥[n]) (^⊥[m]))
    (hand : ∀ n m w p q, L.Semiformula n p → L.Semiformula n q →
      P n m w p (L.substs m w p) → P n m w q (L.substs m w q) → P n m w (p ^⋏[n] q) (L.substs m w p ^⋏[m] L.substs m w q))
    (hor : ∀ n m w p q, L.Semiformula n p → L.Semiformula n q →
      P n m w p (L.substs m w p) → P n m w q (L.substs m w q) → P n m w (p ^⋎[n] q) (L.substs m w p ^⋎[m] L.substs m w q))
    (hall : ∀ n m w p, L.Semiformula (n + 1) p →
      P (n + 1) (m + 1) (L.qSeq n m w) p (L.substs (m + 1) (L.qSeq n m w) p) →
      P n m w (^∀[n] p) (^∀[m] (L.substs (m + 1) (L.qSeq n m w) p)))
    (hex : ∀ n m w p, L.Semiformula (n + 1) p →
      P (n + 1) (m + 1) (L.qSeq n m w) p (L.substs (m + 1) (L.qSeq n m w) p) →
      P n m w (^∃[n] p) (^∃[m] (L.substs (m + 1) (L.qSeq n m w) p))) :
    ∀ {n p m w}, L.Semiformula n p → P n m w p (L.substs m w p) := by
  suffices ∀ param n p, L.Semiformula n p → P n (π₁ param) (π₂ param) p ((construction L).result param p) by
    intro n p m w hp; simpa using this ⟪m, w⟫ n p hp
  apply (construction L).semiformula_result_induction (P := fun param n p y ↦ P n (π₁ param) (π₂ param) p y)
  · apply Definable.comp₅'
      (DefinableFunction.var _)
      (DefinableFunction.comp₁ (DefinableFunction.var _))
      (DefinableFunction.comp₁ (DefinableFunction.var _))
      (DefinableFunction.var _)
      (DefinableFunction.var _)
  · intro param n k R v hkR hv; simpa using hRel n (π₁ param) (π₂ param) k R v hkR hv
  · intro param n k R v hkR hv; simpa using hNRel n (π₁ param) (π₂ param) k R v hkR hv
  · intro param n; simpa using hverum n (π₁ param) (π₂ param)
  · intro param n; simpa using hfalsum n (π₁ param) (π₂ param)
  · intro param n p q hp hq ihp ihq
    simpa [Language.substs] using
      hand n (π₁ param) (π₂ param) p q hp hq (by simpa [Language.substs] using ihp) (by simpa [Language.substs] using ihq)
  · intro param n p q hp hq ihp ihq
    simpa [Language.substs] using
      hor n (π₁ param) (π₂ param) p q hp hq (by simpa [Language.substs] using ihp) (by simpa [Language.substs] using ihq)
  · intro param n p hp ihp
    simpa using hall n (π₁ param) (π₂ param) p hp (by simpa [construction] using ihp)
  · intro param n p hp ihp
    simpa using hex n (π₁ param) (π₂ param) p hp (by simpa [construction] using ihp)

@[simp] lemma Language.Semiformula.substs {n p m w : V} :
    L.Semiformula n p → L.SemitermSeq n m w → L.Semiformula m (L.substs m w p) := by
  apply semiformula_subst_induction (P := fun n m w _ y ↦ L.SemitermSeq n m w → L.Semiformula m y)
  · definability
  case hRel => intro n m w k R v hR hv hw; simp [hR, hv, hw]
  case hNRel => intro n m w k R v hR hv hw; simp [hR, hv, hw]
  case hverum => simp
  case hfalsum => simp
  case hand =>
    intro n m w p q _ _ ihp ihq hw
    simp [ihp hw, ihq hw]
  case hor =>
    intro n m w p q _ _ ihp ihq hw
    simp [ihp hw, ihq hw]
  case hall =>
    intro n m w p _ ih hw
    simpa using ih hw.qSeq
  case hex =>
    intro n m w p _ ih hw
    simpa using ih hw.qSeq

end substs

end LO.Arith

end
