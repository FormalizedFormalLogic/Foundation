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

@[simp] lemma neg_rel {n k R v} (hR : L.Rel k R) (hv : L.SemitermVec k n v) :
    L.neg (^rel n k R v) = ^nrel n k R v := by simp [Language.neg, hR, hv, construction]

@[simp] lemma neg_nrel {n k R v} (hR : L.Rel k R) (hv : L.SemitermVec k n v) :
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

lemma neg_not_uformula {x} (h : ¬L.UFormula x) :
    L.neg x = 0 := (construction L).result_prop_not _ h

lemma fstIdx_neg {p} (h : L.UFormula p) : fstIdx (L.neg p) = fstIdx p := by
  rcases h.case with (⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;>
    simp [*]

lemma Language.Semiformula.neg {p : V} : L.Semiformula n p → L.Semiformula n (L.neg p) := by
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

@[simp] lemma Language.Semiformula.neg_iff {p : V} : L.Semiformula n (L.neg p) ↔ L.Semiformula n p :=
  ⟨fun h ↦ by
    rcases h with ⟨h, rfl⟩
    have : L.UFormula p := by
      by_contra hp
      simp [neg_not_uformula hp] at h
    exact ⟨this, by simp [fstIdx_neg this]⟩,
    Language.Semiformula.neg⟩

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

@[simp] lemma neg_inj_iff (hp : L.Semiformula n p) (hq : L.Semiformula n q) : L.neg p = L.neg q ↔ p = q := by
  constructor
  · intro h; simpa [neg_neg hp, neg_neg hq] using congrArg L.neg h
  · rintro rfl; rfl

end negation

variable (L)

def Language.imp (n p q : V) : V := L.neg p ^⋎[n] q

notation:60 p:61 " ^→[" L "; " n "] " q:60 => Language.imp L n p q

variable {L}

section imp

@[simp] lemma Language.Semiformula.imp {n p q : V} :
    L.Semiformula n (L.imp n p q) ↔ L.Semiformula n p ∧ L.Semiformula n q := by
  simp [Language.imp]

section

def _root_.LO.FirstOrder.Arith.LDef.impDef (pL : LDef) : 𝚺₁-Semisentence 4 := .mkSigma
  “r n p q | ∃ np, !pL.negDef np p ∧ !qqOrDef r n np q” (by simp)

variable (L)

lemma imp_defined : 𝚺₁-Function₃ L.imp via pL.impDef := fun v ↦ by
  simp [LDef.impDef, (neg_defined L).df.iff]; rfl

@[simp] lemma eval_impDef (v : Fin 4 → V) :
    Semiformula.Evalbm V v pL.impDef.val ↔ v 0 = L.imp (v 1) (v 2) (v 3) := (imp_defined L).df.iff v

instance imp_definable : 𝚺₁-Function₃ L.imp :=
  Defined.to_definable _ (imp_defined L)

instance imp_definable' (Γ) : (Γ, m + 1)-Function₃ L.imp :=
  .of_sigmaOne (imp_definable L) _ _

end

end imp

section shift

namespace Shift

def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel := .mkSigma “y param n k R v | ∃ v', !pL.termShiftVecDef v' k n v ∧ !qqRelDef y n k R v'” (by simp)
  nrel := .mkSigma “y param n k R v | ∃ v', !pL.termShiftVecDef v' k n v ∧ !qqNRelDef y n k R v'” (by simp)
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
  rel {_} := fun n k R v ↦ ^rel n k R (L.termShiftVec k n v)
  nrel {_} := fun n k R v ↦ ^nrel n k R (L.termShiftVec k n v)
  verum {_} := fun n ↦ ^⊤[n]
  falsum {_} := fun n ↦ ^⊥[n]
  and {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋏[n] y₂
  or {_} := fun n _ _ y₁ y₂ ↦ y₁ ^⋎[n] y₂
  all {_} := fun n _ y₁ ↦ ^∀[n] y₁
  ex {_} := fun n _ y₁ ↦ ^∃[n] y₁
  allChanges := fun _ _ ↦ 0
  exChanges := fun _ _ ↦ 0
  rel_defined := by intro v; simp [blueprint, (termShiftVec_defined L).df.iff]; rfl
  nrel_defined := by intro v; simp [blueprint, (termShiftVec_defined L).df.iff]; rfl
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

@[simp] lemma shift_rel {n k R v} (hR : L.Rel k R) (hv : L.SemitermVec k n v) :
    L.shift (^rel n k R v) = ^rel n k R (L.termShiftVec k n v) := by simp [Language.shift, hR, hv, construction]

@[simp] lemma shift_nrel {n k R v} (hR : L.Rel k R) (hv : L.SemitermVec k n v) :
    L.shift (^nrel n k R v) = ^nrel n k R (L.termShiftVec k n v) := by simp [Language.shift, hR, hv, construction]

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

lemma shift_not_uformula {x} (h : ¬L.UFormula x) :
    L.shift x = 0 := (construction L).result_prop_not _ h

lemma Language.Semiformula.shift {p : V} : L.Semiformula n p → L.Semiformula n (L.shift p) := by
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

lemma fstIdx_shift {p} (h : L.UFormula p) : fstIdx (L.shift p) = fstIdx p := by
  rcases h.case with (⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;>
    simp [*]

@[simp] lemma Language.Semiformula.shift_iff {p : V} : L.Semiformula n (L.shift p) ↔ L.Semiformula n p :=
  ⟨fun h ↦ by
    rcases h with ⟨h, rfl⟩
    have : L.UFormula p := by
      by_contra hp
      simp [shift_not_uformula hp] at h
    exact ⟨this, by simp [fstIdx_shift this]⟩,
    Language.Semiformula.shift⟩

lemma shift_neg {p : V} (hp : L.Semiformula n p) : L.shift (L.neg p) = L.neg (L.shift p) := by
  apply Language.Semiformula.induction_sigma₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ hp
  · definability
  · intro n k R v hR hv; simp [*]
  · intro n k R v hR hv; simp [*]
  · intro n; simp
  · intro n; simp
  · intro n p q hp hq ihp ihq; simp [*]
  · intro n p q hp hq ihp ihq; simp [*]
  · intro n p hp ih; simp [*]
  · intro n p hp ih; simp [*]

end shift

section substs

section

variable (L)

def _root_.LO.FirstOrder.Arith.LDef.qVecDef (pL : LDef) : 𝚺₁-Semisentence 4 := .mkSigma
  “w' k n w | ∃ sw, !pL.termBShiftVecDef sw k n w ∧ ∃ t, !qqBvarDef t 0 ∧ !consDef w' t sw” (by simp)

lemma qVec_defined : 𝚺₁-Function₃ L.qVec via pL.qVecDef := by
  intro v; simp [LDef.qVecDef, eval_termBShiftVecDef L]; rfl

instance qVec_definable : 𝚺₁-Function₃ L.qVec := Defined.to_definable _ (qVec_defined L)

@[simp, definability] instance qVec_definable' (Γ m) : (Γ, m + 1)-Function₃ L.qVec := .of_sigmaOne (qVec_definable L) _ _

end

namespace Substs

def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel    := .mkSigma “y param n k R v | ∃ m, !pi₁Def m param ∧ ∃ w, !pi₂Def w param ∧ ∃ v', !pL.termSubstVecDef v' k n m w v ∧ !qqRelDef y m k R v'” (by simp)
  nrel   := .mkSigma “y param n k R v | ∃ m, !pi₁Def m param ∧ ∃ w, !pi₂Def w param ∧ ∃ v', !pL.termSubstVecDef v' k n m w v ∧ !qqNRelDef y m k R v'” (by simp)
  verum  := .mkSigma “y param n | ∃ m, !pi₁Def m param ∧ !qqVerumDef y m” (by simp)
  falsum := .mkSigma “y param n | ∃ m, !pi₁Def m param ∧ !qqFalsumDef y m” (by simp)
  and    := .mkSigma “y param n p₁ p₂ y₁ y₂ | ∃ m, !pi₁Def m param ∧ !qqAndDef y m y₁ y₂” (by simp)
  or     := .mkSigma “y param n p₁ p₂ y₁ y₂ | ∃ m, !pi₁Def m param ∧ !qqOrDef y m y₁ y₂” (by simp)
  all    := .mkSigma “y param n p₁ y₁ | ∃ m, !pi₁Def m param ∧ !qqAllDef y m y₁” (by simp)
  ex     := .mkSigma “y param n p₁ y₁ | ∃ m, !pi₁Def m param ∧ !qqExDef y m y₁” (by simp)
  allChanges := .mkSigma “param' param n | ∃ m, !pi₁Def m param ∧ ∃ w, !pi₂Def w param ∧ ∃ qseq, !pL.qVecDef qseq n m w ∧ !pairDef param' (m + 1) qseq” (by simp)
  exChanges := .mkSigma “param' param n | ∃ m, !pi₁Def m param ∧ ∃ w, !pi₂Def w param ∧ ∃ qseq, !pL.qVecDef qseq n m w ∧ !pairDef param' (m + 1) qseq” (by simp)

variable (L)

def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel (param) := fun n k R v ↦ ^rel (π₁ param) k R (L.termSubstVec k n (π₁ param) (π₂ param) v)
  nrel (param) := fun n k R v ↦ ^nrel (π₁ param) k R (L.termSubstVec k n (π₁ param) (π₂ param) v)
  verum (param) := fun _ ↦ ^⊤[π₁ param]
  falsum (param) := fun _ ↦ ^⊥[π₁ param]
  and (param) := fun _ _ _ y₁ y₂ ↦ y₁ ^⋏[π₁ param] y₂
  or (param) := fun _ _ _ y₁ y₂ ↦ y₁ ^⋎[π₁ param] y₂
  all (param) := fun _ _ y₁ ↦ ^∀[π₁ param] y₁
  ex (param) := fun _ _ y₁ ↦ ^∃[π₁ param] y₁
  allChanges (param n) := ⟪π₁ param + 1, L.qVec n (π₁ param) (π₂ param)⟫
  exChanges (param n) := ⟪π₁ param + 1, L.qVec n (π₁ param) (π₂ param)⟫
  rel_defined := by intro v; simp [blueprint, (termSubstVec_defined L).df.iff]; rfl
  nrel_defined := by intro v; simp [blueprint, (termSubstVec_defined L).df.iff]; rfl
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]; rfl
  or_defined := by intro v; simp [blueprint]; rfl
  all_defined := by intro v; simp [blueprint]; rfl
  ex_defined := by intro v; simp [blueprint]; rfl
  allChanges_defined := by intro v; simp [blueprint, (qVec_defined L).df.iff]
  exChanges_defined := by intro v; simp [blueprint, (qVec_defined L).df.iff]

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

@[simp] lemma substs_rel {n k R v} (hR : L.Rel k R) (hv : L.SemitermVec k n v) :
    L.substs m w (^rel n k R v) = ^rel m k R (L.termSubstVec k n m w v) := by simp [Language.substs, hR, hv, construction]

@[simp] lemma substs_nrel {n k R v} (hR : L.Rel k R) (hv : L.SemitermVec k n v) :
    L.substs m w (^nrel n k R v) = ^nrel m k R (L.termSubstVec k n m w v) := by simp [Language.substs, hR, hv, construction]

@[simp] lemma substs_verum (n) :
    L.substs m w ^⊤[n] = ^⊤[m] := by simp [Language.substs, construction]

@[simp] lemma substs_falsum (n) :
    L.substs m w ^⊥[n] = ^⊥[m] := by simp [Language.substs, construction]

@[simp] lemma substs_and {n p q} (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    L.substs m w (p ^⋏[n] q) = L.substs m w p ^⋏[m] L.substs m w q := by simp [Language.substs, hp, hq, construction]

@[simp] lemma substs_or {n p q} (hp : L.Semiformula n p) (hq : L.Semiformula n q) :
    L.substs m w (p ^⋎[n] q) = L.substs m w p ^⋎[m] L.substs m w q := by simp [Language.substs, hp, hq, construction]

@[simp] lemma substs_all {n p} (hp : L.Semiformula (n + 1) p) :
    L.substs m w (^∀[n] p) = ^∀[m] (L.substs (m + 1) (L.qVec n m w) p) := by simp [Language.substs, hp, construction]

@[simp] lemma substs_ex {n p} (hp : L.Semiformula (n + 1) p) :
    L.substs m w (^∃[n] p) = ^∃[m] (L.substs (m + 1) (L.qVec n m w) p) := by simp [Language.substs, hp, construction]

lemma uformula_subst_induction {P : V → V → V → V → Prop} (hP : 𝚺₁-Relation₄ P)
    (hRel : ∀ n m w k R v, L.Rel k R → L.SemitermVec k n v → P m w (^rel n k R v) (^rel m k R (L.termSubstVec k n m w v)))
    (hNRel : ∀ n m w k R v, L.Rel k R → L.SemitermVec k n v → P m w (^nrel n k R v) (^nrel m k R (L.termSubstVec k n m w v)))
    (hverum : ∀ n m w, P m w (^⊤[n]) (^⊤[m]))
    (hfalsum : ∀ n m w, P m w (^⊥[n]) (^⊥[m]))
    (hand : ∀ n m w p q, L.Semiformula n p → L.Semiformula n q →
      P m w p (L.substs m w p) → P m w q (L.substs m w q) → P m w (p ^⋏[n] q) (L.substs m w p ^⋏[m] L.substs m w q))
    (hor : ∀ n m w p q, L.Semiformula n p → L.Semiformula n q →
      P m w p (L.substs m w p) → P m w q (L.substs m w q) → P m w (p ^⋎[n] q) (L.substs m w p ^⋎[m] L.substs m w q))
    (hall : ∀ n m w p, L.Semiformula (n + 1) p →
      P (m + 1) (L.qVec n m w) p (L.substs (m + 1) (L.qVec n m w) p) →
      P m w (^∀[n] p) (^∀[m] (L.substs (m + 1) (L.qVec n m w) p)))
    (hex : ∀ n m w p, L.Semiformula (n + 1) p →
      P (m + 1) (L.qVec n m w) p (L.substs (m + 1) (L.qVec n m w) p) →
      P m w (^∃[n] p) (^∃[m] (L.substs (m + 1) (L.qVec n m w) p))) :
    ∀ {p m w}, L.UFormula p → P m w p (L.substs m w p) := by
  suffices ∀ param p, L.UFormula p → P (π₁ param) (π₂ param) p ((construction L).result param p) by
    intro p m w hp; simpa using this ⟪m, w⟫ p hp
  apply (construction L).uformula_result_induction (P := fun param p y ↦ P (π₁ param) (π₂ param) p y)
  · apply Definable.comp₄_infer
      (DefinableFunction.comp₁_infer (DefinableFunction.var _))
      (DefinableFunction.comp₁_infer (DefinableFunction.var _))
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

lemma semiformula_subst_induction {P : V → V → V → V → V → Prop} (hP : 𝚺₁-Relation₅ P)
    (hRel : ∀ n m w k R v, L.Rel k R → L.SemitermVec k n v → P n m w (^rel n k R v) (^rel m k R (L.termSubstVec k n m w v)))
    (hNRel : ∀ n m w k R v, L.Rel k R → L.SemitermVec k n v → P n m w (^nrel n k R v) (^nrel m k R (L.termSubstVec k n m w v)))
    (hverum : ∀ n m w, P n m w (^⊤[n]) (^⊤[m]))
    (hfalsum : ∀ n m w, P n m w (^⊥[n]) (^⊥[m]))
    (hand : ∀ n m w p q, L.Semiformula n p → L.Semiformula n q →
      P n m w p (L.substs m w p) → P n m w q (L.substs m w q) → P n m w (p ^⋏[n] q) (L.substs m w p ^⋏[m] L.substs m w q))
    (hor : ∀ n m w p q, L.Semiformula n p → L.Semiformula n q →
      P n m w p (L.substs m w p) → P n m w q (L.substs m w q) → P n m w (p ^⋎[n] q) (L.substs m w p ^⋎[m] L.substs m w q))
    (hall : ∀ n m w p, L.Semiformula (n + 1) p →
      P (n + 1) (m + 1) (L.qVec n m w) p (L.substs (m + 1) (L.qVec n m w) p) →
      P n m w (^∀[n] p) (^∀[m] (L.substs (m + 1) (L.qVec n m w) p)))
    (hex : ∀ n m w p, L.Semiformula (n + 1) p →
      P (n + 1) (m + 1) (L.qVec n m w) p (L.substs (m + 1) (L.qVec n m w) p) →
      P n m w (^∃[n] p) (^∃[m] (L.substs (m + 1) (L.qVec n m w) p))) :
    ∀ {n p m w}, L.Semiformula n p → P n m w p (L.substs m w p) := by
  suffices ∀ param n p, L.Semiformula n p → P n (π₁ param) (π₂ param) p ((construction L).result param p) by
    intro n p m w hp; simpa using this ⟪m, w⟫ n p hp
  apply (construction L).semiformula_result_induction (P := fun param n p y ↦ P n (π₁ param) (π₂ param) p y)
  · apply Definable.comp₅_infer
      (DefinableFunction.var _)
      (DefinableFunction.comp₁_infer (DefinableFunction.var _))
      (DefinableFunction.comp₁_infer (DefinableFunction.var _))
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
    L.Semiformula n p → L.SemitermVec n m w → L.Semiformula m (L.substs m w p) := by
  apply semiformula_subst_induction (P := fun n m w _ y ↦ L.SemitermVec n m w → L.Semiformula m y)
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
    simpa using ih hw.qVec
  case hex =>
    intro n m w p _ ih hw
    simpa using ih hw.qVec

lemma substs_not_uformula {m w x} (h : ¬L.UFormula x) :
    L.substs m w x = 0 := (construction L).result_prop_not _ h

lemma substs_neg {p} (hp : L.Semiformula n p) :
    L.SemitermVec n m w → L.substs m w (L.neg p) = L.neg (L.substs m w p) := by
  revert m w
  apply Language.Semiformula.induction_pi₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ hp
  · definability
  · intros; simp [*]
  · intros; simp [*]
  · intros; simp [*]
  · intros; simp [*]
  · intro n p q hp hq ihp ihq m w hw
    simp [hp, hq, hw, hp.substs, hq.substs, ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    simp [hp, hq, hw, hp.substs, hq.substs, ihp hw, ihq hw]
  · intro n p hp ih m w hw
    simp [hp, hw, hp.substs hw.qVec, ih hw.qVec]
  · intro n p hp ih m w hw
    simp [hp, hw, hp.substs hw.qVec, ih hw.qVec]

lemma shift_substs {p} (hp : L.Semiformula n p) :
    L.SemitermVec n m w → L.shift (L.substs m w p) = L.substs m (L.termShiftVec n m w) (L.shift p) := by
  revert m w
  apply Language.Semiformula.induction_pi₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ hp
  · definability
  · intro n k R v hR hv m w hw
    simp only [substs_rel, Language.SemitermVec.termSubstVec, shift_rel,
      Language.SemitermVec.termShiftVec, qqRel_inj, true_and, hR, hv, hw]
    apply nth_ext' k (by simp [*]) (by simp [*])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv) hi,
      nth_termSubstVec hv hi,
      nth_termSubstVec hv.termShiftVec hi,
      nth_termShiftVec hv hi,
      termShift_termSubsts (hv.2 i hi) hw]
  · intro n k R v hR hv m w hw
    simp only [substs_nrel, Language.SemitermVec.termSubstVec, shift_nrel,
      Language.SemitermVec.termShiftVec, qqNRel_inj, true_and, hR, hv, hw]
    apply nth_ext' k (by simp [*]) (by simp [*])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv) hi,
      nth_termSubstVec hv hi,
      nth_termSubstVec hv.termShiftVec hi,
      nth_termShiftVec hv hi,
      termShift_termSubsts (hv.2 i hi) hw]
  · intro n w hw; simp
  · intro n w hw; simp
  · intro n p q hp hq ihp ihq m w hw
    simp [*]
    rw [shift_and (hp.substs hw) (hq.substs hw), ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    simp [*]
    rw [shift_or (hp.substs hw) (hq.substs hw), ihp hw, ihq hw]
  · intro n p hp ih m w hw
    simp only [substs_all, shift_all, Language.Semiformula.shift_iff, hp]
    rw [shift_all (hp.substs hw.qVec), ih hw.qVec, termShift_qVec hw]
  · intro n p hp ih m w hw
    simp only [substs_ex, shift_ex, Language.Semiformula.shift_iff, hp]
    rw [shift_ex (hp.substs hw.qVec), ih hw.qVec, termShift_qVec hw]

lemma substs_substs {p} (hp : L.Semiformula l p) :
    L.SemitermVec n m w → L.SemitermVec l n v → L.substs m w (L.substs n v p) = L.substs m (L.termSubstVec l n m w v) p := by
  revert m w n v
  apply Language.Semiformula.induction_pi₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ hp
  · apply Definable.all
    apply Definable.all
    apply Definable.all
    apply Definable.all
    apply Definable.imp (by definability)
    apply Definable.imp (by definability)
    apply Definable.comp₂_infer (by simp; definability)
    apply DefinableFunction.comp₃_infer (by definability) ?_ (by definability)
    apply DefinableFunction₅.comp (termSubstVec_definable _) <;> definability
  · intro l k R ts hR hts m w n v _ hv
    simp only [substs_rel, Language.SemitermVec.termSubstVec, qqRel_inj, true_and, hR, hts, hv]
    apply nth_ext' k (by simp [hv, hts]) (by simp [hts])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts) hi,
      nth_termSubstVec hts hi,
      nth_termSubstVec hts hi,
      termSubst_termSubst hv (hts.2 i hi)]
  · intro l k R ts hR hts m w n v _ hv
    simp only [substs_nrel, Language.SemitermVec.termSubstVec, qqNRel_inj, true_and, hR, hts, hv]
    apply nth_ext' k (by simp [hv, hts]) (by simp [hts])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts) hi,
      nth_termSubstVec hts hi,
      nth_termSubstVec hts hi,
      termSubst_termSubst hv (hts.2 i hi)]
  · intro l m w n v _ _; simp [*]
  · intro l m w n v _ _; simp [*]
  · intro l p q hp hq ihp ihq m w n v hw hv
    simp only [substs_and, hp, hq]
    rw [substs_and (hp.substs hv) (hq.substs hv), ihp hw hv, ihq hw hv]
  · intro l p q hp hq ihp ihq m w n v hw hv
    simp only [substs_or, hp, hq]
    rw [substs_or (hp.substs hv) (hq.substs hv), ihp hw hv, ihq hw hv]
  · intro l p hp ih m w n v hw hv
    simp only [substs_all, hp]
    rw [substs_all (hp.substs hv.qVec), ih hw.qVec hv.qVec, termSubstVec_qVec_qVec hv hw]
  · intro l p hp ih m w n v hw hv
    simp only [substs_ex, hp]
    rw [substs_ex (hp.substs hv.qVec), ih hw.qVec hv.qVec, termSubstVec_qVec_qVec hv hw]

lemma subst_eq_self {n w : V} (hp : L.Semiformula n p) (hw : L.SemitermVec n n w) (H : ∀ i < n, w.[i] = ^#i) :
    L.substs n w p = p := by
  revert w
  apply Language.Semiformula.induction_pi₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ hp
  · definability
  · intro n k R v hR hv w _ H
    simp only [substs_rel, qqRel_inj, true_and, hR, hv]
    apply nth_ext' k (by simp [*]) (by simp [hv.1])
    intro i hi
    rw [nth_termSubstVec hv hi, termSubst_eq_self (hv.2 i hi) H]
  · intro n k R v hR hv w _ H
    simp only [substs_nrel, qqNRel_inj, true_and, hR, hv]
    apply nth_ext' k (by simp [*]) (by simp [hv.1])
    intro i hi
    rw [nth_termSubstVec hv hi, termSubst_eq_self (hv.2 i hi) H]
  · intro n w _ _; simp
  · intro n w _ _; simp
  · intro n p q hp hq ihp ihq w hw H
    simp [*, ihp hw H, ihq hw H]
  · intro n p q hp hq ihp ihq w hw H
    simp [*, ihp hw H, ihq hw H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (L.qVec n n w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [Language.qVec]
      · have hi : i < n := by simpa using hi
        simp only [Language.qVec, nth_cons_succ]
        rw [nth_termBShiftVec hw hi]
        simp [H i hi, hi]
    simp [*, ih hw.qVec H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (L.qVec n n w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [Language.qVec]
      · have hi : i < n := by simpa using hi
        simp only [Language.qVec, nth_cons_succ]
        rw [nth_termBShiftVec hw hi]
        simp [H i hi, hi]
    simp [*, ih hw.qVec H]

end substs


variable (L)

def Language.substs₁ (t u : V) : V := L.substs 0 ?[t] u

variable {L}

section substs₁

section

def _root_.LO.FirstOrder.Arith.LDef.substs₁Def (pL : LDef) : 𝚺₁-Semisentence 3 := .mkSigma
  “ z t p | ∃ v, !consDef v t 0 ∧ !pL.substsDef z 0 v p” (by simp)

variable (L)

lemma substs₁_defined : 𝚺₁-Function₂ L.substs₁ via pL.substs₁Def := by
  intro v; simp [LDef.substs₁Def, (substs_defined L).df.iff]; rfl

@[simp] instance substs₁_definable : 𝚺₁-Function₂ L.substs₁ := Defined.to_definable _ (substs₁_defined L)

end

lemma Language.Semiformula.substs₁ (ht : L.Term t) (hp : L.Semiformula 1 p) : L.Semiformula 0 (L.substs₁ t p) :=
  Language.Semiformula.substs hp (by simp [ht])

end substs₁

variable (L)

def Language.free (p : V) : V := L.substs₁ ^&0 (L.shift p)

variable {L}

section free

section

def _root_.LO.FirstOrder.Arith.LDef.freeDef (pL : LDef) : 𝚺₁-Semisentence 2 := .mkSigma
  “q p | ∃ fz, !qqFvarDef fz 0 ∧ ∃ sp, !pL.shiftDef sp p ∧ !pL.substs₁Def q fz sp” (by simp)

variable (L)

lemma free_defined : 𝚺₁-Function₁ L.free via pL.freeDef := by
  intro v; simp [LDef.freeDef, (shift_defined L).df.iff, (substs₁_defined L).df.iff, Language.free]

@[simp] instance free_definable : 𝚺₁-Function₁ L.free := Defined.to_definable _ (free_defined L)

end

@[simp] lemma Language.Semiformula.free (hp : L.Semiformula 1 p) : L.Formula (L.free p) :=
  Language.Semiformula.substs₁ (by simp) (by simp [hp])

end free

section fvfree

variable (L)

def Language.IsFVFree (n p : V) : Prop := L.Semiformula n p ∧ L.shift p = p

section

def _root_.LO.FirstOrder.Arith.LDef.isFVFreeDef (pL : LDef) : 𝚺₁-Semisentence 2 :=
  .mkSigma “n p | !pL.isSemiformulaDef.sigma n p ∧ !pL.shiftDef p p” (by simp)

lemma isFVFree_defined : 𝚺₁-Relation L.IsFVFree via pL.isFVFreeDef := by
  intro v; simp [LDef.isFVFreeDef, HSemiformula.val_sigma, (semiformula_defined L).df.iff, (shift_defined L).df.iff]
  simp [Language.IsFVFree, eq_comm]

end

variable {L}

@[simp] lemma Language.IsFVFree.verum (n : V) : L.IsFVFree n ^⊤[n] := by simp [Language.IsFVFree]

@[simp] lemma Language.IsFVFree.falsum (n : V) : L.IsFVFree n ^⊥[n] := by simp [Language.IsFVFree]

lemma Language.IsFVFree.and {n p q : V} (hp : L.IsFVFree n p) (hq : L.IsFVFree n q) :
    L.IsFVFree n (p ^⋏[n] q) := by simp [Language.IsFVFree, hp.1, hq.1, hp.2, hq.2]

lemma Language.IsFVFree.or {n p q : V} (hp : L.IsFVFree n p) (hq : L.IsFVFree n q) :
    L.IsFVFree n (p ^⋎[n] q) := by simp [Language.IsFVFree, hp.1, hq.1, hp.2, hq.2]

lemma Language.IsFVFree.all {n p : V} (hp : L.IsFVFree (n + 1) p) :
    L.IsFVFree n (^∀[n] p) := by simp [Language.IsFVFree, hp.1, hp.2]

lemma Language.IsFVFree.ex {n p : V} (hp : L.IsFVFree (n + 1) p) :
    L.IsFVFree n (^∃[n] p) := by simp [Language.IsFVFree, hp.1, hp.2]

@[simp] lemma Language.IsFVFree.neg_iff : L.IsFVFree n (L.neg p) ↔ L.IsFVFree n p := by
  constructor
  · intro h
    have hp : L.Semiformula n p := Language.Semiformula.neg_iff.mp h.1
    have : L.shift (L.neg p) = L.neg p := h.2
    simp [shift_neg hp, neg_inj_iff hp.shift hp] at this
    exact ⟨hp, this⟩
  · intro h; exact ⟨by simp [h.1], by rw [shift_neg h.1, h.2]⟩

end fvfree

namespace Formalized

def qqEQ (n x y : V) : V := ^rel n 2 (eqIndex : V) ?[x, y]

def qqNEQ (n x y : V) : V := ^nrel n 2 (eqIndex : V) ?[x, y]

def qqLT (n x y : V) : V := ^rel n 2 (ltIndex : V) ?[x, y]

def qqNLT (n x y : V) : V := ^nrel n 2 (ltIndex : V) ?[x, y]

notation:75 x:75 " ^=[" n "] " y:76 => qqEQ n x y

notation:75 x:75 " ^= " y:76 => qqEQ 0 x y

notation:75 x:75 " ^≠[" n "] " y:76 => qqNEQ n x y

notation:75 x:75 " ^≠ " y:76 => qqNEQ 0 x y

notation:78 x:78 " ^<[" n "] " y:79 => qqLT n x y

notation:78 x:78 " ^< " y:79 => qqLT 0 x y

notation:78 x:78 " ^≮[" n "] " y:79 => qqNLT n x y

notation:78 x:78 " ^≮ " y:79 => qqNLT 0 x y

def _root_.LO.FirstOrder.Arith.qqEQDef : 𝚺₁-Semisentence 4 :=
  .mkSigma “p n x y | ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p n 2 (!(.Operator.numeral ℒₒᵣ eqIndex)) v” (by simp)

def _root_.LO.FirstOrder.Arith.qqNEQDef : 𝚺₁-Semisentence 4 :=
  .mkSigma “p n x y | ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p n 2 (!(.Operator.numeral ℒₒᵣ eqIndex)) v” (by simp)

def _root_.LO.FirstOrder.Arith.qqLTDef : 𝚺₁-Semisentence 4 :=
  .mkSigma “p n x y | ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p n 2 (!(.Operator.numeral ℒₒᵣ ltIndex)) v” (by simp)

def _root_.LO.FirstOrder.Arith.qqNLTDef : 𝚺₁-Semisentence 4 :=
  .mkSigma “p n x y | ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p n 2 (!(.Operator.numeral ℒₒᵣ ltIndex)) v” (by simp)

lemma qqEQ_defined : 𝚺₁-Function₃ (qqEQ : V → V → V → V) via qqEQDef := by
  intro v; simp [qqEQDef, numeral_eq_natCast, qqEQ]

lemma qqNEQ_defined : 𝚺₁-Function₃ (qqNEQ : V → V → V → V) via qqNEQDef := by
  intro v; simp [qqNEQDef, numeral_eq_natCast, qqNEQ]

lemma qqLT_defined : 𝚺₁-Function₃ (qqLT : V → V → V → V) via qqLTDef := by
  intro v; simp [qqLTDef, numeral_eq_natCast, qqLT]

lemma qqNLT_defined : 𝚺₁-Function₃ (qqNLT : V → V → V → V) via qqNLTDef := by
  intro v; simp [qqNLTDef, numeral_eq_natCast, qqNLT]

@[simp] lemma eval_qqEQDef (v) : Semiformula.Evalbm V v qqEQDef.val ↔ v 0 = v 2 ^=[v 1] v 3 := qqEQ_defined.df.iff v

@[simp] lemma eval_qqNEQDef (v) : Semiformula.Evalbm V v qqNEQDef.val ↔ v 0 = v 2 ^≠[v 1] v 3 := qqNEQ_defined.df.iff v

@[simp] lemma eval_qqLTDef (v) : Semiformula.Evalbm V v qqLTDef.val ↔ v 0 = v 2 ^<[v 1] v 3 := qqLT_defined.df.iff v

@[simp] lemma eval_qqNLTDef (v) : Semiformula.Evalbm V v qqNLTDef.val ↔ v 0 = v 2 ^≮[v 1] v 3 := qqNLT_defined.df.iff v

end Formalized

end LO.Arith

end
