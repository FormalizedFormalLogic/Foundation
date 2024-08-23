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
  rel := .mkSigma “y param k R v | !qqNRelDef y k R v” (by simp)
  nrel := .mkSigma “y param k R v | !qqRelDef y k R v” (by simp)
  verum := .mkSigma “y param | !qqFalsumDef y” (by simp)
  falsum := .mkSigma “y param | !qqVerumDef y” (by simp)
  and := .mkSigma “y param p₁ p₂ y₁ y₂ | !qqOrDef y y₁ y₂” (by simp)
  or := .mkSigma “y param p₁ p₂ y₁ y₂ | !qqAndDef y y₁ y₂” (by simp)
  all := .mkSigma “y param p₁ y₁ | !qqExDef y y₁” (by simp)
  ex := .mkSigma “y param p₁ y₁ | !qqAllDef y y₁” (by simp)
  allChanges := .mkSigma “param' param | param' = 0” (by simp)
  exChanges := .mkSigma “param' param | param' = 0” (by simp)

variable (L)

def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel {_} := fun k R v ↦ ^nrel k R v
  nrel {_} := fun k R v ↦ ^rel k R v
  verum {_} := ^⊥
  falsum {_} := ^⊤
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  all {_} := fun _ y₁ ↦ ^∃ y₁
  ex {_} := fun _ y₁ ↦ ^∀ y₁
  allChanges := fun _ ↦ 0
  exChanges := fun _ ↦ 0
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

def _root_.LO.FirstOrder.Arith.LDef.negDef (pL : LDef) : 𝚺₁.Semisentence 2 := (blueprint pL).result.rew (Rew.substs ![#0, ‘0’, #1])

variable (L)

lemma Language.neg_defined : 𝚺₁-Function₁ L.neg via pL.negDef := fun v ↦ by
  simpa [LDef.negDef] using (construction L).result_defined ![v 0, 0, v 1]

instance Language.neg_definable : 𝚺₁-Function₁ L.neg := L.neg_defined.to_definable

instance Language.neg_definable' (Γ) : Γ-[m + 1]-Function₁ L.neg :=
  .of_sigmaOne (neg_definable L)

end

@[simp] lemma neg_rel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.neg (^rel k R v) = ^nrel k R v := by simp [Language.neg, hR, hv, construction]

@[simp] lemma neg_nrel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.neg (^nrel k R v) = ^rel k R v := by simp [Language.neg, hR, hv, construction]

@[simp] lemma neg_verum :
    L.neg ^⊤ = ^⊥ := by simp [Language.neg, construction]

@[simp] lemma neg_falsum :
    L.neg ^⊥ = ^⊤ := by simp [Language.neg, construction]

@[simp] lemma neg_and {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.neg (p ^⋏ q) = L.neg p ^⋎ L.neg q := by simp [Language.neg, hp, hq, construction]

@[simp] lemma neg_or {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.neg (p ^⋎ q) = L.neg p ^⋏ L.neg q := by simp [Language.neg, hp, hq, construction]

@[simp] lemma neg_all {p} (hp : L.IsUFormula p) :
    L.neg (^∀ p) = ^∃ (L.neg p) := by simp [Language.neg, hp, construction]

@[simp] lemma neg_ex {p} (hp : L.IsUFormula p) :
    L.neg (^∃ p) = ^∀ (L.neg p) := by simp [Language.neg, hp, construction]

lemma neg_not_uformula {x} (h : ¬L.IsUFormula x) :
    L.neg x = 0 := (construction L).result_prop_not _ h

lemma Language.IsUFormula.neg {p : V} : L.IsUFormula p → L.IsUFormula (L.neg p) := by
  apply Language.IsUFormula.induction_sigma1
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

@[simp] lemma Language.IsUFormula.bv_neg {p : V} : L.IsUFormula p → L.bv (L.neg p) = L.bv p := by
  apply Language.IsUFormula.induction_sigma1
  · definability
  · intro k R v hR hv; simp [*]
  · intro k R v hR hv; simp [*]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

@[simp] lemma Language.IsUFormula.neg_neg {p : V} : L.IsUFormula p → L.neg (L.neg p) = p := by
  apply Language.IsUFormula.induction_sigma1
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

@[simp] lemma Language.IsUFormula.neg_iff {p : V} : L.IsUFormula (L.neg p) ↔ L.IsUFormula p := by
  constructor
  · intro h; by_contra hp
    have Hp : L.IsUFormula p := by by_contra hp; simp [neg_not_uformula hp] at h
    contradiction
  · exact Language.IsUFormula.neg

@[simp] lemma Language.IsSemiformula.neg_iff {p : V} : L.IsSemiformula n (L.neg p) ↔ L.IsSemiformula n p := by
  constructor
  · intro h; by_contra hp
    have Hp : L.IsUFormula p := by by_contra hp; simp [neg_not_uformula hp] at h
    have : L.IsSemiformula n p := ⟨Hp, by simpa [Hp.bv_neg] using h.bv⟩
    contradiction
  · intro h; exact ⟨by simp [h.isUFormula], by simpa [h.isUFormula] using h.bv⟩

alias ⟨Language.IsSemiformula.elim_neg, Language.IsSemiformula.neg⟩ := Language.IsSemiformula.neg_iff

@[simp] lemma neg_inj_iff (hp : L.IsUFormula p) (hq : L.IsUFormula q) : L.neg p = L.neg q ↔ p = q := by
  constructor
  · intro h; simpa [hp.neg_neg, hq.neg_neg] using congrArg L.neg h
  · rintro rfl; rfl

end negation

variable (L)

def Language.imp (p q : V) : V := L.neg p ^⋎ q

notation:60 p:61 " ^→[" L "] " q:60 => Language.imp L p q

variable {L}

section imp

@[simp] lemma Language.IsUFormula.imp {p q : V} :
    L.IsUFormula (L.imp p q) ↔ L.IsUFormula p ∧ L.IsUFormula q := by
  simp [Language.imp]

@[simp] lemma Language.IsSemiformula.imp {n p q : V} :
    L.IsSemiformula n (L.imp p q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q := by
  simp [Language.imp]

section

def _root_.LO.FirstOrder.Arith.LDef.impDef (pL : LDef) : 𝚺₁.Semisentence 3 := .mkSigma
  “r p q | ∃ np, !pL.negDef np p ∧ !qqOrDef r np q” (by simp)

variable (L)

lemma Language.imp_defined : 𝚺₁-Function₂ L.imp via pL.impDef := fun v ↦ by
  simp [LDef.impDef, L.neg_defined.df.iff]; rfl

instance Language.imp_definable : 𝚺₁-Function₂ L.imp := L.imp_defined.to_definable

instance imp_definable' : Γ-[m + 1]-Function₂ L.imp := L.imp_definable.of_sigmaOne

end

end imp

section shift

namespace Shift

def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel := .mkSigma “y param k R v | ∃ v', !pL.termShiftVecDef v' k v ∧ !qqRelDef y k R v'” (by simp)
  nrel := .mkSigma “y param k R v | ∃ v', !pL.termShiftVecDef v' k v ∧ !qqNRelDef y k R v'” (by simp)
  verum := .mkSigma “y param | !qqVerumDef y” (by simp)
  falsum := .mkSigma “y param | !qqFalsumDef y” (by simp)
  and := .mkSigma “y param p₁ p₂ y₁ y₂ | !qqAndDef y y₁ y₂” (by simp)
  or := .mkSigma “y param p₁ p₂ y₁ y₂ | !qqOrDef y y₁ y₂” (by simp)
  all := .mkSigma “y param p₁ y₁ | !qqAllDef y y₁” (by simp)
  ex := .mkSigma “y param p₁ y₁ | !qqExDef y y₁” (by simp)
  allChanges := .mkSigma “param' param | param' = 0” (by simp)
  exChanges := .mkSigma “param' param | param' = 0” (by simp)

variable (L)

def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel {_} := fun k R v ↦ ^rel k R (L.termShiftVec k v)
  nrel {_} := fun k R v ↦ ^nrel k R (L.termShiftVec k v)
  verum {_} := ^⊤
  falsum {_} := ^⊥
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all {_} := fun _ y₁ ↦ ^∀ y₁
  ex {_} := fun _ y₁ ↦ ^∃ y₁
  allChanges := fun _ ↦ 0
  exChanges := fun _ ↦ 0
  rel_defined := by intro v; simp [blueprint, L.termShiftVec_defined.df.iff]; rfl
  nrel_defined := by intro v; simp [blueprint, L.termShiftVec_defined.df.iff]; rfl
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

def _root_.LO.FirstOrder.Arith.LDef.shiftDef (pL : LDef) : 𝚺₁.Semisentence 2 := (blueprint pL).result.rew (Rew.substs ![#0, ‘0’, #1])

variable (L)

lemma Language.shift_defined : 𝚺₁-Function₁ L.shift via pL.shiftDef := fun v ↦ by
  simpa [LDef.shiftDef] using (construction L).result_defined ![v 0, 0, v 1]

instance Language.shift_definable : 𝚺₁-Function₁ L.shift := L.shift_defined.to_definable

instance language.shift_definable' : Γ-[m + 1]-Function₁ L.shift := L.shift_definable.of_sigmaOne

end

@[simp] lemma shift_rel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.shift (^relk R v) = ^relk R (L.termShiftVec k v) := by simp [Language.shift, hR, hv, construction]

@[simp] lemma shift_nrel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.shift (^nrelk R v) = ^nrelk R (L.termShiftVec k v) := by simp [Language.shift, hR, hv, construction]

@[simp] lemma shift_verum : L.shift ^⊤ = ^⊤ := by simp [Language.shift, construction]

@[simp] lemma shift_falsum : L.shift ^⊥ = ^⊥ := by simp [Language.shift, construction]

@[simp] lemma shift_and {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.shift (p ^⋏ q) = L.shift p ^⋏ L.shift q := by simp [Language.shift, hp, hq, construction]

@[simp] lemma shift_or {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.shift (p ^⋎ q) = L.shift p ^⋎ L.shift q := by simp [Language.shift, hp, hq, construction]

@[simp] lemma shift_all {p} (hp : L.IsUFormula p) :
    L.shift (^∀ p) = ^∀ (L.shift p) := by simp [Language.shift, hp, construction]

@[simp] lemma shift_ex {p} (hp : L.IsUFormula p) :
    L.shift (^∃ p) = ^∃ (L.shift p) := by simp [Language.shift, hp, construction]

lemma shift_not_uformula {x} (h : ¬L.IsUFormula x) :
    L.shift x = 0 := (construction L).result_prop_not _ h

lemma Language.IsUFormula.shift {p : V} : L.IsUFormula p → L.IsUFormula (L.shift p) := by
  apply Language.IsUFormula.induction_sigma1
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

lemma Language.IsUFormula.bv_shift {p : V} : L.IsUFormula p → L.bv (L.shift p) = L.bv p := by
  apply Language.IsUFormula.induction_sigma1
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq, hp.shift, hq.shift]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq, hp.shift, hq.shift]
  · intro p hp ihp; simp [hp, hp.neg, ihp, hp.shift]
  · intro p hp ihp; simp [hp, hp.neg, ihp, hp.shift]

lemma Language.IsSemiformula.shift {p : V} : L.IsSemiformula n p → L.IsSemiformula n (L.shift p) := by
  apply Language.IsSemiformula.induction_sigma1
  · definability
  · intro n k r v hr hv; simp [hr, hv, hv.isUTerm]
  · intro n k r v hr hv; simp [hr, hv, hv.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp, hq, hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp, hq, hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp; simp [hp, hp.isUFormula, ihp]
  · intro n p hp ihp; simp [hp, hp.isUFormula, ihp]


@[simp] lemma Language.IsSemiformula.shift_iff {p : V} : L.IsSemiformula n (L.shift p) ↔ L.IsSemiformula n p :=
  ⟨fun h ↦ by
    have : L.IsUFormula p := by by_contra hp; simp [shift_not_uformula hp] at h
    exact ⟨this, by simpa [this.bv_shift] using h.bv⟩,
    Language.IsSemiformula.shift⟩

lemma shift_neg {p : V} (hp : L.IsSemiformula n p) : L.shift (L.neg p) = L.neg (L.shift p) := by
  apply Language.IsSemiformula.induction_sigma1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv; simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm]
  · intro n k R v hR hv; simp [hR, hv.isUTerm, hv.termShiftVec.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, hp.shift.isUFormula, hq.shift.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, hp.shift.isUFormula, hq.shift.isUFormula, ihp, ihq]
  · intro n p hp ih; simp [hp.isUFormula, hp.shift.isUFormula, ih]
  · intro n p hp ih; simp [hp.isUFormula, hp.shift.isUFormula, ih]

end shift

section substs

section

variable (L)

def _root_.LO.FirstOrder.Arith.LDef.qVecDef (pL : LDef) : 𝚺₁.Semisentence 2 := .mkSigma
  “w' w | ∃ k, !lenDef k w ∧ ∃ sw, !pL.termBShiftVecDef sw k w ∧ ∃ t, !qqBvarDef t 0 ∧ !consDef w' t sw” (by simp)

lemma Language.qVec_defined : 𝚺₁-Function₁ L.qVec via pL.qVecDef := by
  intro v; simp [LDef.qVecDef, L.termBShiftVec_defined.df.iff]; rfl

instance Language.qVec_definable : 𝚺₁-Function₁ L.qVec := L.qVec_defined.to_definable

instance Language.qVec_definable' : Γ-[m + 1]-Function₁ L.qVec := L.qVec_definable.of_sigmaOne

end

namespace Substs

def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel    := .mkSigma “y param k R v | ∃ v', !pL.termSubstVecDef v' k param v ∧ !qqRelDef y k R v'” (by simp)
  nrel   := .mkSigma “y param k R v | ∃ v', !pL.termSubstVecDef v' k param v ∧ !qqNRelDef y k R v'” (by simp)
  verum  := .mkSigma “y param | !qqVerumDef y” (by simp)
  falsum := .mkSigma “y param | !qqFalsumDef y” (by simp)
  and    := .mkSigma “y param p₁ p₂ y₁ y₂ | !qqAndDef y y₁ y₂” (by simp)
  or     := .mkSigma “y param p₁ p₂ y₁ y₂ | !qqOrDef y y₁ y₂” (by simp)
  all    := .mkSigma “y param p₁ y₁ | !qqAllDef y y₁” (by simp)
  ex     := .mkSigma “y param p₁ y₁ | !qqExDef y y₁” (by simp)
  allChanges := .mkSigma “param' param | !pL.qVecDef param' param” (by simp)
  exChanges  := .mkSigma “param' param | !pL.qVecDef param' param” (by simp)

variable (L)

def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel (param)  := fun k R v ↦ ^rel k R (L.termSubstVec k param v)
  nrel (param) := fun k R v ↦ ^nrel k R (L.termSubstVec k param v)
  verum _      := ^⊤
  falsum _     := ^⊥
  and _        := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or _         := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all _        := fun _ y₁ ↦ ^∀ y₁
  ex _         := fun _ y₁ ↦ ^∃ y₁
  allChanges (param) := L.qVec param
  exChanges (param) := L.qVec param
  rel_defined := by intro v; simp [blueprint, L.termSubstVec_defined.df.iff]; rfl
  nrel_defined := by intro v; simp [blueprint, L.termSubstVec_defined.df.iff]; rfl
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]; rfl
  or_defined := by intro v; simp [blueprint]; rfl
  all_defined := by intro v; simp [blueprint]; rfl
  ex_defined := by intro v; simp [blueprint]; rfl
  allChanges_defined := by intro v; simp [blueprint, L.qVec_defined.df.iff]
  exChanges_defined := by intro v; simp [blueprint, L.qVec_defined.df.iff]

end Substs

open Substs

variable (L)

def Language.substs (w p : V) : V := (construction L).result w p

variable {L}

section

def _root_.LO.FirstOrder.Arith.LDef.substsDef (pL : LDef) : 𝚺₁.Semisentence 3 := (blueprint pL).result

variable (L)

lemma Language.substs_defined : 𝚺₁-Function₂ L.substs via pL.substsDef := (construction L).result_defined

instance Language.substs_definable : 𝚺₁-Function₂ L.substs := L.substs_defined.to_definable

instance Language.substs_definable' : Γ-[m + 1]-Function₂ L.substs := L.substs_definable.of_sigmaOne

end

variable {m w : V}

@[simp] lemma substs_rel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.substs w (^relk R v) = ^rel k R (L.termSubstVec k w v) := by simp [Language.substs, hR, hv, construction]

@[simp] lemma substs_nrel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.substs w (^nrelk R v) = ^nrel k R (L.termSubstVec k w v) := by simp [Language.substs, hR, hv, construction]

@[simp] lemma substs_verum (w) : L.substs w ^⊤ = ^⊤ := by simp [Language.substs, construction]

@[simp] lemma substs_falsum (w) : L.substs w ^⊥ = ^⊥ := by simp [Language.substs, construction]

@[simp] lemma substs_and {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.substs w (p ^⋏ q) = L.substs w p ^⋏ L.substs w q := by simp [Language.substs, hp, hq, construction]

@[simp] lemma substs_or {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.substs w (p ^⋎ q) = L.substs w p ^⋎ L.substs w q := by simp [Language.substs, hp, hq, construction]

@[simp] lemma substs_all {p} (hp : L.IsUFormula p) :
    L.substs w (^∀ p) = ^∀ (L.substs (L.qVec w) p) := by simp [Language.substs, hp, construction]

@[simp] lemma substs_ex {p} (hp : L.IsUFormula p) :
    L.substs w (^∃ p) = ^∃ (L.substs (L.qVec w) p) := by simp [Language.substs, hp, construction]

lemma isUFormula_subst_induction_sigma1 {P : V → V → V → Prop} (hP : 𝚺₁-Relation₃ P)
    (hRel : ∀ w k R v, L.Rel k R → L.IsUTermVec k v → P w (^relk R v) (^rel k R (L.termSubstVec k w v)))
    (hNRel : ∀ w k R v, L.Rel k R → L.IsUTermVec k v → P w (^nrelk R v) (^nrel k R (L.termSubstVec k w v)))
    (hverum : ∀ w, P w ^⊤ ^⊤)
    (hfalsum : ∀ w, P w ^⊥ ^⊥)
    (hand : ∀ w p q, L.IsUFormula p → L.IsUFormula q →
      P w p (L.substs w p) → P w q (L.substs w q) → P w (p ^⋏ q) (L.substs w p ^⋏ L.substs w q))
    (hor : ∀ w p q, L.IsUFormula p → L.IsUFormula q →
      P w p (L.substs w p) → P w q (L.substs w q) → P w (p ^⋎ q) (L.substs w p ^⋎ L.substs w q))
    (hall : ∀ w p, L.IsUFormula p → P (L.qVec w) p (L.substs (L.qVec w) p) → P w (^∀ p) (^∀ (L.substs (L.qVec w) p)))
    (hex : ∀ w p, L.IsUFormula p → P (L.qVec w) p (L.substs (L.qVec w) p) → P w (^∃ p) (^∃ (L.substs (L.qVec w) p))) :
    ∀ {w p}, L.IsUFormula p → P w p (L.substs w p) := by
  suffices ∀ param p, L.IsUFormula p → P param p ((construction L).result param p) by
    intro w p hp; simpa using this w p hp
  apply (construction L).uformula_result_induction (P := fun param p y ↦ P param p y)
  · definability
  · intro param k R v hkR hv; simpa using hRel param k R v hkR hv
  · intro param k R v hkR hv; simpa using hNRel param k R v hkR hv
  · intro param; simpa using hverum param
  · intro param; simpa using hfalsum param
  · intro param p q hp hq ihp ihq
    simpa [Language.substs] using
      hand param p q hp hq (by simpa [Language.substs] using ihp) (by simpa [Language.substs] using ihq)
  · intro param p q hp hq ihp ihq
    simpa [Language.substs] using
      hor param p q hp hq (by simpa [Language.substs] using ihp) (by simpa [Language.substs] using ihq)
  · intro param p hp ihp
    simpa using hall param p hp (by simpa [construction] using ihp)
  · intro param p hp ihp
    simpa using hex param p hp (by simpa [construction] using ihp)

lemma semiformula_subst_induction {P : V → V → V → V → Prop} (hP : 𝚺₁-Relation₄ P)
    (hRel : ∀ n w k R v, L.Rel k R → L.IsSemitermVec k n v → P n w (^relk R v) (^rel k R (L.termSubstVec k w v)))
    (hNRel : ∀ n w k R v, L.Rel k R → L.IsSemitermVec k n v → P n w (^nrelk R v) (^nrel k R (L.termSubstVec k w v)))
    (hverum : ∀ n w, P n w ^⊤ ^⊤)
    (hfalsum : ∀ n w, P n w ^⊥ ^⊥)
    (hand : ∀ n w p q, L.IsSemiformula n p → L.IsSemiformula n q →
      P n w p (L.substs w p) → P n w q (L.substs w q) → P n w (p ^⋏ q) (L.substs w p ^⋏ L.substs w q))
    (hor : ∀ n w p q, L.IsSemiformula n p → L.IsSemiformula n q →
      P n w p (L.substs w p) → P n w q (L.substs w q) → P n w (p ^⋎ q) (L.substs w p ^⋎ L.substs w q))
    (hall : ∀ n w p, L.IsSemiformula (n + 1) p →
      P (n + 1) (L.qVec w) p (L.substs (L.qVec w) p) → P n w (^∀ p) (^∀ (L.substs (L.qVec w) p)))
    (hex : ∀ n w p, L.IsSemiformula (n + 1) p →
      P (n + 1) (L.qVec w) p (L.substs (L.qVec w) p) → P n w (^∃ p) (^∃ (L.substs (L.qVec w) p))) :
    ∀ {n p w}, L.IsSemiformula n p → P n w p (L.substs w p) := by
  suffices ∀ param n p, L.IsSemiformula n p → P n param p ((construction L).result param p) by
    intro n p w hp; simpa using this w n p hp
  apply (construction L).semiformula_result_induction (P := fun param n p y ↦ P n param p y)
  · definability
  · intro n param k R v hkR hv; simpa using hRel n param k R v hkR hv
  · intro n param k R v hkR hv; simpa using hNRel n param k R v hkR hv
  · intro n param; simpa using hverum n param
  · intro n param; simpa using hfalsum n param
  · intro n param p q hp hq ihp ihq
    simpa [Language.substs] using
      hand n param p q hp hq (by simpa [Language.substs] using ihp) (by simpa [Language.substs] using ihq)
  · intro n param p q hp hq ihp ihq
    simpa [Language.substs] using
      hor n param p q hp hq (by simpa [Language.substs] using ihp) (by simpa [Language.substs] using ihq)
  · intro n param p hp ihp
    simpa using hall n param p hp (by simpa [construction] using ihp)
  · intro n param p hp ihp
    simpa using hex n param p hp (by simpa [construction] using ihp)

@[simp] lemma Language.IsSemiformula.substs {n p m w : V} :
    L.IsSemiformula n p → L.IsSemitermVec n m w → L.IsSemiformula m (L.substs w p) := by
  let fw : V → V → V → V → V := fun _ w _ _ ↦ Max.max w (L.qVec w)
  have hfw : 𝚺₁-Function₄ fw := by simp [fw]; definability
  let fn : V → V → V → V → V := fun _ _ n _ ↦ n + 1
  have hfn : 𝚺₁-Function₄ fn := by simp [fn]; definability
  let fm : V → V → V → V → V := fun _ _ _ m ↦ m + 1
  have hfm : 𝚺₁-Function₄ fm := by simp [fm]; definability
  apply order_ball_induction₃_sigma1 hfw hfn hfm ?_ ?_ p w n m
  · definability
  intro p w n m ih hp hw
  rcases Language.IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · simp [hR, hv.isUTerm, hw.termSubstVec hv]
  · simp [hR, hv.isUTerm, hw.termSubstVec hv]
  · simp
  · simp
  · have ih₁ : L.IsSemiformula m (L.substs w p₁) := ih p₁ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₁ hw
    have ih₂ : L.IsSemiformula m (L.substs w p₂) := ih p₂ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₂ hw
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · have ih₁ : L.IsSemiformula m (L.substs w p₁) := ih p₁ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₁ hw
    have ih₂ : L.IsSemiformula m (L.substs w p₂) := ih p₂ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₂ hw
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · simpa [h₁.isUFormula] using ih p₁ (by simp) (L.qVec w) (by simp [fw]) (n + 1) (by simp [fn]) (m + 1) (by simp [fm]) h₁ hw.qVec
  · simpa [h₁.isUFormula] using ih p₁ (by simp) (L.qVec w) (by simp [fw]) (n + 1) (by simp [fn]) (m + 1) (by simp [fm]) h₁ hw.qVec

lemma substs_not_uformula {w x} (h : ¬L.IsUFormula x) :
    L.substs w x = 0 := (construction L).result_prop_not _ h

lemma substs_neg {p} (hp : L.IsSemiformula n p) :
    L.IsSemitermVec n m w → L.substs w (L.neg p) = L.neg (L.substs w p) := by
  revert m w
  apply Language.IsSemiformula.induction_pi1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intros n k R v hR hv m w hw
    rw [neg_rel hR hv.isUTerm, substs_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm, neg_rel hR (hw.termSubstVec hv).isUTerm]
  · intros n k R v hR hv m w hw
    rw [neg_nrel hR hv.isUTerm, substs_rel hR hv.isUTerm, substs_nrel hR hv.isUTerm, neg_nrel hR (hw.termSubstVec hv).isUTerm]
  · intros; simp [*]
  · intros; simp [*]
  · intro n p q hp hq ihp ihq m w hw
    rw [neg_and hp.isUFormula hq.isUFormula,
      substs_or hp.neg.isUFormula hq.neg.isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      neg_and (hp.substs hw).isUFormula (hq.substs hw).isUFormula,
      ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    rw [neg_or hp.isUFormula hq.isUFormula,
      substs_and hp.neg.isUFormula hq.neg.isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      neg_or (hp.substs hw).isUFormula (hq.substs hw).isUFormula,
      ihp hw, ihq hw]
  · intro n p hp ih m w hw
    rw [neg_all hp.isUFormula, substs_ex hp.neg.isUFormula,
      substs_all hp.isUFormula, neg_all (hp.substs hw.qVec).isUFormula, ih hw.qVec]
  · intro n p hp ih m w hw
    rw [neg_ex hp.isUFormula, substs_all hp.neg.isUFormula,
      substs_ex hp.isUFormula, neg_ex (hp.substs hw.qVec).isUFormula, ih hw.qVec]

lemma shift_substs {p} (hp : L.IsSemiformula n p) :
    L.IsSemitermVec n m w → L.shift (L.substs w p) = L.substs (L.termShiftVec n w) (L.shift p) := by
  revert m w
  apply Language.IsSemiformula.induction_pi1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w hw
    rw [substs_rel hR hv.isUTerm,
      shift_rel hR (hw.termSubstVec hv).isUTerm,
      shift_rel hR hv.isUTerm,
      substs_rel hR hv.termShiftVec.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      termShift_termSubsts (hv.nth hi) hw]
  · intro n k R v hR hv m w hw
    rw [substs_nrel hR hv.isUTerm,
      shift_nrel hR (hw.termSubstVec hv).isUTerm,
      shift_nrel hR hv.isUTerm,
      substs_nrel hR hv.termShiftVec.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (by rw [len_termShiftVec (hw.termSubstVec hv).isUTerm])
      (by rw [len_termSubstVec hv.termShiftVec.isUTerm])
    intro i hi
    rw [nth_termShiftVec (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec hv.termShiftVec.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi,
      termShift_termSubsts (hv.nth hi) hw]
  · intro n w hw; simp
  · intro n w hw; simp
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_and hp.isUFormula hq.isUFormula,
      shift_and (hp.substs hw).isUFormula (hq.substs hw).isUFormula,
      shift_and hp.isUFormula hq.isUFormula,
      substs_and hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw, ihq hw]
  · intro n p q hp hq ihp ihq m w hw
    rw [substs_or hp.isUFormula hq.isUFormula,
      shift_or (hp.substs hw).isUFormula (hq.substs hw).isUFormula,
      shift_or hp.isUFormula hq.isUFormula,
      substs_or hp.shift.isUFormula hq.shift.isUFormula,
      ihp hw, ihq hw]
  · intro n p hp ih m w hw
    rw [substs_all hp.isUFormula,
      shift_all (hp.substs hw.qVec).isUFormula,
      shift_all hp.isUFormula,
      substs_all hp.shift.isUFormula,
      ih hw.qVec,
      termShift_qVec hw]
  · intro n p hp ih m w hw
    rw [substs_ex hp.isUFormula,
      shift_ex (hp.substs hw.qVec).isUFormula,
      shift_ex hp.isUFormula,
      substs_ex hp.shift.isUFormula,
      ih hw.qVec,
      termShift_qVec hw]

lemma substs_substs {p} (hp : L.IsSemiformula l p) :
    L.IsSemitermVec n m w → L.IsSemitermVec l n v → L.substs w (L.substs v p) = L.substs (L.termSubstVec l w v) p := by
  revert m w n v
  apply Language.IsSemiformula.induction_pi1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro l k R ts hR hts m w n v _ hv
    rw [substs_rel hR hts.isUTerm,
      substs_rel hR (hv.termSubstVec hts).isUTerm,
      substs_rel hR hts.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm]) (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      termSubst_termSubst hv (hts.nth hi)]
  · intro l k R ts hR hts m w n v _ hv
    rw [substs_nrel hR hts.isUTerm,
      substs_nrel hR (hv.termSubstVec hts).isUTerm,
      substs_nrel hR hts.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k (by rw [len_termSubstVec (hv.termSubstVec hts).isUTerm]) (by rw [len_termSubstVec hts.isUTerm])
    intro i hi
    rw [nth_termSubstVec (hv.termSubstVec hts).isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      nth_termSubstVec hts.isUTerm hi,
      termSubst_termSubst hv (hts.nth hi)]
  · intros; simp
  · intros; simp
  · intro l p q hp hq ihp ihq m w n v hw hv
    rw [substs_and hp.isUFormula hq.isUFormula,
      substs_and (hp.substs hv).isUFormula (hq.substs hv).isUFormula,
      substs_and hp.isUFormula hq.isUFormula,
      ihp hw hv, ihq hw hv]
  · intro l p q hp hq ihp ihq m w n v hw hv
    rw [substs_or hp.isUFormula hq.isUFormula,
      substs_or (hp.substs hv).isUFormula (hq.substs hv).isUFormula,
      substs_or hp.isUFormula hq.isUFormula,
      ihp hw hv, ihq hw hv]
  · intro l p hp ih m w n v hw hv
    rw [substs_all hp.isUFormula,
      substs_all (hp.substs hv.qVec).isUFormula,
      substs_all hp.isUFormula,
      ih hw.qVec hv.qVec,
      termSubstVec_qVec_qVec hv hw]
  · intro l p hp ih m w n v hw hv
    rw [substs_ex hp.isUFormula,
      substs_ex (hp.substs hv.qVec).isUFormula,
      substs_ex hp.isUFormula,
      ih hw.qVec hv.qVec,
      termSubstVec_qVec_qVec hv hw]

lemma subst_eq_self {n w : V} (hp : L.IsSemiformula n p) (hw : L.IsSemitermVec n n w) (H : ∀ i < n, w.[i] = ^#i) :
    L.substs w p = p := by
  revert w
  apply Language.IsSemiformula.induction_pi1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv w _ H
    simp only [substs_rel, qqRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n k R v hR hv w _ H
    simp only [substs_nrel, qqNRel_inj, true_and, hR, hv.isUTerm]
    apply nth_ext' k (by simp [*, hv.isUTerm]) (by simp [hv.lh])
    intro i hi
    rw [nth_termSubstVec hv.isUTerm hi, termSubst_eq_self (hv.nth hi) H]
  · intro n w _ _; simp
  · intro n w _ _; simp
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp hw H, ihq hw H]
  · intro n p q hp hq ihp ihq w hw H
    simp [*, hp.isUFormula, hq.isUFormula, ihp hw H, ihq hw H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (L.qVec w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [Language.qVec]
      · have hi : i < n := by simpa using hi
        simp only [Language.qVec, nth_cons_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
        simp [hw.lh, H i hi, hi]
    simp [*, hp.isUFormula, ih hw.qVec H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (L.qVec w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [Language.qVec]
      · have hi : i < n := by simpa using hi
        simp only [Language.qVec, nth_cons_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
        simp [H i hi, hi]
    simp [*, hp.isUFormula, ih hw.qVec H]

end substs

variable (L)

def Language.substs₁ (t u : V) : V := L.substs ?[t] u

variable {L}

section substs₁

section

def _root_.LO.FirstOrder.Arith.LDef.substs₁Def (pL : LDef) : 𝚺₁.Semisentence 3 := .mkSigma
  “ z t p | ∃ v, !consDef v t 0 ∧ !pL.substsDef z v p” (by simp)

variable (L)

lemma Language.substs₁_defined : 𝚺₁-Function₂ L.substs₁ via pL.substs₁Def := by
  intro v; simp [LDef.substs₁Def, L.substs_defined.df.iff]; rfl

instance Language.substs₁_definable : 𝚺₁-Function₂ L.substs₁ := L.substs₁_defined.to_definable

instance : Γ-[m + 1]-Function₂ L.substs₁ := L.substs₁_definable.of_sigmaOne

end

lemma Language.IsSemiformula.substs₁ (ht : L.IsSemiterm n t) (hp : L.IsSemiformula 1 p) : L.IsSemiformula n (L.substs₁ t p) :=
  Language.IsSemiformula.substs hp (by simp [ht])

end substs₁

variable (L)

def Language.free (p : V) : V := L.substs₁ ^&0 (L.shift p)

variable {L}

section free

section

def _root_.LO.FirstOrder.Arith.LDef.freeDef (pL : LDef) : 𝚺₁.Semisentence 2 := .mkSigma
  “q p | ∃ fz, !qqFvarDef fz 0 ∧ ∃ sp, !pL.shiftDef sp p ∧ !pL.substs₁Def q fz sp” (by simp)

variable (L)

lemma Language.free_defined : 𝚺₁-Function₁ L.free via pL.freeDef := by
  intro v; simp [LDef.freeDef, L.shift_defined.df.iff, L.substs₁_defined.df.iff, Language.free]

instance Language.free_definable : 𝚺₁-Function₁ L.free := L.free_defined.to_definable

instance Language.free_definable' : Γ-[m + 1]-Function₁ L.free := L.free_definable.of_sigmaOne

end

@[simp] lemma Language.IsSemiformula.free (hp : L.IsSemiformula 1 p) : L.IsFormula (L.free p) :=
  Language.IsSemiformula.substs₁ (by simp) hp.shift

end free

/-
section fvfree

variable (L)

def Language.IsFVFree (n p : V) : Prop := L.IsSemiformula n p ∧ L.shift p = p

section

def _root_.LO.FirstOrder.Arith.LDef.isFVFreeDef (pL : LDef) : 𝚺₁.Semisentence 2 :=
  .mkSigma “n p | !pL.isSemiformulaDef.sigma n p ∧ !pL.shiftDef p p” (by simp)

lemma isFVFree_defined : 𝚺₁-Relation L.IsFVFree via pL.isFVFreeDef := by
  intro v; simp [LDef.isFVFreeDef, HierarchySymbol.Semiformula.val_sigma, (semiformula_defined L).df.iff, (shift_defined L).df.iff]
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
    have hp : L.Semiformula n p := Language.IsSemiformula.neg_iff.mp h.1
    have : L.shift (L.neg p) = L.neg p := h.2
    simp [shift_neg hp, neg_inj_iff hp.shift hp] at this
    exact ⟨hp, this⟩
  · intro h; exact ⟨by simp [h.1], by rw [shift_neg h.1, h.2]⟩

end fvfree
-/

namespace Formalized

def qqEQ (x y : V) : V := ^rel 2 (eqIndex : V) ?[x, y]

def qqNEQ (x y : V) : V := ^nrel 2 (eqIndex : V) ?[x, y]

def qqLT (x y : V) : V := ^rel 2 (ltIndex : V) ?[x, y]

def qqNLT (x y : V) : V := ^nrel 2 (ltIndex : V) ?[x, y]

notation:75 x:75 " ^= " y:76 => qqEQ x y

notation:75 x:75 " ^≠ " y:76 => qqNEQ x y

notation:78 x:78 " ^< " y:79 => qqLT x y

notation:78 x:78 " ^≮ " y:79 => qqNLT x y

def _root_.LO.FirstOrder.Arith.qqEQDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y | ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p 2 ↑eqIndex v” (by simp)

def _root_.LO.FirstOrder.Arith.qqNEQDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y | ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p 2 ↑eqIndex v” (by simp)

def _root_.LO.FirstOrder.Arith.qqLTDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y | ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p 2 ↑ltIndex v” (by simp)

def _root_.LO.FirstOrder.Arith.qqNLTDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y | ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p 2 ↑ltIndex v” (by simp)

lemma qqEQ_defined : 𝚺₁-Function₂ (qqEQ : V → V → V) via qqEQDef := by
  intro v; simp [qqEQDef, numeral_eq_natCast, qqEQ]

lemma qqNEQ_defined : 𝚺₁-Function₂ (qqNEQ : V → V → V) via qqNEQDef := by
  intro v; simp [qqNEQDef, numeral_eq_natCast, qqNEQ]

lemma qqLT_defined : 𝚺₁-Function₂ (qqLT : V → V → V) via qqLTDef := by
  intro v; simp [qqLTDef, numeral_eq_natCast, qqLT]

lemma qqNLT_defined : 𝚺₁-Function₂ (qqNLT : V → V → V) via qqNLTDef := by
  intro v; simp [qqNLTDef, numeral_eq_natCast, qqNLT]

instance (Γ m) : Γ-[m + 1]-Function₂ (qqEQ : V → V → V) := .of_sigmaOne qqEQ_defined.to_definable

instance (Γ m) : Γ-[m + 1]-Function₂ (qqNEQ : V → V → V) := .of_sigmaOne qqNEQ_defined.to_definable

instance (Γ m) : Γ-[m + 1]-Function₂ (qqLT : V → V → V) := .of_sigmaOne qqLT_defined.to_definable

instance (Γ m) : Γ-[m + 1]-Function₂ (qqNLT : V → V → V) := .of_sigmaOne qqNLT_defined.to_definable

@[simp] lemma eval_qqEQDef (v) : Semiformula.Evalbm V v qqEQDef.val ↔ v 0 = v 1 ^= v 2 := qqEQ_defined.df.iff v

@[simp] lemma eval_qqNEQDef (v) : Semiformula.Evalbm V v qqNEQDef.val ↔ v 0 = v 1 ^≠ v 2 := qqNEQ_defined.df.iff v

@[simp] lemma eval_qqLTDef (v) : Semiformula.Evalbm V v qqLTDef.val ↔ v 0 = v 1 ^< v 2 := qqLT_defined.df.iff v

@[simp] lemma eval_qqNLTDef (v) : Semiformula.Evalbm V v qqNLTDef.val ↔ v 0 = v 1 ^≮ v 2 := qqNLT_defined.df.iff v

end Formalized

end LO.Arith

end
