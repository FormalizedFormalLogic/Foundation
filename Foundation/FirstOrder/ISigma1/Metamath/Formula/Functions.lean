import Foundation.FirstOrder.ISigma1.Metamath.Formula.Basic
import Foundation.FirstOrder.ISigma1.Metamath.Term.Functions

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

section negation

namespace Negation

def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. !qqNRelDef y k R v” (by simp)
  nrel := .mkSigma “y param k R v. !qqRelDef y k R v” (by simp)
  verum := .mkSigma “y param. !qqFalsumDef y” (by simp)
  falsum := .mkSigma “y param. !qqVerumDef y” (by simp)
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂” (by simp)
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂” (by simp)
  all := .mkSigma “y param p₁ y₁. !qqExDef y y₁” (by simp)
  ex := .mkSigma “y param p₁ y₁. !qqAllDef y y₁” (by simp)
  allChanges := .mkSigma “param' param. param' = 0” (by simp)
  exChanges := .mkSigma “param' param. param' = 0” (by simp)

noncomputable def construction : UformulaRec1.Construction V blueprint where
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
  rel_defined := by intro v; simp [blueprint]
  nrel_defined := by intro v; simp [blueprint]
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]
  or_defined := by intro v; simp [blueprint]
  all_defined := by intro v; simp [blueprint]
  ex_defined := by intro v; simp [blueprint]
  allChanges_defined := by intro v; simp [blueprint]
  exChanges_defined := by intro v; simp [blueprint]

end Negation

open Negation

variable (L)

noncomputable def neg (p : V) : V := construction.result L 0 p

def negGraph : 𝚺₁.Semisentence 2 := (blueprint.result L).rew (Rew.substs ![#0, ‘0’, #1])

variable {L}

section

lemma neg.defined : 𝚺₁-Function₁ neg (V := V) L via negGraph L  := fun v ↦ by
  simpa [negGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using construction.result_defined ![v 0, 0, v 1]

instance neg.definable : 𝚺₁-Function₁ neg (V := V) L := neg.defined.to_definable

instance neg.definable' : Γ-[m + 1]-Function₁ neg (V := V) L := .of_sigmaOne neg.definable

end

@[simp] lemma neg_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    neg L (^rel k R v) = ^nrel k R v := by simp [neg, hR, hv, construction]

@[simp] lemma neg_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    neg L (^nrel k R v) = ^rel k R v := by simp [neg, hR, hv, construction]

@[simp] lemma neg_verum :
    neg L (^⊤ : V) = ^⊥ := by simp [neg, construction]

@[simp] lemma neg_falsum :
    neg L (^⊥ : V) = ^⊤ := by simp [neg, construction]

@[simp] lemma neg_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (p ^⋏ q) = neg L p ^⋎ neg L q := by simp [neg, hp, hq, construction]

@[simp] lemma neg_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    neg L (p ^⋎ q) = neg L p ^⋏ neg L q := by simp [neg, hp, hq, construction]

@[simp] lemma neg_all {p : V} (hp : IsUFormula L p) :
    neg L (^∀ p) = ^∃ (neg L p) := by simp [neg, hp, construction]

@[simp] lemma neg_ex {p : V} (hp : IsUFormula L p) :
    neg L (^∃ p) = ^∀ (neg L p) := by simp [neg, hp, construction]

lemma neg_not_uformula {x : V} (h : ¬IsUFormula L x) :
    neg L x = 0 := construction.result_prop_not _ h

lemma IsUFormula.neg {p : V} : IsUFormula L p → IsUFormula L (neg L p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

@[simp] lemma IsUFormula.bv_neg {p : V} : IsUFormula L p → bv L (Metamath.neg L p) = bv L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k R v hR hv; simp [*]
  · intro k R v hR hv; simp [*]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

@[simp] lemma IsUFormula.neg_neg {p : V} : IsUFormula L p → Metamath.neg L (Metamath.neg L p) = p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

@[simp] lemma IsUFormula.neg_iff {p : V} : IsUFormula L (Metamath.neg L p) ↔ IsUFormula L p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [neg_not_uformula hp] at h
    contradiction
  · exact IsUFormula.neg

@[simp] lemma IsSemiformula.neg_iff {p : V} : IsSemiformula L n (neg L p) ↔ IsSemiformula L n p := by
  constructor
  · intro h; by_contra hp
    have Hp : IsUFormula L p := by by_contra hp; simp [neg_not_uformula hp] at h
    have : IsSemiformula L n p := ⟨Hp, by simpa [Hp.bv_neg] using h.bv_le⟩
    contradiction
  · intro h; exact ⟨by simp [h.isUFormula], by simpa [h.isUFormula] using h.bv_le⟩

alias ⟨IsSemiformula.elim_neg, IsSemiformula.neg⟩ := IsSemiformula.neg_iff

@[simp] lemma neg_inj_iff {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) : neg L p = neg L q ↔ p = q := by
  constructor
  · intro h; simpa [hp.neg_neg, hq.neg_neg] using congrArg (neg L) h
  · rintro rfl; rfl

end negation

variable (L)

noncomputable def imp (p q : V) : V := neg L p ^⋎ q

notation:60 p:61 " ^→[" L "] " q:60 => Language.imp L p q

def impGraph : 𝚺₁.Semisentence 3 := .mkSigma “r p q. ∃ np, !(negGraph L) np p ∧ !qqOrDef r np q”

noncomputable def iff (p q : V) : V := (imp L p q) ^⋏ (imp L q p)

def iffGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “r p q. ∃ pq, !(impGraph L) pq p q ∧ ∃ qp, !(impGraph L) qp q p ∧ !qqAndDef r pq qp”

variable {L}

section imp

@[simp] lemma IsUFormula.imp {p q : V} :
    IsUFormula L (imp L p q) ↔ IsUFormula L p ∧ IsUFormula L q := by
  simp [Metamath.imp]

@[simp] lemma IsSemiformula.imp {n p q : V} :
    IsSemiformula L n (imp L p q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  simp [Metamath.imp]

section

lemma imp.defined : 𝚺₁-Function₂ imp (V := V) L via impGraph L := fun v ↦ by
  simp [impGraph, neg.defined.df.iff]; rfl

instance imp.definable : 𝚺₁-Function₂ imp (V := V) L := imp.defined.to_definable

instance imp.definable' : Γ-[m + 1]-Function₂ imp (V := V) L := imp.definable.of_sigmaOne

end

end imp

section iff

@[simp] lemma IsUFormula.iff {p q : V} :
    IsUFormula L (iff L p q) ↔ IsUFormula L p ∧ IsUFormula L q := by
  simp only [Metamath.iff, and, imp, and_iff_left_iff_imp, and_imp]
  intros; simp_all

@[simp] lemma IsSemiformula.iff {n p q : V} :
    IsSemiformula L n (iff L p q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  simp only [Metamath.iff, and, imp, and_iff_left_iff_imp, and_imp]
  intros; simp_all

@[simp] lemma lt_iff_left (p q : V) : p < iff L p q := lt_trans (lt_or_right _ _) (lt_K!_right _ _)

@[simp] lemma lt_iff_right (p q : V) : q < iff L p q := lt_trans (lt_or_right _ _) (lt_K!_left _ _)

section

lemma iff.defined : 𝚺₁-Function₂ iff (V := V) L via iffGraph L := fun v ↦ by
  simp [iffGraph, imp.defined.df.iff]; rfl

instance iff.definable : 𝚺₁-Function₂ iff (V := V) L := iff.defined.to_definable

instance iff_definable' : Γ-[m + 1]-Function₂ iff (V := V) L := iff.definable.of_sigmaOne

end

end iff

section shift

namespace Shift

variable (L)

def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ v', !(termShiftVecGraph L) v' k v ∧ !qqRelDef y k R v'”
  nrel := .mkSigma “y param k R v. ∃ v', !(termShiftVecGraph L) v' k v ∧ !qqNRelDef y k R v'”
  verum := .mkSigma “y param. !qqVerumDef y” (by simp)
  falsum := .mkSigma “y param. !qqFalsumDef y” (by simp)
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂” (by simp)
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂” (by simp)
  all := .mkSigma “y param p₁ y₁. !qqAllDef y y₁” (by simp)
  ex := .mkSigma “y param p₁ y₁. !qqExDef y y₁” (by simp)
  allChanges := .mkSigma “param' param. param' = 0” (by simp)
  exChanges := .mkSigma “param' param. param' = 0” (by simp)

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k R v ↦ ^rel k R (termShiftVec L k v)
  nrel {_} := fun k R v ↦ ^nrel k R (termShiftVec L k v)
  verum {_} := ^⊤
  falsum {_} := ^⊥
  and {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all {_} := fun _ y₁ ↦ ^∀ y₁
  ex {_} := fun _ y₁ ↦ ^∃ y₁
  allChanges := fun _ ↦ 0
  exChanges := fun _ ↦ 0
  rel_defined := by intro v; simp [blueprint, termShiftVec.defined.df.iff]
  nrel_defined := by intro v; simp [blueprint, termShiftVec.defined.df.iff]
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]
  or_defined := by intro v; simp [blueprint]
  all_defined := by intro v; simp [blueprint]
  ex_defined := by intro v; simp [blueprint]
  allChanges_defined := by intro v; simp [blueprint]
  exChanges_defined := by intro v; simp [blueprint]

end Shift

open Shift

variable (L)

noncomputable def shift (p : V) : V := (construction L).result L 0 p

def shiftGraph : 𝚺₁.Semisentence 2 := blueprint L |>.result L |>.rew (Rew.substs ![#0, ‘0’, #1])

variable {L}

section

lemma shift.defined : 𝚺₁-Function₁[V] shift L via shiftGraph L := fun v ↦ by
  simpa [shiftGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using (construction L).result_defined ![v 0, 0, v 1]

instance shift.definable : 𝚺₁-Function₁[V] shift L := shift.defined.to_definable

instance shift.definable' : Γ-[m + 1]-Function₁[V] shift L := shift.definable.of_sigmaOne

end

@[simp] lemma shift_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    shift L (^relk R v) = ^relk R (termShiftVec L k v) := by simp [shift, hR, hv, construction]

@[simp] lemma shift_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    shift L (^nrelk R v) = ^nrelk R (termShiftVec L k v) := by simp [shift, hR, hv, construction]

@[simp] lemma shift_verum : shift L (^⊤ : V) = ^⊤ := by simp [shift, construction]

@[simp] lemma shift_falsum : shift L (^⊥ : V) = ^⊥ := by simp [shift, construction]

@[simp] lemma shift_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    shift L (p ^⋏ q) = shift L p ^⋏ shift L q := by simp [shift, hp, hq, construction]

@[simp] lemma shift_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    shift L (p ^⋎ q) = shift L p ^⋎ shift L q := by simp [shift, hp, hq, construction]

@[simp] lemma shift_all {p : V} (hp : IsUFormula L p) :
    shift L (^∀ p) = ^∀ (shift L p) := by simp [shift, hp, construction]

@[simp] lemma shift_ex {p : V} (hp : IsUFormula L p) :
    shift L (^∃ p) = ^∃ (shift L p) := by simp [shift, hp, construction]

lemma shift_not_uformula {x : V} (h : ¬IsUFormula L x) :
    shift L x = 0 := (construction L).result_prop_not _ h

lemma IsUFormula.shift {p : V} : IsUFormula L p → IsUFormula L (shift L p) := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq]
  · intro p hp ihp; simp [hp, ihp]
  · intro p hp ihp; simp [hp, ihp]

lemma IsUFormula.bv_shift {p : V} : IsUFormula L p → bv L (Metamath.shift L p) = bv L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction
  · definability
  · intro k r v hr hv; simp [hr, hv]
  · intro k r v hr hv; simp [hr, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq, hp.shift, hq.shift]
  · intro p q hp hq ihp ihq; simp [hp, hq, ihp, ihq, hp.shift, hq.shift]
  · intro p hp ihp; simp [hp, ihp, hp.shift]
  · intro p hp ihp; simp [hp, ihp, hp.shift]

lemma IsSemiformula.shift {p : V} : IsSemiformula L n p → IsSemiformula L n (shift L p) := by
  apply IsSemiformula.ISigma1.sigma1_succ_induction
  · definability
  · intro n k r v hr hv; simp [hr, hv, hv.isUTerm]
  · intro n k r v hr hv; simp [hr, hv, hv.isUTerm]
  · simp
  · simp
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p q hp hq ihp ihq; simp [hp.isUFormula, hq.isUFormula, ihp, ihq]
  · intro n p hp ihp; simp [hp.isUFormula, ihp]
  · intro n p hp ihp; simp [hp.isUFormula, ihp]


@[simp] lemma IsSemiformula.shift_iff {p : V} : IsSemiformula L n (Metamath.shift L p) ↔ IsSemiformula L n p :=
  ⟨fun h ↦ by
    have : IsUFormula L p := by by_contra hp; simp [shift_not_uformula hp] at h
    exact ⟨this, by simpa [this.bv_shift] using h.bv_le⟩,
    IsSemiformula.shift⟩

lemma shift_neg {p : V} (hp : IsSemiformula L n p) : shift L (neg L p) = neg L (shift L p) := by
  apply IsSemiformula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
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

namespace Substs

variable (L)

def blueprint : UformulaRec1.Blueprint where
  rel    := .mkSigma “y param k R v. ∃ v', !(termSubstVecGraph L) v' k param v ∧ !qqRelDef y k R v'”
  nrel   := .mkSigma “y param k R v. ∃ v', !(termSubstVecGraph L) v' k param v ∧ !qqNRelDef y k R v'”
  verum  := .mkSigma “y param. !qqVerumDef y” (by simp)
  falsum := .mkSigma “y param. !qqFalsumDef y” (by simp)
  and    := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂” (by simp)
  or     := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂” (by simp)
  all    := .mkSigma “y param p₁ y₁. !qqAllDef y y₁” (by simp)
  ex     := .mkSigma “y param p₁ y₁. !qqExDef y y₁” (by simp)
  allChanges := .mkSigma “param' param. !(qVecGraph L) param' param”
  exChanges  := .mkSigma “param' param. !(qVecGraph L) param' param”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel (param)  := fun k R v ↦ ^rel k R (termSubstVec L k param v)
  nrel (param) := fun k R v ↦ ^nrel k R (termSubstVec L k param v)
  verum _      := ^⊤
  falsum _     := ^⊥
  and _        := fun _ _ y₁ y₂ ↦ y₁ ^⋏ y₂
  or _         := fun _ _ y₁ y₂ ↦ y₁ ^⋎ y₂
  all _        := fun _ y₁ ↦ ^∀ y₁
  ex _         := fun _ y₁ ↦ ^∃ y₁
  allChanges (param) := qVec L param
  exChanges (param) := qVec L param
  rel_defined := by intro v; simp [blueprint, termSubstVec.defined.df.iff]
  nrel_defined := by intro v; simp [blueprint, termSubstVec.defined.df.iff]
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]
  or_defined := by intro v; simp [blueprint]
  all_defined := by intro v; simp [blueprint]
  ex_defined := by intro v; simp [blueprint]
  allChanges_defined := by intro v; simp [blueprint, qVec.defined.df.iff]
  exChanges_defined := by intro v; simp [blueprint, qVec.defined.df.iff]

end Substs

open Substs

variable (L)

noncomputable def substs (w p : V) : V := (construction L).result L w p

def substsGraph : 𝚺₁.Semisentence 3 := (blueprint L).result L

variable {L}

section

lemma substs.defined : 𝚺₁-Function₂[V] substs L via substsGraph L := (construction L).result_defined

instance substs.definable : 𝚺₁-Function₂[V] substs L := substs.defined.to_definable

instance substs.definable' : Γ-[m + 1]-Function₂[V] substs L := substs.definable.of_sigmaOne

end

variable {m w : V}

@[simp] lemma substs_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    substs L w (^relk R v) = ^rel k R (termSubstVec L k w v) := by simp [substs, hR, hv, construction]

@[simp] lemma substs_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    substs L w (^nrelk R v) = ^nrel k R (termSubstVec L k w v) := by simp [substs, hR, hv, construction]

@[simp] lemma substs_verum (w : V) : substs L w ^⊤ = ^⊤ := by simp [substs, construction]

@[simp] lemma substs_falsum (w : V) : substs L w ^⊥ = ^⊥ := by simp [substs, construction]

@[simp] lemma substs_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    substs L w (p ^⋏ q) = substs L w p ^⋏ substs L w q := by simp [substs, hp, hq, construction]

@[simp] lemma substs_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    substs L w (p ^⋎ q) = substs L w p ^⋎ substs L w q := by simp [substs, hp, hq, construction]

@[simp] lemma substs_all {p} (hp : IsUFormula L p) :
    substs L w (^∀ p) = ^∀ (substs L (qVec L w) p) := by simp [substs, hp, construction]

@[simp] lemma substs_ex {p} (hp : IsUFormula L p) :
    substs L w (^∃ p) = ^∃ (substs L (qVec L w) p) := by simp [substs, hp, construction]

lemma isUFormula_subst_ISigma1.sigma1_succ_induction {P : V → V → V → Prop} (hP : 𝚺₁-Relation₃ P)
    (hRel : ∀ w k R v, L.IsRel k R → IsUTermVec L k v → P w (^relk R v) (^rel k R (termSubstVec L k w v)))
    (hNRel : ∀ w k R v, L.IsRel k R → IsUTermVec L k v → P w (^nrelk R v) (^nrel k R (termSubstVec L k w v)))
    (hverum : ∀ w, P w ^⊤ ^⊤)
    (hfalsum : ∀ w, P w ^⊥ ^⊥)
    (hand : ∀ w p q, IsUFormula L p → IsUFormula L q →
      P w p (substs L w p) → P w q (substs L w q) → P w (p ^⋏ q) (substs L w p ^⋏ substs L w q))
    (hor : ∀ w p q, IsUFormula L p → IsUFormula L q →
      P w p (substs L w p) → P w q (substs L w q) → P w (p ^⋎ q) (substs L w p ^⋎ substs L w q))
    (hall : ∀ w p, IsUFormula L p → P (qVec L w) p (substs L (qVec L w) p) → P w (^∀ p) (^∀ (substs L (qVec L w) p)))
    (hex : ∀ w p, IsUFormula L p → P (qVec L w) p (substs L (qVec L w) p) → P w (^∃ p) (^∃ (substs L (qVec L w) p))) :
    ∀ {w p}, IsUFormula L p → P w p (substs L w p) := by
  suffices ∀ param p, IsUFormula L p → P param p ((construction L).result L param p) by
    intro w p hp; simpa using this w p hp
  apply (construction L).uformula_result_induction (P := fun param p y ↦ P param p y)
  · definability
  · intro param k R v hkR hv; simpa using hRel param k R v hkR hv
  · intro param k R v hkR hv; simpa using hNRel param k R v hkR hv
  · intro param; simpa using hverum param
  · intro param; simpa using hfalsum param
  · intro param p q hp hq ihp ihq
    simpa [substs] using
      hand param p q hp hq (by simpa [substs] using ihp) (by simpa [substs] using ihq)
  · intro param p q hp hq ihp ihq
    simpa [substs] using
      hor param p q hp hq (by simpa [substs] using ihp) (by simpa [substs] using ihq)
  · intro param p hp ihp
    simpa using hall param p hp (by simpa [construction] using ihp)
  · intro param p hp ihp
    simpa using hex param p hp (by simpa [construction] using ihp)

lemma semiformula_subst_induction {P : V → V → V → V → Prop} (hP : 𝚺₁-Relation₄ P)
    (hRel : ∀ n w k R v, L.IsRel k R → IsSemitermVec L k n v → P n w (^relk R v) (^rel k R (termSubstVec L k w v)))
    (hNRel : ∀ n w k R v, L.IsRel k R → IsSemitermVec L k n v → P n w (^nrelk R v) (^nrel k R (termSubstVec L k w v)))
    (hverum : ∀ n w, P n w ^⊤ ^⊤)
    (hfalsum : ∀ n w, P n w ^⊥ ^⊥)
    (hand : ∀ n w p q, IsSemiformula L n p → IsSemiformula L n q →
      P n w p (substs L w p) → P n w q (substs L w q) → P n w (p ^⋏ q) (substs L w p ^⋏ substs L w q))
    (hor : ∀ n w p q, IsSemiformula L n p → IsSemiformula L n q →
      P n w p (substs L w p) → P n w q (substs L w q) → P n w (p ^⋎ q) (substs L w p ^⋎ substs L w q))
    (hall : ∀ n w p, IsSemiformula L (n + 1) p →
      P (n + 1) (qVec L w) p (substs L (qVec L w) p) → P n w (^∀ p) (^∀ (substs L (qVec L w) p)))
    (hex : ∀ n w p, IsSemiformula L (n + 1) p →
      P (n + 1) (qVec L w) p (substs L (qVec L w) p) → P n w (^∃ p) (^∃ (substs L (qVec L w) p))) :
    ∀ {n p w}, IsSemiformula L n p → P n w p (substs L w p) := by
  suffices ∀ param n p, IsSemiformula L n p → P n param p ((construction L).result L param p) by
    intro n p w hp; simpa using this w n p hp
  apply (construction L).semiformula_result_induction (P := fun param n p y ↦ P n param p y)
  · definability
  · intro n param k R v hkR hv; simpa using hRel n param k R v hkR hv
  · intro n param k R v hkR hv; simpa using hNRel n param k R v hkR hv
  · intro n param; simpa using hverum n param
  · intro n param; simpa using hfalsum n param
  · intro n param p q hp hq ihp ihq
    simpa [substs] using
      hand n param p q hp hq (by simpa [substs] using ihp) (by simpa [substs] using ihq)
  · intro n param p q hp hq ihp ihq
    simpa [substs] using
      hor n param p q hp hq (by simpa [substs] using ihp) (by simpa [substs] using ihq)
  · intro n param p hp ihp
    simpa using hall n param p hp (by simpa [construction] using ihp)
  · intro n param p hp ihp
    simpa using hex n param p hp (by simpa [construction] using ihp)

@[simp] lemma IsSemiformula.substs {n p m w : V} :
    IsSemiformula L n p → IsSemitermVec L n m w → IsSemiformula L m (substs L w p) := by
  let fw : V → V → V → V → V := fun _ w _ _ ↦ Max.max w (qVec L w)
  have hfw : 𝚺₁-Function₄ fw := by definability
  let fn : V → V → V → V → V := fun _ _ n _ ↦ n + 1
  have hfn : 𝚺₁-Function₄ fn := by definability
  let fm : V → V → V → V → V := fun _ _ _ m ↦ m + 1
  have hfm : 𝚺₁-Function₄ fm := by definability
  apply bounded_all_sigma1_order_induction₃ hfw hfn hfm ?_ ?_ p w n m
  · definability
  intro p w n m ih hp hw
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · simp [hR, hv.isUTerm, hw.termSubstVec hv]
  · simp [hR, hv.isUTerm, hw.termSubstVec hv]
  · simp
  · simp
  · have ih₁ : IsSemiformula L m (Metamath.substs L w p₁) := ih p₁ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₁ hw
    have ih₂ : IsSemiformula L m (Metamath.substs L w p₂) := ih p₂ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₂ hw
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · have ih₁ : IsSemiformula L m (Metamath.substs L w p₁) := ih p₁ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₁ hw
    have ih₂ : IsSemiformula L m (Metamath.substs L w p₂) := ih p₂ (by simp) w (by simp [fw]) n (by simp [fn]) m (by simp [fm]) h₂ hw
    simp [h₁.isUFormula, h₂.isUFormula, ih₁, ih₂]
  · simpa [h₁.isUFormula] using ih p₁ (by simp) (qVec L w) (by simp [fw]) (n + 1) (by simp [fn]) (m + 1) (by simp [fm]) h₁ hw.qVec
  · simpa [h₁.isUFormula] using ih p₁ (by simp) (qVec L w) (by simp [fw]) (n + 1) (by simp [fn]) (m + 1) (by simp [fm]) h₁ hw.qVec

lemma substs_not_uformula {w x} (h : ¬IsUFormula L x) :
    substs L w x = 0 := (construction L).result_prop_not _ h

lemma substs_neg {p} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → substs L w (neg L p) = neg L (substs L w p) := by
  revert m w
  apply IsSemiformula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
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

lemma shift_substs {p} (hp : IsSemiformula L n p) :
    IsSemitermVec L n m w → shift L (substs L w p) = substs L (termShiftVec L n w) (shift L p) := by
  revert m w
  apply IsSemiformula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
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

lemma substs_substs {p} (hp : IsSemiformula L l p) :
    IsSemitermVec L n m w → IsSemitermVec L l n v → substs L w (substs L v p) = substs L (termSubstVec L l w v) p := by
  revert m w n v
  apply IsSemiformula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
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

lemma subst_eq_self {n w : V} (hp : IsSemiformula L n p) (hw : IsSemitermVec L n n w) (H : ∀ i < n, w.[i] = ^#i) :
    substs L w p = p := by
  revert w
  apply IsSemiformula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
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
    have H : ∀ i < n + 1, (qVec L w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_cons_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
        simp [H i hi]
    simp [*, hp.isUFormula, ih hw.qVec H]
  · intro n p hp ih w hw H
    have H : ∀ i < n + 1, (qVec L w).[i] = ^#i := by
      intro i hi
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp [qVec]
      · have hi : i < n := by simpa using hi
        simp only [qVec, nth_cons_succ]
        rw [nth_termBShiftVec (by simpa [hw.lh] using hw.isUTerm) (by simp [hw.lh, hi])]
        simp [H i hi]
    simp [*, hp.isUFormula, ih hw.qVec H]

lemma subst_eq_self₁ (hp : IsSemiformula L 1 p) :
    substs L (^#0 ∷ 0) p = p := subst_eq_self hp (by simp) (by simp)

end substs

variable (L)

noncomputable def substs1 (t u : V) : V := substs L ?[t] u

def substs1Graph : 𝚺₁.Semisentence 3 := .mkSigma “ z t p. ∃ v, !consDef v t 0 ∧ !(substsGraph L) z v p”

variable {L}

section substs1

section

lemma substs1.defined : 𝚺₁-Function₂[V] substs1 L via substs1Graph L := by
  intro v; simp [substs1Graph, substs.defined.df.iff]; rfl

instance substs1.definable : 𝚺₁-Function₂[V] substs1 L := substs1.defined.to_definable

instance substs1.definable' : Γ-[m + 1]-Function₂[V] substs1 L := substs1.definable.of_sigmaOne

end

lemma IsSemiformula.substs1 (ht : IsSemiterm L n t) (hp : IsSemiformula L 1 p) : IsSemiformula L n (substs1 L t p) :=
  IsSemiformula.substs hp (by simp [ht])

end substs1

variable (L)

noncomputable def free (p : V) : V := substs1 L ^&0 (shift L p)

def freeGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “q p. ∃ fz, !qqFvarDef fz 0 ∧ ∃ sp, !(shiftGraph L) sp p ∧ !(substs1Graph L) q fz sp”

variable {L}

section free

section

lemma free.defined : 𝚺₁-Function₁[V] free L via freeGraph L := by
  intro v; simp [freeGraph, shift.defined.df.iff, substs1.defined.df.iff, free]

instance free.definable : 𝚺₁-Function₁[V] free L := free.defined.to_definable

instance free.definable' : Γ-[m + 1]-Function₁[V] free L := free.definable.of_sigmaOne

end

@[simp] lemma IsSemiformula.free (hp : IsSemiformula L 1 p) : IsFormula L (free L p) :=
  IsSemiformula.substs1 (by simp) hp.shift

end free

/-
section fvfree

variable (L)

def Language.IsFVFree (n p : V) : Prop := IsSemiformula L n p ∧ shift L p = p

section

def _root_.LO.FirstOrder.Arithmetic.LDef.isFVFreeDef (pL : LDef) : 𝚺₁.Semisentence 2 :=
  .mkSigma “n p | !(isSemiformula L).sigma n p ∧ !pshift LDef p p” (by simp)

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

@[simp] lemma Language.IsFVFree.neg_iff : L.IsFVFree n (neg L p) ↔ L.IsFVFree n p := by
  constructor
  · intro h
    have hp : Semiformula L n p := IsSemiformula.neg_iff.mp h.1
    have : shift L (neg L p) = neg L p := h.2
    simp [shift_neg hp, neg_inj_iff hp.shift hp] at this
    exact ⟨hp, this⟩
  · intro h; exact ⟨by simp [h.1], by rw [shift_neg h.1, h.2]⟩

end fvfree
-/

namespace InternalArithmetic

noncomputable def qqEQ (x y : V) : V := ^rel 2 (eqIndex : V) ?[x, y]

noncomputable def qqNEQ (x y : V) : V := ^nrel 2 (eqIndex : V) ?[x, y]

noncomputable def qqLT (x y : V) : V := ^rel 2 (ltIndex : V) ?[x, y]

noncomputable def qqNLT (x y : V) : V := ^nrel 2 (ltIndex : V) ?[x, y]

notation:75 x:75 " ^= " y:76 => qqEQ x y

notation:75 x:75 " ^≠ " y:76 => qqNEQ x y

notation:78 x:78 " ^< " y:79 => qqLT x y

notation:78 x:78 " ^≮ " y:79 => qqNLT x y

@[simp] lemma lt_qqEQ_left (x y : V) : x < x ^= y := by
  simpa using nth_lt_qqRel_of_lt (i := 0) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqEQ_right (x y : V) : y < x ^= y := by
  simpa using nth_lt_qqRel_of_lt (i := 1) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqLT_left (x y : V) : x < x ^< y := by
  simpa using nth_lt_qqRel_of_lt (i := 0) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqLT_right (x y : V) : y < x ^< y := by
  simpa using nth_lt_qqRel_of_lt (i := 1) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNEQ_left (x y : V) : x < x ^≠ y := by
  simpa using nth_lt_qqNRel_of_lt (i := 0) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNEQ_right (x y : V) : y < x ^≠ y := by
  simpa using nth_lt_qqNRel_of_lt (i := 1) (k := 2) (r := (eqIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNLT_left (x y : V) : x < x ^≮ y := by
  simpa using nth_lt_qqNRel_of_lt (i := 0) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

@[simp] lemma lt_qqNLT_right (x y : V) : y < x ^≮ y := by
  simpa using nth_lt_qqNRel_of_lt (i := 1) (k := 2) (r := (ltIndex : V)) (v := ?[x, y]) (by simp)

def _root_.LO.FirstOrder.Arithmetic.qqEQDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p 2 ↑eqIndex v” (by simp)

def _root_.LO.FirstOrder.Arithmetic.qqNEQDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p 2 ↑eqIndex v” (by simp)

def _root_.LO.FirstOrder.Arithmetic.qqLTDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqRelDef p 2 ↑ltIndex v” (by simp)

def _root_.LO.FirstOrder.Arithmetic.qqNLTDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “p x y. ∃ v, !mkVec₂Def v x y ∧ !qqNRelDef p 2 ↑ltIndex v” (by simp)

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

lemma neg_eq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^= u) = t ^≠ u := by
  simp only [qqEQ, qqNEQ]
  rw [neg_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_neq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^≠ u) = t ^= u := by
  simp only [qqNEQ, qqEQ]
  rw [neg_nrel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_lt {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^< u) = t ^≮ u := by
  simp only [qqLT, qqNLT]
  rw [neg_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma neg_nlt {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) : neg ℒₒᵣ (t ^≮ u) = t ^< u := by
  simp only [qqNLT, qqLT]
  rw [neg_nrel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]

lemma substs_eq {t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    substs ℒₒᵣ w (t ^= u) = (termSubst ℒₒᵣ w t) ^= (termSubst ℒₒᵣ w u) := by
  simp only [qqEQ]
  rw [substs_rel (L := ℒₒᵣ) (by simp) (by simp [ht, hu])]
  simp [termSubstVec_cons₂ ht hu]

end InternalArithmetic

end LO.ISigma1.Metamath
