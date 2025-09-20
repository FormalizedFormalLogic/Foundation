import Foundation.FirstOrder.Internal.Syntax.Term.Basic
import Foundation.FirstOrder.ISigma1.Ind

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def qqRel (k r v : V) : V := ⟪0, k, r, v⟫ + 1

noncomputable def qqNRel (k r v : V) : V := ⟪1, k, r, v⟫ + 1

noncomputable def qqVerum : V := ⟪2, 0⟫ + 1

noncomputable def qqFalsum : V := ⟪3, 0⟫ + 1

noncomputable def qqAnd (p q : V) : V := ⟪4, p, q⟫ + 1

noncomputable def qqOr (p q : V) : V := ⟪5, p, q⟫ + 1

noncomputable def qqAll (p : V) : V := ⟪6, p⟫ + 1

noncomputable def qqEx (p : V) : V := ⟪7, p⟫ + 1

scoped prefix:max "^rel " => qqRel

scoped prefix:max "^nrel " => qqNRel

scoped notation "^⊤" => qqVerum

scoped notation "^⊥" => qqFalsum

scoped notation p:69 " ^⋏ " q:70 => qqAnd p q

scoped notation p:68 " ^⋎ " q:69 => qqOr p q

scoped notation "^∀ " p:64 => qqAll p

scoped notation "^∃ " p:64 => qqEx p

section

def _root_.LO.FirstOrder.Arithmetic.qqRelDef : 𝚺₀.Semisentence 4 :=
  .mkSigma “p k r v. ∃ p' < p, !pair₄Def p' 0 k r v ∧ p = p' + 1”

def _root_.LO.FirstOrder.Arithmetic.qqNRelDef : 𝚺₀.Semisentence 4 :=
  .mkSigma “p k r v. ∃ p' < p, !pair₄Def p' 1 k r v ∧ p = p' + 1”

def _root_.LO.FirstOrder.Arithmetic.qqVerumDef : 𝚺₀.Semisentence 1 :=
  .mkSigma “p. ∃ p' < p, !pairDef p' 2 0 ∧ p = p' + 1”

def _root_.LO.FirstOrder.Arithmetic.qqFalsumDef : 𝚺₀.Semisentence 1 :=
  .mkSigma “p. ∃ p' < p, !pairDef p' 3 0 ∧ p = p' + 1”

def _root_.LO.FirstOrder.Arithmetic.qqAndDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “r p q. ∃ r' < r, !pair₃Def r' 4 p q ∧ r = r' + 1”

def _root_.LO.FirstOrder.Arithmetic.qqOrDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “r p q. ∃ r' < r, !pair₃Def r' 5 p q ∧ r = r' + 1”

def _root_.LO.FirstOrder.Arithmetic.qqAllDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “r p. ∃ r' < r, !pairDef r' 6 p ∧ r = r' + 1”

def _root_.LO.FirstOrder.Arithmetic.qqExDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “r p. ∃ r' < r, !pairDef r' 7 p ∧ r = r' + 1”

lemma qqRel_defined : 𝚺₀-Function₃ (qqRel : V → V → V → V) via qqRelDef := by
  intro v; simp_all [qqRelDef, qqRel]

lemma qqNRel_defined : 𝚺₀-Function₃ (qqNRel : V → V → V → V) via qqNRelDef := by
  intro v; simp_all [qqNRelDef, qqNRel]

lemma qqVerum_defined : 𝚺₀-Function₀ (qqVerum : V) via qqVerumDef := by
  intro v; simp_all [qqVerumDef, qqVerum]

lemma qqFalsum_defined : 𝚺₀-Function₀ (qqFalsum : V) via qqFalsumDef := by
  intro v; simp_all [qqFalsumDef, qqFalsum]

lemma qqAnd_defined : 𝚺₀-Function₂ (qqAnd : V → V → V) via qqAndDef := by
  intro v; simp_all [qqAndDef, qqAnd]

lemma qqOr_defined : 𝚺₀-Function₂ (qqOr : V → V → V) via qqOrDef := by
  intro v; simp_all [qqOrDef, numeral_eq_natCast, qqOr]

lemma qqForall_defined : 𝚺₀-Function₁ (qqAll : V → V) via qqAllDef := by
  intro v; simp_all [qqAllDef, numeral_eq_natCast, qqAll]

lemma qqExists_defined : 𝚺₀-Function₁ (qqEx : V → V) via qqExDef := by
  intro v; simp_all [qqExDef, numeral_eq_natCast, qqEx]

@[simp] lemma eval_qqRelDef (v) :
    Semiformula.Evalbm V v qqRelDef.val ↔ v 0 = ^rel (v 1) (v 2) (v 3) := qqRel_defined.df.iff v

@[simp] lemma eval_qqNRelDef (v) :
    Semiformula.Evalbm V v qqNRelDef.val ↔ v 0 = ^nrel (v 1) (v 2) (v 3) := qqNRel_defined.df.iff v

@[simp] lemma eval_qqVerumDef (v) :
    Semiformula.Evalbm V v qqVerumDef.val ↔ v 0 = ^⊤ := qqVerum_defined.df.iff v

@[simp] lemma eval_qqFalsumDef (v) :
    Semiformula.Evalbm V v qqFalsumDef.val ↔ v 0 = ^⊥ := qqFalsum_defined.df.iff v

@[simp] lemma eval_qqAndDef (v) :
    Semiformula.Evalbm V v qqAndDef.val ↔ v 0 = (v 1) ^⋏ (v 2) := qqAnd_defined.df.iff v

@[simp] lemma eval_qqOrDef (v) :
    Semiformula.Evalbm V v qqOrDef.val ↔ v 0 = (v 1) ^⋎ (v 2) := qqOr_defined.df.iff v

@[simp] lemma eval_qqAllDef (v) :
    Semiformula.Evalbm V v qqAllDef.val ↔ v 0 = ^∀ (v 1) := qqForall_defined.df.iff v

@[simp] lemma eval_qqExDef (v) :
    Semiformula.Evalbm V v qqExDef.val ↔ v 0 = ^∃ (v 1) := qqExists_defined.df.iff v

instance (ℌ : HierarchySymbol) : ℌ-Function₃ (qqRel : V → V → V → V) := .of_zero qqRel_defined.to_definable

instance (ℌ : HierarchySymbol) : ℌ-Function₃ (qqNRel : V → V → V → V) := .of_zero qqNRel_defined.to_definable

-- instance (ℌ : HierarchySymbol) : ℌ-Function₀ (qqVerum : V) := .of_zero qqVerum_defined.to_definable

-- instance (ℌ : HierarchySymbol) : ℌ-Function₁ (qqFalsum : V → V) := .of_zero qqFalsum_defined.to_definable

instance (ℌ : HierarchySymbol) : ℌ-Function₂ (qqAnd : V → V → V) := .of_zero qqAnd_defined.to_definable

instance (ℌ : HierarchySymbol) : ℌ-Function₂ (qqOr : V → V → V) := .of_zero qqOr_defined.to_definable

instance (ℌ : HierarchySymbol) : ℌ-Function₁ (qqAll : V → V) := .of_zero qqForall_defined.to_definable

instance (ℌ : HierarchySymbol) : ℌ-Function₁ (qqEx : V → V) := .of_zero qqExists_defined.to_definable

end

@[simp] lemma qqRel_inj (k₁ r₁ v₁ k₂ r₂ v₂ : V) :
    ^rel k₁ r₁ v₁ = ^rel k₂ r₂ v₂ ↔ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqRel]
@[simp] lemma qqNRel_inj (k₁ r₁ v₁ k₂ r₂ v₂ : V) :
    ^nrel k₁ r₁ v₁ = ^nrel k₂ r₂ v₂ ↔ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqNRel]
@[simp] lemma qqAnd_inj (p₁ q₁ p₂ q₂ : V) : p₁ ^⋏ q₁ = p₂ ^⋏ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqAnd]
@[simp] lemma qqOr_inj (p₁ q₁ p₂ q₂ : V) : p₁ ^⋎ q₁ = p₂ ^⋎ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqOr]
@[simp] lemma qqAll_inj (p₁ p₂ : V) : ^∀ p₁ = ^∀ p₂ ↔ p₁ = p₂ := by simp [qqAll]
@[simp] lemma qqEx_inj (p₁ p₂ : V) : ^∃ p₁ = ^∃ p₂ ↔ p₁ = p₂ := by simp [qqEx]

@[simp] lemma arity_lt_rel (k r v : V) : k < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left k ⟪r, v⟫) <| le_pair_right _ _
@[simp] lemma r_lt_rel (k r v : V) : r < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_rel (k r v : V) : v < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma arity_lt_nrel (k r v : V) : k < ^nrel k r v := le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma r_lt_nrel (k r v : V) : r < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <| le_pair_right _ _
@[simp] lemma v_lt_nrel (k r v : V) : v < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <| le_pair_right _ _

lemma nth_lt_qqRel_of_lt {i k r v : V} (hi : i < len v) : v.[i] < ^rel k r v :=
  lt_trans (nth_lt_self hi) (v_lt_rel _ _ _)

lemma nth_lt_qqNRel_of_lt {i k r v : V} (hi : i < len v) : v.[i] < ^nrel k r v :=
  lt_trans (nth_lt_self hi) (v_lt_nrel _ _ _)

@[simp] lemma lt_K!_left (p q : V) : p < p ^⋏ q := le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma lt_K!_right (p q : V) : q < p ^⋏ q := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_or_left (p q : V) : p < p ^⋎ q := le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma lt_or_right (p q : V) : q < p ^⋎ q := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_forall (p : V) : p < ^∀ p := le_iff_lt_succ.mp <| le_pair_right _ _

@[simp] lemma lt_exists (p : V) : p < ^∃ p := le_iff_lt_succ.mp <| le_pair_right _ _

namespace FormalizedFormula

variable (L)

def Phi (C : Set V) (p : V) : Prop :=
  (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ p = ^rel k R v) ∨
  (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ p = ^nrel k R v) ∨
  (p = ^⊤) ∨
  (p = ^⊥) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∀ p₁) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∃ p₁)

private lemma phi_iff (C p : V) :
    Phi L {x | x ∈ C} p ↔
    (∃ k < p, ∃ r < p, ∃ v < p, L.IsRel k r ∧ IsUTermVec L k v ∧ p = ^rel k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, L.IsRel k r ∧ IsUTermVec L k v ∧ p = ^nrel k r v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ p = ^∀ p₁) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ p = ^∃ p₁) where
  mp := by
    rintro (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | H)
    · left; refine ⟨k, ?_, r, ?_, v, ?_, hkr, hv, rfl⟩ <;> simp
    · right; left; refine ⟨k, ?_, r, ?_, v, ?_, hkr, hv, rfl⟩ <;> simp
    right; right
    rcases H with (rfl | rfl | H)
    · left; rfl
    · right; left; rfl
    right; right
    rcases H with (⟨q, r, hp, hq, rfl⟩ | ⟨q, r, hp, hq, rfl⟩ | H)
    · left; refine ⟨q, ?_, r, ?_, hp, hq, rfl⟩ <;> simp
    · right; left; refine ⟨q, ?_, r, ?_, hp, hq, rfl⟩ <;> simp
    right; right
    rcases H with (⟨q, h, rfl⟩ | ⟨q, h, rfl⟩)
    · left; refine ⟨q, ?_, h, rfl⟩; simp
    · right; refine ⟨q, ?_, h, rfl⟩; simp
  mpr := by
    unfold Phi
    rintro (⟨k, _, r, _, v, _, hkr, hv, rfl⟩ | ⟨k, _, r, _, v, _, hkr, hv, rfl⟩ | H)
    · left; exact ⟨k, r, v, hkr, hv, rfl⟩
    · right; left; exact ⟨k, r, v, hkr, hv, rfl⟩
    right; right
    rcases H with (rfl | rfl | H)
    · left; rfl
    · right; left; rfl
    right; right
    rcases H with (⟨q, _, r, _, hq, hr, rfl⟩ | ⟨q, _, r, _, hq, hr, rfl⟩ | H)
    · left; exact ⟨q, r, hq, hr, rfl⟩
    · right; left; exact ⟨q, r, hq, hr, rfl⟩
    right; right
    rcases H with (⟨q, _, hq, rfl⟩ | ⟨q, _, hq, rfl⟩)
    · left; exact ⟨q, hq, rfl⟩
    · right; exact ⟨q, hq, rfl⟩

def formulaAux : 𝚺₀.Semisentence 2 := .mkSigma
  “p C.
    !qqVerumDef p ∨
    !qqFalsumDef p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqAllDef p p₁) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqExDef p p₁)”

def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma
    “p C.
      (∃ k < p, ∃ r < p, ∃ v < p, !L.isRel k r ∧ !(isUTermVec L).sigma k v ∧ !qqRelDef p k r v) ∨
      (∃ k < p, ∃ r < p, ∃ v < p, !L.isRel k r ∧ !(isUTermVec L).sigma k v ∧ !qqNRelDef p k r v) ∨
      !formulaAux p C”)
  (.mkPi
    “p C.
      (∃ k < p, ∃ r < p, ∃ v < p, !L.isRel k r ∧ !(isUTermVec L).pi k v ∧ !qqRelDef p k r v) ∨
      (∃ k < p, ∃ r < p, ∃ v < p, !L.isRel k r ∧ !(isUTermVec L).pi k v ∧ !qqNRelDef p k r v) ∨
      !formulaAux p C”)⟩

def construction : Fixpoint.Construction V (blueprint L) where
  Φ := fun _ ↦ Phi L
  defined := ⟨
    by  intro v
        -- simp [blueprint, HierarchySymbol.Semiformula.val_sigma, L.isUTermVec_defined.proper.iff']
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, blueprint, Fin.isValue,
          HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.sigma_mkDelta,
          HierarchySymbol.Semiformula.val_mkSigma, LogicalConnective.HomClass.map_or,
          Semiformula.eval_bexLT, Semiterm.val_bvar, Matrix.cons_val_one, Matrix.vecHead,
          Matrix.cons_val_two, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
          LogicalConnective.HomClass.map_and, Semiformula.eval_substs, Matrix.comp_vecCons',
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
          Matrix.cons_val_three, Fin.succ_one_eq_two, eval_qqRelDef, LogicalConnective.Prop.and_eq,
          eval_qqNRelDef, LogicalConnective.Prop.or_eq, HierarchySymbol.Semiformula.pi_mkDelta,
          HierarchySymbol.Semiformula.val_mkPi, IsUTermVec.defined.proper.iff']
        ,
    by  intro v
        -- simpa [blueprint, Language.Defined.eval_rel_iff (L := L), L.isUTermVec_defined.df.iff,
        --  HierarchySymbol.Semiformula.val_sigma, formulaAux] using phi_iff L _ _
        simpa only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, blueprint,
          HierarchySymbol.Semiformula.val_sigma, formulaAux,
          HierarchySymbol.Semiformula.val_mkSigma, LogicalConnective.HomClass.map_or,
          HierarchySymbol.Semiformula.val_mkDelta, Semiformula.eval_bexLT, Semiterm.val_bvar,
          Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_two, Matrix.vecTail,
          Function.comp_apply, Fin.succ_zero_eq_one, LogicalConnective.HomClass.map_and,
          Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_zero,
          Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
          eval_rel_iff (L := L), IsUTermVec.defined.df.iff,
          Matrix.cons_val_three, Fin.succ_one_eq_two, eval_qqRelDef, LogicalConnective.Prop.and_eq,
          eval_qqNRelDef, eval_qqVerumDef, eval_qqFalsumDef, Semiformula.eval_operator_two,
          Structure.Mem.mem, eval_qqAndDef, eval_qqOrDef, eval_qqAllDef, eval_qqExDef,
          LogicalConnective.Prop.or_eq] using phi_iff L _ _⟩
  monotone := by
    unfold Phi
    rintro C C' hC _ x (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨q, r, hqC, hrC, rfl⟩ | ⟨q, r, hqC, hrC, rfl⟩ | H)
    · left; exact ⟨q, r, hC hqC, hC hrC, rfl⟩
    · right; left; exact ⟨q, r, hC hqC, hC hrC, rfl⟩
    right; right
    rcases H with (⟨q, hqC, rfl⟩ | ⟨q, hqC, rfl⟩)
    · left; exact ⟨q, hC hqC, rfl⟩
    · right; exact ⟨q, hC hqC, rfl⟩

instance : (construction L).StrongFinite V where
  strong_finite := by
    unfold construction Phi
    rintro C _ x (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨q, r, hqC, hrC, rfl⟩ | ⟨q, r, hqC, hrC, rfl⟩ | H)
    · left; exact ⟨q, r, by simp [hqC], by simp [hrC], rfl⟩
    · right; left; exact ⟨q, r, by simp [hqC], by simp [hrC], rfl⟩
    right; right
    rcases H with (⟨q, hqC, rfl⟩ | ⟨q, hqC, rfl⟩)
    · left; exact ⟨q, by simp [hqC], rfl⟩
    · right; exact ⟨q, by simp [hqC], rfl⟩

end FormalizedFormula

variable (L)

def IsUFormula : V → Prop := (FormalizedFormula.construction L).Fixpoint ![]

def isUFormula : 𝚫₁.Semisentence 1 := (FormalizedFormula.blueprint L).fixpointDefΔ₁

variable {L}

namespace IsUFormula

open FormalizedFormula

section

lemma defined : 𝚫₁-Predicate IsUFormula (V := V) L via isUFormula L := (construction L).fixpoint_definedΔ₁

instance definable : 𝚫₁-Predicate IsUFormula (V := V) L := IsUFormula.defined.to_definable

instance definable' : Γ-[m + 1]-Predicate IsUFormula (V := V) L := IsUFormula.definable.of_deltaOne

end

lemma case_iff {p : V} :
    IsUFormula L p ↔
    (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ p = ^rel k R v) ∨
    (∃ k R v, L.IsRel k R ∧ IsUTermVec L k v ∧ p = ^nrel k R v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ p₂, IsUFormula L p₁ ∧ IsUFormula L p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsUFormula L p₁ ∧ IsUFormula L p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, IsUFormula L p₁ ∧ p = ^∀ p₁) ∨
    (∃ p₁, IsUFormula L p₁ ∧ p = ^∃ p₁) :=
  (construction L).case

alias ⟨case, mk⟩ := case_iff

set_option linter.flexible false in
@[simp] lemma rel {k r v : V} :
    IsUFormula L (^rel k r v) ↔ L.IsRel k r ∧ IsUTermVec L k v :=
  ⟨by intro h
      rcases h.case with (⟨k, r, v, hkr, hv, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact mk (Or.inl ⟨k, r, v, hkr, hv, rfl⟩)⟩

set_option linter.flexible false in
@[simp] lemma nrel {k r v : V} :
    IsUFormula L (^nrel k r v) ↔ L.IsRel k r ∧ IsUTermVec L k v :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨k, r, v, hkr, hv, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact mk (Or.inr <| Or.inl ⟨k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma verum : IsUFormula L (^⊤ : V) :=
  mk (Or.inr <| Or.inr <| Or.inl rfl)

@[simp] lemma falsum : IsUFormula L (^⊥ : V) :=
  mk (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)

set_option linter.flexible false in
@[simp] lemma and {p q : V} :
    IsUFormula L (p ^⋏ q) ↔ IsUFormula L p ∧ IsUFormula L q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, hp, hq, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p, q, hp, hq, rfl⟩)⟩

set_option linter.flexible false in
@[simp] lemma or {p q : V} :
    IsUFormula L (p ^⋎ q) ↔ IsUFormula L p ∧ IsUFormula L q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, hp, hq, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p, q, hp, hq, rfl⟩)⟩

set_option linter.flexible false in
@[simp] lemma all {p : V} :
    IsUFormula L (^∀ p) ↔ IsUFormula L p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, hp, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact hp,
   by rintro hp
      exact mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p, hp, rfl⟩)⟩

set_option linter.flexible false in
@[simp] lemma ex {p : V} :
    IsUFormula L (^∃ p) ↔ IsUFormula L p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, hp, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact hp,
   by rintro hp
      exact mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p, hp, rfl⟩)⟩

lemma pos {p : V} (h : IsUFormula L p) : 0 < p := by
  rcases h.case with (⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;>
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]

--lemma IsSemiformula.pos {n p : V} (h : Semiformula L n p) : 0 < p := h.1.pos

@[simp] lemma not_zero : ¬IsUFormula L (0 : V) := by intro h; simpa using h.pos

-- @[simp] lemma IsSemiformula.not_zero (m : V) : ¬Semiformula L m (0 : V) := by intro h; simpa using h.pos

/-
@[simp] lemma IsSemiformula.rel {k r v : V} :
    IsUFormula L (^rel k r v) ↔ L.IsRel k r ∧ IsUTermVec L k v := by simp
@[simp] lemma IsSemiformula.nrel {n k r v : V} :
    Semiformula L n (^nrel n k r v) ↔ L.IsRel k r ∧ SemitermVec L k n v := by simp [IsSemiformula]
@[simp] lemma IsSemiformula.verum (n : V) : Semiformula L n ^⊤[n] := by simp [IsSemiformula]
@[simp] lemma IsSemiformula.falsum (n : V) : Semiformula L n ^⊥[n] := by simp [IsSemiformula]
@[simp] lemma IsSemiformula.and {n p q : V} :
    Semiformula L n (p ^⋏ q) ↔ Semiformula L n p ∧ Semiformula L n q := by simp [IsSemiformula]
@[simp] lemma IsSemiformula.or {n p q : V} :
    Semiformula L n (p ^⋎ q) ↔ Semiformula L n p ∧ Semiformula L n q := by simp [IsSemiformula]
@[simp] lemma IsSemiformula.all {n p : V} : Semiformula L n (^∀ p) ↔ Semiformula L (n + 1) p := by simp [IsSemiformula]
@[simp] lemma IsSemiformula.ex {n p : V} : Semiformula L n (^∃ p) ↔ Semiformula L (n + 1) p := by simp [IsSemiformula]
-/

lemma induction1 (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hex : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p :=
  (construction L).induction (v := ![]) hP (by
    rintro C hC x (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ |
      ⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact hrel k r v hkr hv
    · exact hnrel k r v hkr hv
    · exact hverum
    · exact hfalsum
    · exact hand p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hor p q (hC p hp).1 (hC q hq).1 (hC p hp).2 (hC q hq).2
    · exact hall p (hC p hp).1 (hC p hp).2
    · exact hex p (hC p hp).1 (hC p hp).2)

lemma ISigma1.sigma1_succ_induction {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hex : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p :=
  induction1 𝚺 hP hrel hnrel hverum hfalsum hand hor hall hex

lemma ISigma1.pi1_succ_induction {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hex : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p :=
  induction1 𝚷 hP hrel hnrel hverum hfalsum hand hor hall hex

/-
lemma IsSemiformula.induction (Γ) {P : V → V → Prop} (hP : Γ-[1]-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, Semiformula L n p → P n p := by
  suffices ∀ p, IsUFormula L p → ∀ n ≤ p, fstIdx p = n → P n p
  by rintro n p ⟨h, rfl⟩; exact this p h (fstIdx p) (by simp) rfl
  apply IsUFormula.induction (P := fun p ↦ ∀ n ≤ p, fstIdx p = n → P n p) Γ
  · apply HierarchySymbol.Boldface.ball_le (by definability)
    apply HierarchySymbol.Boldface.imp (by definability)
    simp; exact hP
  · rintro n k r v hr hv _ _ rfl; simpa using hrel n k r v hr hv
  · rintro n k r v hr hv _ _ rfl; simpa using hnrel n k r v hr hv
  · rintro n _ _ rfl; simpa using hverum n
  · rintro n _ _ rfl; simpa using hfalsum n
  · rintro n p q hp hq ihp ihq _ _ rfl
    simpa using hand n p q hp hq
      (by simpa [hp.2] using ihp (fstIdx p) (by simp) rfl) (by simpa [hq.2] using ihq (fstIdx q) (by simp) rfl)
  · rintro n p q hp hq ihp ihq _ _ rfl
    simpa using hor n p q hp hq
      (by simpa [hp.2] using ihp (fstIdx p) (by simp) rfl) (by simpa [hq.2] using ihq (fstIdx q) (by simp) rfl)
  · rintro n p hp ih _ _ rfl
    simpa using hall n p hp (by simpa [hp.2] using ih (fstIdx p) (by simp) rfl)
  · rintro n p hp ih _ _ rfl
    simpa using hex n p hp (by simpa [hp.2] using ih (fstIdx p) (by simp) rfl)

lemma IsSemiformula.induction_sigma₁ {P : V → V → Prop} (hP : 𝚺₁-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, Semiformula L n p → P n p :=
  IsSemiformula.induction 𝚺 hP hrel hnrel hverum hfalsum hand hor hall hex

lemma IsSemiformula.pi1_structural_induction {P : V → V → Prop} (hP : 𝚷₁-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, Semiformula L n p → P n p :=
  IsSemiformula.induction 𝚷 hP hrel hnrel hverum hfalsum hand hor hall hex
-/

end IsUFormula

namespace UformulaRec1

structure Blueprint where
  rel        : 𝚺₁.Semisentence 5
  nrel       : 𝚺₁.Semisentence 5
  verum      : 𝚺₁.Semisentence 2
  falsum     : 𝚺₁.Semisentence 2
  and        : 𝚺₁.Semisentence 6
  or         : 𝚺₁.Semisentence 6
  all        : 𝚺₁.Semisentence 4
  ex         : 𝚺₁.Semisentence 4
  allChanges : 𝚺₁.Semisentence 2
  exChanges  : 𝚺₁.Semisentence 2

namespace Blueprint

variable (L) (β : Blueprint)

def blueprint (β : Blueprint) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C.
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !(isUFormula L).sigma p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p k R v ∧ !β.rel y param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p k R v ∧ !β.nrel y param k R v) ∨
    (!qqVerumDef p ∧ !β.verum y param) ∨
    (!qqFalsumDef p ∧ !β.falsum y param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqAndDef p p₁ p₂ ∧ !β.and y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqOrDef p p₁ p₂ ∧ !β.or y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      (∃ param', !β.allChanges param' param ∧ :⟪param', p₁, y₁⟫:∈ C) ∧ !qqAllDef p p₁ ∧ !β.all y param p₁ y₁) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      (∃ param', !β.exChanges param' param ∧ :⟪param', p₁, y₁⟫:∈ C) ∧ !qqExDef p p₁ ∧ !β.ex y param p₁ y₁))
  ”)
  (.mkPi “pr C.
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !(isUFormula L).pi p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, !qqRelDef p k R v ∧ !β.rel.graphDelta.pi.val y param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, !qqNRelDef p k R v ∧ !β.nrel.graphDelta.pi.val y param k R v) ∨
    (!qqVerumDef p ∧ !β.verum.graphDelta.pi.val y param) ∨
    (!qqFalsumDef p ∧ !β.falsum.graphDelta.pi.val y param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqAndDef p p₁ p₂ ∧ !β.and.graphDelta.pi.val y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      :⟪param, p₁, y₁⟫:∈ C ∧ :⟪param, p₂, y₂⟫:∈ C ∧ !qqOrDef p p₁ p₂ ∧ !β.or.graphDelta.pi.val y param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      (∀ param', !β.allChanges param' param → :⟪param', p₁, y₁⟫:∈ C) ∧ !qqAllDef p p₁ ∧ !β.all.graphDelta.pi.val y param p₁ y₁) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      (∀ param', !β.exChanges param' param → :⟪param', p₁, y₁⟫:∈ C) ∧ !qqExDef p p₁ ∧ !β.ex.graphDelta.pi.val y param p₁ y₁))
  ”)⟩

def graph : 𝚺₁.Semisentence 3 := .mkSigma
  “param p y. ∃ pr, !pair₃Def pr param p y ∧ !(β.blueprint L).fixpointDef pr”

def result : 𝚺₁.Semisentence 3 := .mkSigma
  “y param p. (!(isUFormula L).pi p → !(β.graph L) param p y) ∧ (¬!(isUFormula L).sigma p → y = 0)”

end Blueprint

variable (V)

structure Construction (φ : Blueprint) where
  rel        (param k R v : V) : V
  nrel       (param k R v : V) : V
  verum      (param : V) : V
  falsum     (param : V) : V
  and        (param p₁ p₂ y₁ y₂ : V) : V
  or         (param p₁ p₂ y₁ y₂ : V) : V
  all        (param p₁ y₁ : V) : V
  ex         (param p₁ y₁ : V) : V
  allChanges (param : V) : V
  exChanges  (param : V) : V
  rel_defined    : 𝚺₁-Function₄ rel via φ.rel
  nrel_defined   : 𝚺₁-Function₄ nrel via φ.nrel
  verum_defined  : 𝚺₁-Function₁ verum via φ.verum
  falsum_defined : 𝚺₁-Function₁ falsum via φ.falsum
  and_defined    : 𝚺₁-Function₅ and via φ.and
  or_defined     : 𝚺₁-Function₅ or via φ.or
  all_defined    : 𝚺₁-Function₃ all via φ.all
  ex_defined     : 𝚺₁-Function₃ ex via φ.ex
  allChanges_defined : 𝚺₁-Function₁ allChanges via φ.allChanges
  exChanges_defined  : 𝚺₁-Function₁ exChanges via φ.exChanges

variable {V}

namespace Construction

variable (L) {β : Blueprint} (c : Construction V β)

def Phi (C : Set V) (pr : V) : Prop :=
  ∃ param p y, pr = ⟪param, p, y⟫ ∧
  IsUFormula L p ∧ (
  (∃ k r v, p = ^rel k r v ∧ y = c.rel param k r v) ∨
  (∃ k r v, p = ^nrel k r v ∧ y = c.nrel param k r v) ∨
  (p = ^⊤ ∧ y = c.verum param) ∨
  (p = ^⊥ ∧ y = c.falsum param) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧ y = c.or  param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ y₁, ⟪c.allChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∀ p₁ ∧ y = c.all param p₁ y₁) ∨
  (∃ p₁ y₁, ⟪c.exChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∃ p₁ ∧ y = c.ex  param p₁ y₁) )

private lemma phi_iff (C pr : V) :
    c.Phi L {x | x ∈ C} pr ↔
    ∃ param ≤ pr, ∃ p ≤ pr, ∃ y ≤ pr, pr = ⟪param, p, y⟫ ∧ IsUFormula L p ∧
    ((∃ k < p, ∃ R < p, ∃ v < p, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k < p, ∃ R < p, ∃ v < p, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, ∃ y₁ < C, ∃ y₂ < C,
      ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧ y = c.or param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      ⟪c.allChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∀ p₁ ∧ y = c.all param p₁ y₁) ∨
    (∃ p₁ < p, ∃ y₁ < C,
      ⟪c.exChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∃ p₁ ∧ y = c.ex param p₁ y₁)) := by
  constructor
  · rintro ⟨param, p, y, rfl, hp, H⟩
    refine ⟨param, by simp,
      p, le_trans (le_pair_left p y) (le_pair_right _ _),
      y, le_trans (le_pair_right p y) (le_pair_right _ _), rfl, hp, ?_⟩
    rcases H with (⟨k, r, v, rfl, rfl⟩ | ⟨k, r, v, rfl, rfl⟩ | H)
    · left; exact ⟨k, by simp, r, by simp, v, by simp, rfl, rfl⟩
    · right; left; exact ⟨k, by simp, r, by simp, v, by simp, rfl, rfl⟩
    right; right
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | H)
    · left; exact ⟨rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), y₂, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₂),
        h₁, h₂, rfl, rfl⟩
    · right; left; exact ⟨p₁, by simp, p₂, by simp,
        y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), y₂, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₂),
        h₁, h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, y₁, h₁, rfl, rfl⟩ | ⟨p₁, y₁, h₁, rfl, rfl⟩)
    · left; exact ⟨p₁, by simp, y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), h₁, rfl, rfl⟩
    · right; exact ⟨p₁, by simp, y₁, lt_of_le_of_lt (by simp) (lt_of_mem_rng h₁), h₁, rfl, rfl⟩
  · rintro ⟨param, _, p, _, y, _, rfl, hp, H⟩
    refine ⟨param, p, y, rfl, hp, ?_⟩
    rcases H with (⟨k, _, r, _, v, _, rfl, rfl⟩ | ⟨k, _, r, _, v, _, rfl, rfl⟩ | H)
    · left; exact ⟨k, r, v, rfl, rfl⟩
    · right; left; exact ⟨k, r, v, rfl, rfl⟩
    right; right
    rcases H with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | H)
    · left; exact ⟨rfl, rfl⟩
    · right; left; exact ⟨rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ |
      ⟨p₁, _, p₂, _, y₁, _, y₂, _, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩
    · right; left; exact ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, _, y₁, _, h₁, rfl, rfl⟩ | ⟨p₁, _, y₁, _, h₁, rfl, rfl⟩)
    · left; exact ⟨p₁, y₁, h₁, rfl, rfl⟩
    · right; exact ⟨p₁, y₁, h₁, rfl, rfl⟩

def construction : Fixpoint.Construction V (β.blueprint L) where
  Φ := fun _ ↦ c.Phi L
  defined :=
  ⟨by intro v
      /-
      simp? [HierarchySymbol.Semiformula.val_sigma, Blueprint.blueprint,
        L.isUFormula_defined.df.iff, L.isUFormula_defined.proper.iff',
        c.rel_defined.iff, c.rel_defined.graph_delta.proper.iff',
        c.nrel_defined.iff, c.nrel_defined.graph_delta.proper.iff',
        c.verum_defined.iff, c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.iff, c.falsum_defined.graph_delta.proper.iff',
        c.and_defined.iff, c.and_defined.graph_delta.proper.iff',
        c.or_defined.iff, c.or_defined.graph_delta.proper.iff',
        c.all_defined.iff, c.all_defined.graph_delta.proper.iff',
        c.ex_defined.iff, c.ex_defined.graph_delta.proper.iff',
        c.allChanges_defined.iff, c.allChanges_defined.graph_delta.proper.iff',
        c.exChanges_defined.iff, c.exChanges_defined.graph_delta.proper.iff']
      -/
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Blueprint.blueprint, Fin.isValue,
        HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.sigma_mkDelta,
        HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
        Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_two, Matrix.vecTail,
        Function.comp_apply, Fin.succ_zero_eq_one, LogicalConnective.HomClass.map_and,
        Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_three, Fin.succ_one_eq_two,
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton, eval_pair₃Def,
        IsUFormula.defined.df.iff, LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT,
        Matrix.cons_val_four, Matrix.cons_val_succ, eval_qqRelDef, Matrix.cons_app_five,
        c.rel_defined.iff, LogicalConnective.Prop.and_eq, eval_qqNRelDef, c.nrel_defined.iff,
        eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef, c.falsum_defined.iff,
        Matrix.cons_app_six, Matrix.cons_app_seven, Semiformula.eval_operator_four,
        Matrix.cons_app_eight, eval_memRel₃, eval_qqAndDef, c.and_defined.iff, eval_qqOrDef,
        c.or_defined.iff, Semiformula.eval_ex, c.allChanges_defined.iff, exists_eq_left,
        eval_qqAllDef, c.all_defined.iff, c.exChanges_defined.iff, eval_qqExDef, c.ex_defined.iff,
        LogicalConnective.Prop.or_eq, HierarchySymbol.Semiformula.pi_mkDelta,
        HierarchySymbol.Semiformula.val_mkPi, IsUFormula.defined.proper.iff',
        c.rel_defined.graph_delta.proper.iff', HierarchySymbol.Semiformula.graphDelta_val,
        c.nrel_defined.graph_delta.proper.iff', c.verum_defined.graph_delta.proper.iff',
        c.falsum_defined.graph_delta.proper.iff', c.and_defined.graph_delta.proper.iff',
        c.or_defined.graph_delta.proper.iff', Semiformula.eval_all,
        LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq, forall_eq,
        c.all_defined.graph_delta.proper.iff', c.ex_defined.graph_delta.proper.iff'],
    by  intro v
        /-
        simpa? [HierarchySymbol.Semiformula.val_sigma, Blueprint.blueprint,
          L.isUFormula_defined.df.iff,
          c.rel_defined.iff,
          c.nrel_defined.iff,
          c.verum_defined.iff,
          c.falsum_defined.iff,
          c.and_defined.iff,
          c.or_defined.iff,
          c.all_defined.iff,
          c.ex_defined.iff,
          c.allChanges_defined.iff,
          c.exChanges_defined.iff] using c.phi_iff _ _
        -/
        simpa only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Blueprint.blueprint,
          HierarchySymbol.Semiformula.val_sigma, HierarchySymbol.Semiformula.val_mkDelta,
          HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_bexLTSucc', Semiterm.val_bvar,
          Matrix.cons_val_one, Matrix.vecHead, Matrix.cons_val_two, Matrix.vecTail,
          Function.comp_apply, Fin.succ_zero_eq_one, LogicalConnective.HomClass.map_and,
          Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.cons_val_three, Fin.succ_one_eq_two,
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.constant_eq_singleton,
          eval_pair₃Def, IsUFormula.defined.df.iff, LogicalConnective.HomClass.map_or,
          Semiformula.eval_bexLT, Matrix.cons_val_four, Matrix.cons_val_succ, eval_qqRelDef,
          Matrix.cons_app_five, c.rel_defined.iff, LogicalConnective.Prop.and_eq, eval_qqNRelDef,
          c.nrel_defined.iff, eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef,
          c.falsum_defined.iff, Matrix.cons_app_six, Matrix.cons_app_seven,
          Semiformula.eval_operator_four, Matrix.cons_app_eight, eval_memRel₃, eval_qqAndDef,
          c.and_defined.iff, eval_qqOrDef, c.or_defined.iff, Semiformula.eval_ex,
          c.allChanges_defined.iff, exists_eq_left, eval_qqAllDef, c.all_defined.iff,
          c.exChanges_defined.iff, eval_qqExDef, c.ex_defined.iff,
          LogicalConnective.Prop.or_eq] using c.phi_iff L _ _⟩
  monotone := by
    unfold Phi
    rintro C C' hC _ _ ⟨param, p, y, rfl, hp, H⟩
    refine ⟨param, p, y, rfl, hp, ?_⟩
    rcases H with (h | h | h | h | H)
    · left; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; left; exact h
    right; right; right; right
    rcases H with (⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩ | H)
    · left; exact ⟨p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩
    · right; left; exact ⟨p₁, p₂, r₁, r₂, hC h₁, hC h₂, rfl, rfl⟩
    right; right
    rcases H with (⟨p₁, r₁, h₁, rfl, rfl⟩ | ⟨p₁, r₁, h₁, rfl, rfl⟩)
    · left; exact ⟨p₁, r₁, hC h₁, rfl, rfl⟩
    · right; exact ⟨p₁, r₁, hC h₁, rfl, rfl⟩

instance : (c.construction L).Finite where
  finite {C _ pr h} := by
    rcases h with ⟨param, p, y, rfl, hp, (h | h | h | h |
      ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, p₂, y₁, y₂, h₁, h₂, rfl, rfl⟩ | ⟨p₁, y₁, h₁, rfl, rfl⟩ | ⟨p₁, y₁, h₁, rfl, rfl⟩)⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inr <| Or.inl h⟩
    · exact ⟨0, param, _, _, rfl, hp, Or.inr <| Or.inr <| Or.inr <| Or.inl h⟩
    · exact ⟨Max.max ⟪param, p₁, y₁⟫ ⟪param, p₂, y₂⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; left
        exact ⟨p₁, p₂, y₁, y₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl, rfl⟩⟩
    · exact ⟨Max.max ⟪param, p₁, y₁⟫ ⟪param, p₂, y₂⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; left
        exact ⟨p₁, p₂, y₁, y₂, by simp [h₁, lt_succ_iff_le], by simp [h₂, lt_succ_iff_le], rfl, rfl⟩⟩
    · exact ⟨⟪c.allChanges param, p₁, y₁⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; right; left
        exact ⟨p₁, y₁, by simp [h₁], rfl, rfl⟩⟩
    · exact ⟨⟪c.exChanges param, p₁, y₁⟫ + 1, param, _, _, rfl, hp, by
        right; right; right; right; right; right; right
        exact ⟨p₁, y₁, by simp [h₁], rfl, rfl⟩⟩

def Graph (param : V) (x y : V) : Prop := (c.construction L).Fixpoint ![] ⟪param, x, y⟫

variable {param : V}

variable {L c}

lemma Graph.case_iff {p y : V} :
    c.Graph L param p y ↔
    IsUFormula L p ∧ (
    (∃ k R v, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k R v, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph L param p₁ y₁ ∧ c.Graph L param p₂ y₂ ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph L param p₁ y₁ ∧ c.Graph L param p₂ y₂ ∧ p = p₁ ^⋎ p₂ ∧ y = c.or param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ y₁, c.Graph L (c.allChanges param) p₁ y₁ ∧ p = ^∀ p₁ ∧ y = c.all param p₁ y₁) ∨
    (∃ p₁ y₁, c.Graph L (c.exChanges param) p₁ y₁ ∧ p = ^∃ p₁ ∧ y = c.ex param p₁ y₁) ) :=
  Iff.trans (c.construction L).case (by
    constructor
    · rintro ⟨param, p', y', e, H⟩;
      rcases show _ = param ∧ p = p' ∧ y = y' by simpa using e with ⟨rfl, rfl, rfl⟩
      refine H
    · intro H; exact ⟨_, _, _, rfl, H⟩)

variable (c β)

lemma graph_defined : 𝚺₁-Relation₃ c.Graph L via β.graph L := by
  intro v; simp [Blueprint.graph, (c.construction L).fixpoint_defined.iff, Matrix.empty_eq]; rfl

@[simp] lemma eval_graphDef (v) :
    Semiformula.Evalbm V v (β.graph L).val ↔ c.Graph L (v 0) (v 1) (v 2) := (graph_defined β c).df.iff v

instance graph_definable : 𝚺-[0 + 1]-Relation₃ c.Graph L := c.graph_defined.to_definable

variable {β}

lemma graph_dom_uformula {p r} :
    c.Graph L param p r → IsUFormula L p := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_rel_iff {k r v y} (hkr : L.IsRel k r) (hv : IsUTermVec L k v) :
    c.Graph L param (^rel k r v) y ↔ y = c.rel param k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨k, r, v, H, rfl⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · rcases (by simpa [qqRel] using H) with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · simp [qqRel, qqNRel] at H
    · simp [qqRel, qqVerum] at H
    · simp [qqRel, qqFalsum] at H
    · simp [qqRel, qqAnd] at H
    · simp [qqRel, qqOr] at H
    · simp [qqRel, qqAll] at H
    · simp [qqRel, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_nrel_iff {k r v y} (hkr : L.IsRel k r) (hv : IsUTermVec L k v) :
    c.Graph L param (^nrel k r v) y ↔ y = c.nrel param k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqNRel, qqRel] at H
    · rcases (by simpa [qqNRel] using H) with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · simp [qqNRel, qqVerum] at H
    · simp [qqNRel, qqFalsum] at H
    · simp [qqNRel, qqAnd] at H
    · simp [qqNRel, qqOr] at H
    · simp [qqNRel, qqAll] at H
    · simp [qqNRel, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_verum_iff {y} :
    c.Graph L param ^⊤ y ↔ y = c.verum param := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, rfl⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqVerum, qqRel] at H
    · simp [qqVerum, qqNRel] at H
    · rcases (by simpa [qqVerum] using H); rfl
    · simp [qqVerum, qqFalsum] at H
    · simp [qqVerum, qqAnd] at H
    · simp [qqVerum, qqOr] at H
    · simp [qqVerum, qqAll] at H
    · simp [qqVerum, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_falsum_iff {y} :
    c.Graph L param ^⊥ y ↔ y = c.falsum param := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, rfl⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqFalsum, qqRel] at H
    · simp [qqFalsum, qqNRel] at H
    · simp [qqFalsum, qqVerum] at H
    · rcases (by simpa [qqFalsum] using H); rfl
    · simp [qqFalsum, qqAnd] at H
    · simp [qqFalsum, qqOr] at H
    · simp [qqFalsum, qqAll] at H
    · simp [qqFalsum, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_rel {k r v} (hkr : L.IsRel k r) (hv : IsUTermVec L k v) :
    c.Graph L param (^rel k r v) (c.rel param k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_nrel {k r v} (hkr : L.IsRel k r) (hv : IsUTermVec L k v) :
    c.Graph L param (^nrel k r v) (c.nrel param k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_verum :
    c.Graph L param ^⊤ (c.verum param) := (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_falsum :
    c.Graph L param ^⊥ (c.falsum param) := (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_and {p₁ p₂ r₁ r₂ : V} (hp₁ : IsUFormula L p₁) (hp₂ : IsUFormula L p₂)
    (h₁ : c.Graph L param p₁ r₁) (h₂ : c.Graph L param p₂ r₂) :
    c.Graph L param (p₁ ^⋏ p₂) (c.and param p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_and_inv {p₁ p₂ r : V} :
    c.Graph L param (p₁ ^⋏ p₂) r → ∃ r₁ r₂, c.Graph L param p₁ r₁ ∧ c.Graph L param p₂ r₂ ∧ r = c.and param p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqAnd, qqRel] at H
  · simp [qqAnd, qqNRel] at H
  · simp [qqAnd, qqVerum] at H
  · simp [qqAnd, qqFalsum] at H
  · rcases (by simpa [qqAnd] using H) with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqAnd, qqOr] at H
  · simp [qqAnd, qqAll] at H
  · simp [qqAnd, qqEx] at H

lemma graph_or {p₁ p₂ r₁ r₂ : V} (hp₁ : IsUFormula L p₁) (hp₂ : IsUFormula L p₂)
    (h₁ : c.Graph L param p₁ r₁) (h₂ : c.Graph L param p₂ r₂) :
    c.Graph L param (p₁ ^⋎ p₂) (c.or param p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_or_inv {p₁ p₂ r : V} :
    c.Graph L param (p₁ ^⋎ p₂) r → ∃ r₁ r₂, c.Graph L param p₁ r₁ ∧ c.Graph L param p₂ r₂ ∧ r = c.or param p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqOr, qqRel] at H
  · simp [qqOr, qqNRel] at H
  · simp [qqOr, qqVerum] at H
  · simp [qqOr, qqFalsum] at H
  · simp [qqOr, qqAnd] at H
  · rcases (by simpa [qqOr] using H) with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqOr, qqAll] at H
  · simp [qqOr, qqEx] at H

lemma graph_all {p₁ r₁ : V} (hp₁ : IsUFormula L p₁) (h₁ : c.Graph L (c.allChanges param) p₁ r₁) :
    c.Graph L param (^∀ p₁) (c.all param p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_all_inv {p₁ r : V} :
    c.Graph L param (^∀ p₁) r → ∃ r₁, c.Graph L (c.allChanges param) p₁ r₁ ∧ r = c.all param p₁ r₁ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqAll, qqRel] at H
  · simp [qqAll, qqNRel] at H
  · simp [qqAll, qqVerum] at H
  · simp [qqAll, qqFalsum] at H
  · simp [qqAll, qqAnd] at H
  · simp [qqAll, qqOr] at H
  · rcases (by simpa [qqAll] using H) with ⟨rfl, rfl⟩
    exact ⟨_, by assumption, rfl⟩
  · simp [qqAll, qqEx] at H

lemma graph_ex {p₁ r₁ : V} (hp₁ : IsUFormula L p₁) (h₁ : c.Graph L (c.exChanges param) p₁ r₁) :
    c.Graph L param (^∃ p₁) (c.ex param p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_ex_inv {p₁ r : V} :
    c.Graph L param (^∃ p₁) r → ∃ r₁, c.Graph L (c.exChanges param) p₁ r₁ ∧ r = c.ex param p₁ r₁ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩)⟩
  · simp [qqEx, qqRel] at H
  · simp [qqEx, qqNRel] at H
  · simp [qqEx, qqVerum] at H
  · simp [qqEx, qqFalsum] at H
  · simp [qqEx, qqAnd] at H
  · simp [qqEx, qqOr] at H
  · simp [qqEx, qqAll] at H
  · rcases (by simpa [qqEx] using H) with ⟨rfl, rfl⟩
    exact ⟨_, by assumption, rfl⟩

variable (param)

lemma graph_exists {p : V} : IsUFormula L p → ∃ y, c.Graph L param p y := by
  haveI : 𝚺₁-Function₁ c.allChanges := c.allChanges_defined.to_definable
  haveI : 𝚺₁-Function₁ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V := fun _ param ↦ Max.max param (Max.max (c.allChanges param) (c.exChanges param))
  have hf : 𝚺₁-Function₂ f := by definability
  apply bounded_all_sigma1_order_induction hf ?_ ?_ p param
  · definability
  intro p param ih hp
  rcases hp.case with
    (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ |
    rfl | rfl |
    ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ |
    ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  · exact ⟨c.rel param k r v, c.graph_rel hkr hv⟩
  · exact ⟨c.nrel param k r v, c.graph_nrel hkr hv⟩
  · exact ⟨c.verum param, c.graph_verum⟩
  · exact ⟨c.falsum param, c.graph_falsum⟩
  · rcases ih p₁ (by simp) param (by simp [f]) hp₁ with ⟨y₁, h₁⟩
    rcases ih p₂ (by simp) param (by simp [f]) hp₂ with ⟨y₂, h₂⟩
    exact ⟨c.and param p₁ p₂ y₁ y₂, c.graph_and hp₁ hp₂ h₁ h₂⟩
  · rcases ih p₁ (by simp) param (by simp [f]) hp₁ with ⟨y₁, h₁⟩
    rcases ih p₂ (by simp) param (by simp [f]) hp₂ with ⟨y₂, h₂⟩
    exact ⟨c.or param p₁ p₂ y₁ y₂, c.graph_or hp₁ hp₂ h₁ h₂⟩
  · rcases ih p₁ (by simp) (c.allChanges param) (by simp [f]) hp₁ with ⟨y₁, h₁⟩
    exact ⟨c.all param p₁ y₁, c.graph_all hp₁ h₁⟩
  · rcases ih p₁ (by simp) (c.exChanges param) (by simp [f]) hp₁ with ⟨y₁, h₁⟩
    exact ⟨c.ex param p₁ y₁, c.graph_ex hp₁ h₁⟩

lemma graph_unique {p : V} : IsUFormula L p → ∀ {param r r'}, c.Graph L param p r → c.Graph L param p r' → r = r' := by
  apply IsUFormula.ISigma1.pi1_succ_induction (P := fun p ↦ ∀ {param r r'}, c.Graph L param p r → c.Graph L param p r' → r = r')
    (by definability)
  case hrel =>
    intro k R v hkR hv
    simp [c.graph_rel_iff hkR hv]
  case hnrel =>
    intro k R v hkR hv
    simp [c.graph_nrel_iff hkR hv]
  case hverum =>
    simp [c.graph_verum_iff]
  case hfalsum =>
    simp [c.graph_falsum_iff]
  case hand =>
    intro p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr'
    rcases c.graph_and_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_and_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hor =>
    intro p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr'
    rcases c.graph_or_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_or_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hall =>
    intro p _ ih param r r' hr hr'
    rcases c.graph_all_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_all_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl
  case hex =>
    intro p _ ih param r r' hr hr'
    rcases c.graph_ex_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_ex_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl

lemma exists_unique {p : V} (hp : IsUFormula L p) : ∃! r, c.Graph L param p r := by
  rcases c.graph_exists param hp with ⟨r, hr⟩
  exact ExistsUnique.intro r hr (fun r' hr' ↦ c.graph_unique hp hr' hr)

variable (L)

lemma exists_unique_all (p : V) : ∃! r, (IsUFormula L p → c.Graph L param p r) ∧ (¬IsUFormula L p → r = 0) := by
  by_cases hp : IsUFormula L p <;> simp [hp, exists_unique]

noncomputable def result (p : V) : V := Classical.choose! (c.exists_unique_all L param p)

variable {L}

lemma result_prop {p : V} (hp : IsUFormula L p) : c.Graph L param p (c.result L param p) :=
  Classical.choose!_spec (c.exists_unique_all L param p) |>.1 hp

lemma result_prop_not {p : V} (hp : ¬IsUFormula L p) : c.result L param p = 0 :=
  Classical.choose!_spec (c.exists_unique_all L param p) |>.2 hp

variable {param}

lemma result_eq_of_graph {p r} (h : c.Graph L param p r) : c.result L param p = r := Eq.symm <|
  Classical.choose_uniq (c.exists_unique_all L param p) (by simp [c.graph_dom_uformula h, h])

@[simp] lemma result_rel {k R v} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    c.result L param (^rel k R v) = c.rel param k R v :=
  c.result_eq_of_graph (c.graph_rel hR hv)

@[simp] lemma result_nrel {k R v} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    c.result L param (^nrel k R v) = c.nrel param k R v :=
  c.result_eq_of_graph (c.graph_nrel hR hv)

@[simp] lemma result_verum : c.result L param ^⊤ = c.verum param := c.result_eq_of_graph c.graph_verum

@[simp] lemma result_falsum : c.result L param ^⊥ = c.falsum param := c.result_eq_of_graph c.graph_falsum

@[simp] lemma result_and {p q}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    c.result L param (p ^⋏ q) = c.and param p q (c.result L param p) (c.result L param q) :=
  c.result_eq_of_graph (c.graph_and hp hq (c.result_prop param hp) (c.result_prop param hq))

@[simp] lemma result_or {p q}
    (hp : IsUFormula L p) (hq : IsUFormula L q) :
    c.result L param (p ^⋎ q) = c.or param p q (c.result L param p) (c.result L param q) :=
  c.result_eq_of_graph (c.graph_or hp hq (c.result_prop param hp) (c.result_prop param hq))

@[simp] lemma result_all {p} (hp : IsUFormula L p) :
    c.result L param (^∀ p) = c.all param p (c.result L (c.allChanges param) p) :=
  c.result_eq_of_graph (c.graph_all hp (c.result_prop (c.allChanges param) hp))

@[simp] lemma result_ex {p} (hp : IsUFormula L p) :
    c.result L param (^∃ p) = c.ex param p (c.result L (c.exChanges param) p) :=
  c.result_eq_of_graph (c.graph_ex hp (c.result_prop _ hp))

section

lemma result_defined : 𝚺₁-Function₂ c.result L via β.result L := by
  intro v
  simpa [Blueprint.result, HierarchySymbol.Semiformula.val_sigma,
    IsUFormula.defined.df.iff, IsUFormula.defined.proper.iff', c.eval_graphDef]
  using Classical.choose!_eq_iff (c.exists_unique_all L (v 1) (v 2))

instance result_definable : 𝚺-[0 + 1]-Function₂ c.result L := c.result_defined.to_definable

end

lemma uformula_result_induction {P : V → V → V → Prop} (hP : 𝚺₁-Relation₃ P)
    (hRel : ∀ param k R v, L.IsRel k R → IsUTermVec L k v → P param (^rel k R v) (c.rel param k R v))
    (hNRel : ∀ param k R v, L.IsRel k R → IsUTermVec L k v → P param (^nrel k R v) (c.nrel param k R v))
    (hverum : ∀ param, P param ^⊤ (c.verum param))
    (hfalsum : ∀ param, P param ^⊥ (c.falsum param))
    (hand : ∀ param p q, IsUFormula L p → IsUFormula L q →
      P param p (c.result L param p) → P param q (c.result L param q) → P param (p ^⋏ q) (c.and param p q (c.result L param p) (c.result L param q)))
    (hor : ∀ param p q, IsUFormula L p → IsUFormula L q →
      P param p (c.result L param p) → P param q (c.result L param q) → P param (p ^⋎ q) (c.or param p q (c.result L param p) (c.result L param q)))
    (hall : ∀ param p, IsUFormula L p →
      P (c.allChanges param) p (c.result L (c.allChanges param) p) →
      P param (^∀ p) (c.all param p (c.result L (c.allChanges param) p)))
    (hex : ∀ param p, IsUFormula L p →
      P (c.exChanges param) p (c.result L (c.exChanges param) p) →
      P param (^∃ p) (c.ex param p (c.result L (c.exChanges param) p))) :
    ∀ {param p : V}, IsUFormula L p → P param p (c.result L param p) := by
  haveI : 𝚺₁-Function₂ c.result L := c.result_definable
  haveI : 𝚺₁-Function₁ c.allChanges := c.allChanges_defined.to_definable
  haveI : 𝚺₁-Function₁ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V := fun _ param ↦ Max.max param (Max.max (c.allChanges param) (c.exChanges param))
  have hf : 𝚺₁-Function₂ f := by definability
  intro param p
  apply bounded_all_sigma1_order_induction hf ?_ ?_ p param
  · apply HierarchySymbol.Boldface.imp
      (HierarchySymbol.Boldface.comp₁ (HierarchySymbol.BoldfaceFunction.var _))
      (HierarchySymbol.Boldface.comp₃
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.comp₂ (HierarchySymbol.BoldfaceFunction.var _) (HierarchySymbol.BoldfaceFunction.var _)))
  intro p param ih hp
  rcases hp.case with
    (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
  · simpa [hkr, hv] using hRel param k r v hkr hv
  · simpa [hkr, hv] using hNRel param k r v hkr hv
  · simpa using hverum param
  · simpa using hfalsum param
  · simpa [c.result_and hp₁ hp₂] using
      hand param p₁ p₂ hp₁ hp₂ (ih p₁ (by simp) param (by simp [f]) hp₁) (ih p₂ (by simp) param (by simp [f]) hp₂)
  · simpa [c.result_or hp₁ hp₂] using
      hor param p₁ p₂ hp₁ hp₂ (ih p₁ (by simp) param (by simp [f]) hp₁) (ih p₂ (by simp) param (by simp [f]) hp₂)
  · simpa [c.result_all hp₁] using
      hall param p₁ hp₁ (ih p₁ (by simp) (c.allChanges param) (by simp [f]) hp₁)
  · simpa [c.result_ex hp₁] using
      hex param p₁ hp₁ (ih p₁ (by simp) (c.exChanges param) (by simp [f]) hp₁)

/-
lemma semiformula_result_induction {P : V → V → V → V → Prop} (hP : 𝚺₁-Relation₄ P)
    (hRel : ∀ param k R v, L.IsRel k R → SemitermVec L k n v → P param (^rel n k R v) (c.rel param k R v))
    (hNRel : ∀ param k R v, L.IsRel k R → SemitermVec L k n v → P param (^nrel n k R v) (c.nrel param k R v))
    (hverum : ∀ param, P param (^⊤[n]) (c.verum param))
    (hfalsum : ∀ param, P param (^⊥[n]) (c.falsum param))
    (hand : ∀ param p q, Semiformula L n p → Semiformula L n q →
      P param p (c.result L param p) → P param q (c.result L param q) → P param (p ^⋏ q) (c.and param p q (c.result L param p) (c.result L param q)))
    (hor : ∀ param p q, Semiformula L n p → Semiformula L n q →
      P param p (c.result L param p) → P param q (c.result L param q) → P param (p ^⋎ q) (c.or param p q (c.result L param p) (c.result L param q)))
    (hall : ∀ param p, Semiformula L (n + 1) p →
      P (c.allChanges param) (n + 1) p (c.result L (c.allChanges param) p) →
      P param (^∀ p) (c.all param p (c.result L (c.allChanges param) p)))
    (hex : ∀ param p, Semiformula L (n + 1) p →
      P (c.exChanges param) (n + 1) p (c.result L (c.exChanges param) p) →
      P param (^∃ p) (c.ex param p (c.result L (c.exChanges param) p))) :
    ∀ {param p : V}, Semiformula L n p → P param p (c.result L param p) := by
  suffices ∀ {param p : V}, IsUFormula L p → ∀ n ≤ p, n = fstIdx p → P param p (c.result L param p)
  by intro param p hp; exact @this param p hp.1 n (by simp [hp.2]) hp.2
  intro param p hp
  apply c.uformula_result_induction (P := fun param p y ↦ ∀ n ≤ p, n = fstIdx p → P param p y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · apply HierarchySymbol.Boldface.ball_le (HierarchySymbol.BoldfaceFunction.var _)
    simp_all only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two,
      Fin.succ_zero_eq_one]
    apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.imp
    · simp_all only [SigmaPiDelta.alt_sigma, Fin.isValue]
      apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.comp₂
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue]
        apply LO.FirstOrder.Arithmetic.HierarchySymbol.BoldfaceFunction.comp₁
        simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
    · apply LO.FirstOrder.Arithmetic.HierarchySymbol.Boldface.comp₄
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue]
        apply LO.FirstOrder.Arithmetic.HierarchySymbol.BoldfaceFunction.comp₁
        simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
  · rintro param k R v hkR hv _ _ rfl; simpa using hRel param k R v hkR hv
  · rintro param k R v hkR hv _ _ rfl; simpa using hNRel param k R v hkR hv
  · rintro param _ _ rfl; simpa using hverum param
  · rintro param _ _ rfl; simpa using hfalsum param
  · rintro param p q hp hq ihp ihq _ _ rfl
    have ihp : P param p (c.result L param p) := ihp n (by simp [hp.2]) hp.2
    have ihq : P param q (c.result L param q) := ihq n (by simp [hq.2]) hq.2
    simpa using hand param p q hp hq ihp ihq
  · rintro param p q hp hq ihp ihq _ _ rfl
    have ihp : P param p (c.result L param p) := ihp n (by simp [hp.2]) hp.2
    have ihq : P param q (c.result L param q) := ihq n (by simp [hq.2]) hq.2
    simpa using hor param p q hp hq ihp ihq
  · rintro param p hp ihp _ _ rfl
    have ihp : P (c.allChanges param) (n + 1) p (c.result L (c.allChanges param) p) := ihp (n + 1) (by simp [hp.2]) hp.2
    simpa using hall param p hp ihp
  · rintro param p hp ihp _ _ rfl
    have ihp : P (c.exChanges param) (n + 1) p (c.result L (c.exChanges param) p) := ihp (n + 1) (by simp [hp.2]) hp.2
    simpa using hex param p hp ihp
-/

end Construction

end UformulaRec1

section bv

namespace BV

variable (L)

def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ M, !(termBVVecGraph L) M k v ∧ !listMaxDef y M”
  nrel := .mkSigma “y param k R v. ∃ M, !(termBVVecGraph L) M k v ∧ !listMaxDef y M”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !Arithmetic.max y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !Arithmetic.max y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. !subDef y y₁ 1”
  ex := .mkSigma “y param p₁ y₁. !subDef y y₁ 1”
  allChanges := .mkSigma “param' param. param' = 0”
  exChanges := .mkSigma “param' param. param' = 0”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k _ v ↦ listMax (termBVVec L k v)
  nrel {_} := fun k _ v ↦ listMax (termBVVec L k v)
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  or {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  all {_} := fun _ y₁ ↦ y₁ - 1
  ex {_} := fun _ y₁ ↦ y₁ - 1
  allChanges := fun _ ↦ 0
  exChanges := fun _ ↦ 0
  rel_defined := by intro v; simp [blueprint, termBVVec.defined.df.iff]
  nrel_defined := by intro v; simp [blueprint, termBVVec.defined.df.iff]
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]
  or_defined := by intro v; simp [blueprint]
  all_defined := by intro v; simp [blueprint]
  ex_defined := by intro v; simp [blueprint]
  allChanges_defined := by intro v; simp [blueprint]
  exChanges_defined := by intro v; simp [blueprint]

end BV

open BV

variable (L)

noncomputable def bv (p : V) : V := (BV.construction L).result L 0 p

def bvGraph : 𝚺₁.Semisentence 2 := ((BV.blueprint L).result L).rew (Rew.substs ![#0, ‘0’, #1])

variable {L}

section

lemma bv.defined : 𝚺₁-Function₁ bv (V := V) L via bvGraph L := fun v ↦ by
  simpa [bvGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using (BV.construction L).result_defined ![v 0, 0, v 1]

instance bv.definable : 𝚺₁-Function₁ bv (V := V) L := bv.defined.to_definable

instance bv.definable' : Γ-[m + 1]-Function₁ bv (V := V) L := bv.definable.of_sigmaOne

end

@[simp] lemma bv_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    bv L (^rel k R v) = listMax (termBVVec L k v) := by simp [bv, hR, hv, BV.construction]

@[simp] lemma bv_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    bv L (^nrel k R v) = listMax (termBVVec L k v) := by simp [bv, hR, hv, BV.construction]

@[simp] lemma bv_verum : bv L (^⊤ : V) = 0 := by simp [bv, BV.construction]

@[simp] lemma bv_falsum : bv L (^⊥ : V) = 0 := by simp [bv, BV.construction]

@[simp] lemma bv_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bv L (p ^⋏ q) = Max.max (bv L p) (bv L q) := by simp [bv, hp, hq, BV.construction]

@[simp] lemma bv_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bv L (p ^⋎ q) = Max.max (bv L p) (bv L q) := by simp [bv, hp, hq, construction]

@[simp] lemma bv_all {p : V} (hp : IsUFormula L p) : bv L (^∀ p) = bv L p - 1 := by simp [bv, hp, construction]

@[simp] lemma bv_ex {p : V} (hp : IsUFormula L p) : bv L (^∃ p) = bv L p - 1 := by simp [bv, hp, construction]

lemma bv_eq_of_not_isUFormula {p : V} (h : ¬IsUFormula L p) : bv L p = 0 := (construction L).result_prop_not _ h

end bv

section isSemiformula

variable (L)

structure IsSemiformula (n p : V) : Prop where
  isUFormula : IsUFormula L p
  bv_le : bv L p ≤ n

abbrev IsFormula (p : V) : Prop := IsSemiformula L 0 p

def isSemiformula : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “n p. !(isUFormula L).sigma p ∧ ∃ b, !(bvGraph L) b p ∧ b ≤ n”)
  (.mkPi “n p. !(isUFormula L).pi p ∧ ∀ b, !(bvGraph L) b p → b ≤ n”)

variable {L}

lemma isSemiformula_iff {n p : V} :
    IsSemiformula L n p ↔ IsUFormula L p ∧ bv L p ≤ n :=
  ⟨fun h ↦ ⟨h.isUFormula, h.bv_le⟩, by rintro ⟨hp, h⟩; exact ⟨hp, h⟩⟩

section

lemma IsSemiformula.defined : 𝚫₁-Relation IsSemiformula (V := V) L via isSemiformula L := by
  constructor
  · intro v; simp [isSemiformula, HierarchySymbol.Semiformula.val_sigma,
      bv.defined.df.iff, IsUFormula.defined.proper.iff']
  · intro v; simp [isSemiformula, HierarchySymbol.Semiformula.val_sigma,
      bv.defined.df.iff, IsUFormula.defined.df.iff, isSemiformula_iff]

instance IsSemiformula.definable : 𝚫₁-Relation IsSemiformula (V := V) L := IsSemiformula.defined.to_definable

instance IsSemiformula.definable' : Γ-[m + 1]-Relation IsSemiformula (V := V) L := IsSemiformula.definable.of_deltaOne

end

@[simp] lemma IsUFormula.isSemiformula {p : V} (h : IsUFormula L p) : IsSemiformula L (bv L p) p where
  isUFormula := h
  bv_le := by rfl

@[simp] lemma IsSemiformula.rel {n k r v : V} :
    IsSemiformula L n (^rel k r v) ↔ L.IsRel k r ∧ IsSemitermVec L k n v := by
  constructor
  · intro h
    have hrv : L.IsRel k r ∧ IsUTermVec L k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun i hi ↦ by
      have : listMax (termBVVec L k v) ≤ n := by simpa [hrv] using h.bv_le
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_rel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma IsSemiformula.nrel {n k r v : V} :
    IsSemiformula L n (^nrel k r v) ↔ L.IsRel k r ∧ IsSemitermVec L k n v := by
  constructor
  · intro h
    have hrv : L.IsRel k r ∧ IsUTermVec L k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun i hi ↦ by
      have : listMax (termBVVec L k v) ≤ n := by simpa [hrv] using h.bv_le
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_nrel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma IsSemiformula.verum {n : V} : IsSemiformula L n ^⊤ := ⟨by simp, by simp⟩

@[simp] lemma IsSemiformula.falsum {n : V} : IsSemiformula L n ^⊥ := ⟨by simp, by simp⟩

@[simp] lemma IsSemiformula.and {n p q : V} :
    IsSemiformula L n (p ^⋏ q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  constructor
  · intro h
    have hpq : IsUFormula L p ∧ IsUFormula L q := by simpa using h.isUFormula
    have hbv : bv L p ≤ n ∧ bv L q ≤ n := by simpa [hpq] using h.bv_le
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv_le, hq.bv_le]⟩

@[simp] lemma IsSemiformula.or {n p q : V} :
    IsSemiformula L n (p ^⋎ q) ↔ IsSemiformula L n p ∧ IsSemiformula L n q := by
  constructor
  · intro h
    have hpq : IsUFormula L p ∧ IsUFormula L q := by simpa using h.isUFormula
    have hbv : bv L p ≤ n ∧ bv L q ≤ n := by simpa [hpq] using h.bv_le
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv_le, hq.bv_le]⟩

@[simp] lemma IsSemiformula.all {n p : V} :
    IsSemiformula L n (^∀ p) ↔ IsSemiformula L (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show IsUFormula L p by simpa using h.isUFormula] using h.bv_le⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv_le]⟩

@[simp] lemma IsSemiformula.ex {n p : V} :
    IsSemiformula L n (^∃ p) ↔ IsSemiformula L (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show IsUFormula L p by simpa using h.isUFormula] using h.bv_le⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv_le]⟩

lemma IsSemiformula.case_iff {n p : V} :
    IsSemiformula L n p ↔
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ p = ^rel k R v) ∨
    (∃ k R v, L.IsRel k R ∧ IsSemitermVec L k n v ∧ p = ^nrel k R v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ p₂, IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, IsSemiformula L (n + 1) p₁ ∧ p = ^∀ p₁) ∨
    (∃ p₁, IsSemiformula L (n + 1) p₁ ∧ p = ^∃ p₁) := by
  constructor
  · intro h
    rcases h.isUFormula.case with
      (⟨k, r, v, _, _, rfl⟩ | ⟨k, r, v, _, _, rfl⟩ | rfl | rfl | ⟨p₁, p₂, _, _, rfl⟩ | ⟨p₁, p₂, _, _, rfl⟩ | ⟨p₁, _, rfl⟩ | ⟨p₁, _, rfl⟩)
    · have : L.IsRel k r ∧ IsSemitermVec L k n v := by simpa using h
      exact Or.inl ⟨k, r, v, by simp [this]⟩
    · have : L.IsRel k r ∧ IsSemitermVec L k n v := by simpa using h
      exact Or.inr <| Or.inl ⟨k, r, v, by simp [this]⟩
    · exact Or.inr <| Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
    · have : IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ := by simpa using h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, by simp [this]⟩
    · have : IsSemiformula L n p₁ ∧ IsSemiformula L n p₂ := by simpa using h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, by simp [this]⟩
    · have : IsSemiformula L (n + 1) p₁ := by simpa using h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, by simp [this]⟩
    · have : IsSemiformula L (n + 1) p₁ := by simpa using h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p₁, by simp [this]⟩
  · rintro (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩) <;> simp [*]

lemma IsSemiformula.case {P : V → V → Prop} {n p} (hp : IsSemiformula L n p)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, IsSemiformula L (n + 1) p → P n (^∃ p)) : P n p := by
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · exact hrel _ _ _ _ hR hv
  · exact hnrel _ _ _ _ hR hv
  · exact hverum n
  · exact hfalsum n
  · exact hand _ _ _ h₁ h₂
  · exact hor _ _ _ h₁ h₂
  · exact hall _ _ h₁
  · exact hex _ _ h₁

lemma IsSemiformula.sigma1_structural_induction {P : V → V → Prop} (hP : 𝚺₁-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    IsSemiformula L n p → P n p := by
  have : 𝚺₁-Function₂ (fun _ (n : V) ↦ n + 1) := by definability
  apply bounded_all_sigma1_order_induction this ?_ ?_ p n
  · apply HierarchySymbol.Boldface.imp
    · apply HierarchySymbol.Boldface.comp₂ (HierarchySymbol.BoldfaceFunction.var _) (HierarchySymbol.BoldfaceFunction.var _)
    · apply HierarchySymbol.Boldface.comp₂ (HierarchySymbol.BoldfaceFunction.var _) (HierarchySymbol.BoldfaceFunction.var _)
  intro p n ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · apply hrel _ _ _ _ hR hv
  · apply hnrel _ _ _ _ hR hv
  · apply hverum
  · apply hfalsum
  · apply hand _ _ _ h₁ h₂ (ih p₁ (by simp) n (by simp) h₁) (ih p₂ (by simp) n (by simp) h₂)
  · apply hor _ _ _ h₁ h₂ (ih p₁ (by simp) n (by simp) h₁) (ih p₂ (by simp) n (by simp) h₂)
  · apply hall _ _ h₁ (ih p₁ (by simp) (n + 1) (by simp) h₁)
  · apply hex _ _ h₁ (ih p₁ (by simp) (n + 1) (by simp) h₁)

lemma IsSemiformula.pi1_structural_induction {P : V → V → Prop} (hP : 𝚷₁-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    IsSemiformula L n p → P n p := by
  suffices IsUFormula L p → ∀ n, IsSemiformula L n p → P n p by intro h; exact this h.isUFormula n h
  apply IsUFormula.ISigma1.pi1_succ_induction (P := fun p ↦ ∀ n, IsSemiformula L n p → P n p)
  · definability
  · intro k R v hR _ n h
    have : L.IsRel k R ∧ IsSemitermVec L k n v := by simpa using h
    exact hrel _ _ _ _ hR this.2
  · intro k R v hR _ n h
    have : L.IsRel k R ∧ IsSemitermVec L k n v := by simpa using h
    exact hnrel _ _ _ _ hR this.2
  · intro n _; apply hverum
  · intro n _; apply hfalsum
  · intro p q _ _ ihp ihq n h
    have : IsSemiformula L n p ∧ IsSemiformula L n q := by simpa using h
    apply hand _ _ _ this.1 this.2 (ihp n this.1) (ihq n this.2)
  · intro p q _ _ ihp ihq n h
    have : IsSemiformula L n p ∧ IsSemiformula L n q := by simpa using h
    apply hor _ _ _ this.1 this.2 (ihp n this.1) (ihq n this.2)
  · intro p _ ihp n h
    have : IsSemiformula L (n + 1) p := by simpa using h
    apply hall _ _ this (ihp _ this)
  · intro p _ ihp n h
    have : IsSemiformula L (n + 1) p := by simpa using h
    apply hex _ _ this (ihp _ this)

lemma IsSemiformula.induction1 (Γ) {P : V → V → Prop} (hP : Γ-[1]-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^rel k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → IsSemitermVec L k n v → P n (^nrel k r v))
    (hverum : ∀ n, P n ^⊤)
    (hfalsum : ∀ n, P n ^⊥)
    (hand : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, IsSemiformula L n p → IsSemiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, IsSemiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) {n p} :
    IsSemiformula L n p → P n p :=
  match Γ with
  | 𝚺 => IsSemiformula.sigma1_structural_induction hP hrel hnrel hverum hfalsum hand hor hall hex
  | 𝚷 => IsSemiformula.pi1_structural_induction hP hrel hnrel hverum hfalsum hand hor hall hex
  | 𝚫 => IsSemiformula.sigma1_structural_induction hP.of_delta hrel hnrel hverum hfalsum hand hor hall hex


lemma IsSemiformula.pos {n p : V} (h : IsSemiformula L n p) : 0 < p := h.isUFormula.pos

@[simp] lemma IsSemiformula.not_zero (m : V) : ¬IsSemiformula L m (0 : V) := by intro h; simpa using h.pos

end isSemiformula

namespace UformulaRec1.Construction

variable {β : Blueprint} {c : Construction V β} {param : V}

lemma semiformula_result_induction {P : V → V → V → V → Prop} (hP : 𝚺₁-Relation₄ P)
    (hRel : ∀ n param k R v, L.IsRel k R → IsSemitermVec L k n v → P param n (^rel k R v) (c.rel param k R v))
    (hNRel : ∀ n param k R v, L.IsRel k R → IsSemitermVec L k n v → P param n (^nrel k R v) (c.nrel param k R v))
    (hverum : ∀ n param, P param n ^⊤ (c.verum param))
    (hfalsum : ∀ n param, P param n ^⊥ (c.falsum param))
    (hand : ∀ n param p q, IsSemiformula L n p → IsSemiformula L n q →
      P param n p (c.result L param p) → P param n q (c.result L param q) → P param n (p ^⋏ q) (c.and param p q (c.result L param p) (c.result L param q)))
    (hor : ∀ n param p q, IsSemiformula L n p → IsSemiformula L n q →
      P param n p (c.result L param p) → P param n q (c.result L param q) → P param n (p ^⋎ q) (c.or param p q (c.result L param p) (c.result L param q)))
    (hall : ∀ n param p, IsSemiformula L (n + 1) p →
      P (c.allChanges param) (n + 1) p (c.result L (c.allChanges param) p) →
      P param n (^∀ p) (c.all param p (c.result L (c.allChanges param) p)))
    (hex : ∀ n param p, IsSemiformula L (n + 1) p →
      P (c.exChanges param) (n + 1) p (c.result L (c.exChanges param) p) →
      P param n (^∃ p) (c.ex param p (c.result L (c.exChanges param) p))) :
    ∀ {param n p : V}, IsSemiformula L n p → P param n p (c.result L param p) := by
  haveI : 𝚺₁-Function₂ c.result L := c.result_definable
  haveI : 𝚺₁-Function₁ c.allChanges := c.allChanges_defined.to_definable
  haveI : 𝚺₁-Function₁ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V → V := fun _ param _ ↦ Max.max param (Max.max (c.allChanges param) (c.exChanges param))
  have hf : 𝚺₁-Function₃ f := by definability
  let g : V → V → V → V := fun _ _ n ↦ n + 1
  have hg : 𝚺₁-Function₃ g := by definability
  intro param n p
  apply bounded_all_sigma1_order_induction₂ hf hg ?_ ?_ p param n
  · apply HierarchySymbol.Boldface.imp
    · apply HierarchySymbol.Boldface.comp₂ (HierarchySymbol.BoldfaceFunction.var _) (HierarchySymbol.BoldfaceFunction.var _)
    · apply HierarchySymbol.Boldface.comp₄
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
      apply HierarchySymbol.BoldfaceFunction.comp₂ (HierarchySymbol.BoldfaceFunction.var _) (HierarchySymbol.BoldfaceFunction.var _)
  intro p param n ih hp
  rcases IsSemiformula.case_iff.mp hp with
    (⟨k, R, v, hR, hv, rfl⟩ | ⟨k, R, v, hR, hv, rfl⟩ | rfl | rfl | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, p₂, h₁, h₂, rfl⟩ | ⟨p₁, h₁, rfl⟩ | ⟨p₁, h₁, rfl⟩)
  · simpa [hR, hv.isUTerm] using hRel n param k R v hR hv
  · simpa [hR, hv.isUTerm] using hNRel n param k R v hR hv
  · simpa using hverum n param
  · simpa using hfalsum n param
  · simpa [h₁.isUFormula, h₂.isUFormula] using
      hand n param p₁ p₂ h₁ h₂
        (ih p₁ (by simp) param (by simp [f]) n (by simp [g]) h₁)
        (ih p₂ (by simp) param (by simp [f]) n (by simp [g]) h₂)
  · simpa [h₁.isUFormula, h₂.isUFormula] using
      hor n param p₁ p₂ h₁ h₂
        (ih p₁ (by simp) param (by simp [f]) n (by simp [g]) h₁)
        (ih p₂ (by simp) param (by simp [f]) n (by simp [g]) h₂)
  · simpa [h₁.isUFormula] using
      hall n param p₁ h₁
        (ih p₁ (by simp) (c.allChanges param) (by simp [f]) (n + 1) (by simp [g]) h₁)
  · simpa [h₁.isUFormula] using
      hex n param p₁ h₁
        (ih p₁ (by simp) (c.exChanges param) (by simp [f]) (n + 1) (by simp [g]) h₁)

end UformulaRec1.Construction

end LO.ISigma1.Metamath
