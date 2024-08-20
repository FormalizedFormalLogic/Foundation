import Arithmetization.ISigmaOne.Metamath.Term.Basic

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

def qqRel (k r v : V) : V := ⟪0, k, r, v⟫ + 1

def qqNRel (k r v : V) : V := ⟪1, k, r, v⟫ + 1

def qqVerum : V := ⟪2, 0⟫ + 1

def qqFalsum : V := ⟪3, 0⟫ + 1

def qqAnd (p q : V) : V := ⟪4, p, q⟫ + 1

def qqOr (p q : V) : V := ⟪5, p, q⟫ + 1

def qqAll (p : V) : V := ⟪6, p⟫ + 1

def qqEx (p : V) : V := ⟪7, p⟫ + 1

scoped prefix:max "^rel " => qqRel

scoped prefix:max "^nrel " => qqNRel

scoped notation "^⊤" => qqVerum

scoped notation "^⊥" => qqFalsum

scoped notation p:69 " ^⋏ " q:70 => qqAnd p q

scoped notation p:68 " ^⋎ " q:69 => qqOr p q

scoped notation "^∀ " p:64 => qqAll p

scoped notation "^∃ " p:64 => qqEx p

section

def _root_.LO.FirstOrder.Arith.qqRelDef : 𝚺₀.Semisentence 4 :=
  .mkSigma “p k r v | ∃ p' < p, !pair₄Def p' 0 k r v ∧ p = p' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqNRelDef : 𝚺₀.Semisentence 4 :=
  .mkSigma “p k r v | ∃ p' < p, !pair₄Def p' 1 k r v ∧ p = p' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqVerumDef : 𝚺₀.Semisentence 1 :=
  .mkSigma “p | ∃ p' < p, !pairDef p' 2 0 ∧ p = p' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqFalsumDef : 𝚺₀.Semisentence 1 :=
  .mkSigma “p | ∃ p' < p, !pairDef p' 3 0 ∧ p = p' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqAndDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “r p q | ∃ r' < r, !pair₃Def r' 4 p q ∧ r = r' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqOrDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “r p q | ∃ r' < r, !pair₃Def r' 5 p q ∧ r = r' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqAllDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “r p | ∃ r' < r, !pairDef r' 6 p ∧ r = r' + 1” (by simp)

def _root_.LO.FirstOrder.Arith.qqExDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “r p | ∃ r' < r, !pairDef r' 7 p ∧ r = r' + 1” (by simp)

lemma qqRel_defined : 𝚺₀-Function₃ (qqRel : V → V → V → V) via qqRelDef := by
  intro v; simp [qqRelDef]
  constructor
  · intro h; exact ⟨_, by simp [h, qqRel], rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqNRel_defined : 𝚺₀-Function₃ (qqNRel : V → V → V → V) via qqNRelDef := by
  intro v; simp [qqNRelDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqVerum_defined : 𝚺₀-Function₀ (qqVerum : V) via qqVerumDef := by
  intro v; simp [qqVerumDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqFalsum_defined : 𝚺₀-Function₀ (qqFalsum : V) via qqFalsumDef := by
  intro v; simp [qqFalsumDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqAnd_defined : 𝚺₀-Function₂ (qqAnd : V → V → V) via qqAndDef := by
  intro v; simp [qqAndDef]
  constructor
  · intro h; exact ⟨_, by simpa [h, qqRel] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqOr_defined : 𝚺₀-Function₂ (qqOr : V → V → V) via qqOrDef := by
  intro v; simp [qqOrDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqForall_defined : 𝚺₀-Function₁ (qqAll : V → V) via qqAllDef := by
  intro v; simp [qqAllDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

lemma qqExists_defined : 𝚺₀-Function₁ (qqEx : V → V) via qqExDef := by
  intro v; simp [qqExDef, numeral_eq_natCast]
  constructor
  · intro h; exact ⟨_, by simpa [h] using lt_add_one _, rfl, h⟩
  · rintro ⟨_, _, rfl, h⟩; exact h

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

@[simp] lemma lt_and_left (p q : V) : p < p ^⋏ q := le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma lt_and_right (p q : V) : q < p ^⋏ q := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_or_left (p q : V) : p < p ^⋎ q := le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma lt_or_right (p q : V) : q < p ^⋎ q := le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_forall (p : V) : p < ^∀ p := le_iff_lt_succ.mp <| le_pair_right _ _

@[simp] lemma lt_exists (p : V) : p < ^∃ p := le_iff_lt_succ.mp <| le_pair_right _ _

namespace FormalizedFormula

variable (L)

def Phi (C : Set V) (p : V) : Prop :=
  (∃ k R v, L.Rel k R ∧ L.IsUTermVec k v ∧ p = ^rel k R v) ∨
  (∃ k R v, L.Rel k R ∧ L.IsUTermVec k v ∧ p = ^nrel k R v) ∨
  (p = ^⊤) ∨
  (p = ^⊥) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋏ p₂) ∨
  (∃ p₁ p₂, p₁ ∈ C ∧ p₂ ∈ C ∧ p = p₁ ^⋎ p₂) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∀ p₁) ∨
  (∃ p₁, p₁ ∈ C ∧ p = ^∃ p₁)

private lemma phi_iff (C p : V) :
    Phi L {x | x ∈ C} p ↔
    (∃ k < p, ∃ r < p, ∃ v < p, L.Rel k r ∧ L.IsUTermVec k v ∧ p = ^rel k r v) ∨
    (∃ k < p, ∃ r < p, ∃ v < p, L.Rel k r ∧ L.IsUTermVec k v ∧ p = ^nrel k r v) ∨
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
  “p C |
    !qqVerumDef p ∨
    !qqFalsumDef p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqAllDef p p₁) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqExDef p p₁)”
  (by simp)

def blueprint (pL : LDef) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma
    “p C |
      (∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.isUTermVecDef.sigma k v ∧ !qqRelDef p k r v) ∨
      (∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.isUTermVecDef.sigma k v ∧ !qqNRelDef p k r v) ∨
      !formulaAux p C” (by simp))
  (.mkPi
    “p C |
      (∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.isUTermVecDef.pi k v ∧ !qqRelDef p k r v) ∨
      (∃ k < p, ∃ r < p, ∃ v < p, !pL.rel k r ∧ !pL.isUTermVecDef.pi k v ∧ !qqNRelDef p k r v) ∨
      !formulaAux p C” (by simp))⟩

def construction : Fixpoint.Construction V (blueprint pL) where
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
          HierarchySymbol.Semiformula.val_mkPi, L.isUTermVec_defined.proper.iff']
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
          Language.Defined.eval_rel_iff (L := L), L.isUTermVec_defined.df.iff,
          Matrix.cons_val_three, Fin.succ_one_eq_two, eval_qqRelDef, LogicalConnective.Prop.and_eq,
          eval_qqNRelDef, eval_qqVerumDef, eval_qqFalsumDef, Semiformula.eval_operator₂,
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

section formula

open FormalizedFormula

variable (L)

def Language.IsUFormula : V → Prop := (construction L).Fixpoint ![]

section

def _root_.LO.FirstOrder.Arith.LDef.isUFormulaDef (pL : LDef) : 𝚫₁.Semisentence 1 :=
  (blueprint pL).fixpointDefΔ₁

lemma Language.isUFormula_defined : 𝚫₁-Predicate L.IsUFormula via pL.isUFormulaDef := (construction L).fixpoint_definedΔ₁

instance Language.isUFormulaDef_definable : 𝚫₁-Predicate L.IsUFormula := L.isUFormula_defined.to_definable

instance Language.isUFormulaDef_definable' : Γ-[m + 1]-Predicate L.IsUFormula := L.isUFormulaDef_definable.of_deltaOne

end

variable {L}

lemma Language.IsUFormula.case_iff {p : V} :
    L.IsUFormula p ↔
    (∃ k R v, L.Rel k R ∧ L.IsUTermVec k v ∧ p = ^rel k R v) ∨
    (∃ k R v, L.Rel k R ∧ L.IsUTermVec k v ∧ p = ^nrel k R v) ∨
    (p = ^⊤) ∨
    (p = ^⊥) ∨
    (∃ p₁ p₂, L.IsUFormula p₁ ∧ L.IsUFormula p₂ ∧ p = p₁ ^⋏ p₂) ∨
    (∃ p₁ p₂, L.IsUFormula p₁ ∧ L.IsUFormula p₂ ∧ p = p₁ ^⋎ p₂) ∨
    (∃ p₁, L.IsUFormula p₁ ∧ p = ^∀ p₁) ∨
    (∃ p₁, L.IsUFormula p₁ ∧ p = ^∃ p₁) :=
  (construction L).case

alias ⟨Language.IsUFormula.case, Language.IsUFormula.mk⟩ := Language.IsUFormula.case_iff

@[simp] lemma Language.IsUFormula.rel {k r v : V} :
    L.IsUFormula (^rel k r v) ↔ L.Rel k r ∧ L.IsUTermVec k v :=
  ⟨by intro h
      rcases h.case with (⟨k, r, v, hkr, hv, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact Language.IsUFormula.mk (Or.inl ⟨k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.nrel {k r v : V} :
    L.IsUFormula (^nrel k r v) ↔ L.Rel k r ∧ L.IsUTermVec k v :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨k, r, v, hkr, hv, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inl ⟨k, r, v, hkr, hv, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.verum : L.IsUFormula ^⊤ :=
  Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inl rfl)

@[simp] lemma Language.IsUFormula.falsum : L.IsUFormula ^⊥ :=
  Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)

@[simp] lemma Language.IsUFormula.and {p q : V} :
    L.IsUFormula (p ^⋏ q) ↔ L.IsUFormula p ∧ L.IsUFormula q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, hp, hq, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p, q, hp, hq, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.or {p q : V} :
    L.IsUFormula (p ^⋎ q) ↔ L.IsUFormula p ∧ L.IsUFormula q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, hp, hq, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p, q, hp, hq, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.all {p : V} :
    L.IsUFormula (^∀ p) ↔ L.IsUFormula p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, hp, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact hp,
   by rintro hp
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p, hp, rfl⟩)⟩

@[simp] lemma Language.IsUFormula.ex {p : V} :
    L.IsUFormula (^∃ p) ↔ L.IsUFormula p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, hp, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact hp,
   by rintro hp
      exact Language.IsUFormula.mk (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p, hp, rfl⟩)⟩

lemma Language.IsUFormula.pos {p : V} (h : L.IsUFormula p) : 0 < p := by
  rcases h.case with (⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;>
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqEx]

--lemma Language.Semiformula.pos {n p : V} (h : L.Semiformula n p) : 0 < p := h.1.pos

@[simp] lemma Language.IsUFormula.not_zero : ¬L.IsUFormula (0 : V) := by intro h; simpa using h.pos

-- @[simp] lemma Language.Semiformula.not_zero (m : V) : ¬L.Semiformula m (0 : V) := by intro h; simpa using h.pos

/-
@[simp] lemma Language.Semiformula.rel {k r v : V} :
    L.IsUFormula (^rel k r v) ↔ L.Rel k r ∧ L.IsUTermVec k v := by simp
@[simp] lemma Language.Semiformula.nrel {n k r v : V} :
    L.Semiformula n (^nrel n k r v) ↔ L.Rel k r ∧ L.SemitermVec k n v := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.verum (n : V) : L.Semiformula n ^⊤[n] := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.falsum (n : V) : L.Semiformula n ^⊥[n] := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.and {n p q : V} :
    L.Semiformula n (p ^⋏ q) ↔ L.Semiformula n p ∧ L.Semiformula n q := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.or {n p q : V} :
    L.Semiformula n (p ^⋎ q) ↔ L.Semiformula n p ∧ L.Semiformula n q := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.all {n p : V} : L.Semiformula n (^∀ p) ↔ L.Semiformula (n + 1) p := by simp [Language.Semiformula]
@[simp] lemma Language.Semiformula.ex {n p : V} : L.Semiformula n (^∃ p) ↔ L.Semiformula (n + 1) p := by simp [Language.Semiformula]
-/

lemma Language.IsUFormula.induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hrel : ∀ k r v, L.Rel k r → L.IsUTermVec k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.Rel k r → L.IsUTermVec k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, L.IsUFormula p → L.IsUFormula q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, L.IsUFormula p → L.IsUFormula q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, L.IsUFormula p → P p → P (^∀ p))
    (hex : ∀ p, L.IsUFormula p → P p → P (^∃ p)) :
    ∀ p, L.IsUFormula p → P p :=
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

/-
lemma Language.Semiformula.induction (Γ) {P : V → V → Prop} (hP : Γ-[1]-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, L.Semiformula n p → P n p := by
  suffices ∀ p, L.IsUFormula p → ∀ n ≤ p, fstIdx p = n → P n p
  by rintro n p ⟨h, rfl⟩; exact this p h (fstIdx p) (by simp) rfl
  apply Language.IsUFormula.induction (P := fun p ↦ ∀ n ≤ p, fstIdx p = n → P n p) Γ
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

lemma Language.Semiformula.induction_sigma₁ {P : V → V → Prop} (hP : 𝚺₁-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, L.Semiformula n p → P n p :=
  Language.Semiformula.induction 𝚺 hP hrel hnrel hverum hfalsum hand hor hall hex

lemma Language.Semiformula.induction_pi1 {P : V → V → Prop} (hP : 𝚷₁-Relation P)
    (hrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.Rel k r → L.SemitermVec k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, L.Semiformula n p → L.Semiformula n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hex : ∀ n p, L.Semiformula (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, L.Semiformula n p → P n p :=
  Language.Semiformula.induction 𝚷 hP hrel hnrel hverum hfalsum hand hor hall hex
-/

end formula

namespace Language.UformulaRec1

structure Blueprint (pL : LDef) where
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

variable {pL : LDef} (β : Blueprint pL)

def blueprint (β : Blueprint pL) : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “pr C |
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !pL.isUFormulaDef.sigma p ∧
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
  ” (by simp))
  (.mkPi “pr C |
    ∃ param <⁺ pr, ∃ p <⁺ pr, ∃ y <⁺ pr, !pair₃Def pr param p y ∧ !pL.isUFormulaDef.pi p ∧
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
  ” (by simp))⟩

def graph : 𝚺₁.Semisentence 3 := .mkSigma
  “param p y | ∃ pr, !pair₃Def pr param p y ∧ !β.blueprint.fixpointDef pr” (by simp)

def result : 𝚺₁.Semisentence 3 := .mkSigma
  “y param p | (!pL.isUFormulaDef.pi p → !β.graph param p y) ∧ (¬!pL.isUFormulaDef.sigma p → y = 0)” (by simp)

end Blueprint

variable (V)

structure Construction (L : Arith.Language V) (φ : Blueprint pL) where
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

variable {β : Blueprint pL} (c : Construction V L β)

def Phi (C : Set V) (pr : V) : Prop :=
  ∃ param p y, pr = ⟪param, p, y⟫ ∧
  L.IsUFormula p ∧ (
  (∃ k r v, p = ^rel k r v ∧ y = c.rel param k r v) ∨
  (∃ k r v, p = ^nrel k r v ∧ y = c.nrel param k r v) ∨
  (p = ^⊤ ∧ y = c.verum param) ∨
  (p = ^⊥ ∧ y = c.falsum param) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ p₂ y₁ y₂, ⟪param, p₁, y₁⟫ ∈ C ∧ ⟪param, p₂, y₂⟫ ∈ C ∧ p = p₁ ^⋎ p₂ ∧ y = c.or  param p₁ p₂ y₁ y₂) ∨
  (∃ p₁ y₁, ⟪c.allChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∀ p₁ ∧ y = c.all param p₁ y₁) ∨
  (∃ p₁ y₁, ⟪c.exChanges param, p₁, y₁⟫ ∈ C ∧ p = ^∃ p₁ ∧ y = c.ex  param p₁ y₁) )

private lemma phi_iff (C pr : V) :
    c.Phi {x | x ∈ C} pr ↔
    ∃ param ≤ pr, ∃ p ≤ pr, ∃ y ≤ pr, pr = ⟪param, p, y⟫ ∧ L.IsUFormula p ∧
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

def construction : Fixpoint.Construction V (β.blueprint) where
  Φ := fun _ ↦ c.Phi
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
        L.isUFormula_defined.df.iff, LogicalConnective.HomClass.map_or, Semiformula.eval_bexLT,
        Matrix.cons_val_four, Matrix.cons_val_succ, eval_qqRelDef, Matrix.cons_app_five,
        c.rel_defined.iff, LogicalConnective.Prop.and_eq, eval_qqNRelDef, c.nrel_defined.iff,
        eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef, c.falsum_defined.iff,
        Matrix.cons_app_six, Matrix.cons_app_seven, Semiformula.eval_operator₄,
        Matrix.cons_app_eight, eval_memRel₃, eval_qqAndDef, c.and_defined.iff, eval_qqOrDef,
        c.or_defined.iff, Semiformula.eval_ex, c.allChanges_defined.iff, exists_eq_left,
        eval_qqAllDef, c.all_defined.iff, c.exChanges_defined.iff, eval_qqExDef, c.ex_defined.iff,
        LogicalConnective.Prop.or_eq, HierarchySymbol.Semiformula.pi_mkDelta,
        HierarchySymbol.Semiformula.val_mkPi, L.isUFormula_defined.proper.iff',
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
          eval_pair₃Def, L.isUFormula_defined.df.iff, LogicalConnective.HomClass.map_or,
          Semiformula.eval_bexLT, Matrix.cons_val_four, Matrix.cons_val_succ, eval_qqRelDef,
          Matrix.cons_app_five, c.rel_defined.iff, LogicalConnective.Prop.and_eq, eval_qqNRelDef,
          c.nrel_defined.iff, eval_qqVerumDef, c.verum_defined.iff, eval_qqFalsumDef,
          c.falsum_defined.iff, Matrix.cons_app_six, Matrix.cons_app_seven,
          Semiformula.eval_operator₄, Matrix.cons_app_eight, eval_memRel₃, eval_qqAndDef,
          c.and_defined.iff, eval_qqOrDef, c.or_defined.iff, Semiformula.eval_ex,
          c.allChanges_defined.iff, exists_eq_left, eval_qqAllDef, c.all_defined.iff,
          c.exChanges_defined.iff, eval_qqExDef, c.ex_defined.iff,
          LogicalConnective.Prop.or_eq] using c.phi_iff _ _⟩
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

instance : c.construction.Finite where
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

def Graph (param : V) (x y : V) : Prop := c.construction.Fixpoint ![] ⟪param, x, y⟫

variable {param : V}

variable {c}

lemma Graph.case_iff {p y : V} :
    c.Graph param p y ↔
    L.IsUFormula p ∧ (
    (∃ k R v, p = ^rel k R v ∧ y = c.rel param k R v) ∨
    (∃ k R v, p = ^nrel k R v ∧ y = c.nrel param k R v) ∨
    (p = ^⊤ ∧ y = c.verum param) ∨
    (p = ^⊥ ∧ y = c.falsum param) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph param p₁ y₁ ∧ c.Graph param p₂ y₂ ∧ p = p₁ ^⋏ p₂ ∧ y = c.and param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ p₂ y₁ y₂, c.Graph param p₁ y₁ ∧ c.Graph param p₂ y₂ ∧ p = p₁ ^⋎ p₂ ∧ y = c.or param p₁ p₂ y₁ y₂) ∨
    (∃ p₁ y₁, c.Graph (c.allChanges param) p₁ y₁ ∧ p = ^∀ p₁ ∧ y = c.all param p₁ y₁) ∨
    (∃ p₁ y₁, c.Graph (c.exChanges param) p₁ y₁ ∧ p = ^∃ p₁ ∧ y = c.ex param p₁ y₁) ) :=
  Iff.trans c.construction.case (by
    constructor
    · rintro ⟨param, p, y, e, H⟩;
      simp at e; rcases e with ⟨rfl, rfl, rfl⟩
      refine H
    · intro H; exact ⟨_, _, _, rfl, H⟩)

variable (c β)

lemma graph_defined : 𝚺₁-Relation₃ c.Graph via β.graph := by
  intro v; simp [Blueprint.graph, c.construction.fixpoint_defined.iff, Matrix.empty_eq]; rfl

@[simp] lemma eval_graphDef (v) :
    Semiformula.Evalbm V v β.graph.val ↔ c.Graph (v 0) (v 1) (v 2) := (graph_defined β c).df.iff v

instance graph_definable : 𝚺-[0 + 1]-Relation₃ c.Graph := (c.graph_defined).to_definable

variable {β}

lemma graph_dom_uformula {p r} :
    c.Graph param p r → L.IsUFormula p := fun h ↦ Graph.case_iff.mp h |>.1

lemma graph_rel_iff {k r v y} (hkr : L.Rel k r) (hv : L.IsUTermVec k v) :
    c.Graph param (^rel k r v) y ↔ y = c.rel param k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨k, r, v, H, rfl⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqRel] at H; rcases H with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · simp [qqRel, qqNRel] at H
    · simp [qqRel, qqVerum] at H
    · simp [qqRel, qqFalsum] at H
    · simp [qqRel, qqAnd] at H
    · simp [qqRel, qqOr] at H
    · simp [qqRel, qqAll] at H
    · simp [qqRel, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_nrel_iff {k r v y} (hkr : L.Rel k r) (hv : L.IsUTermVec k v) :
    c.Graph param (^nrel k r v) y ↔ y = c.nrel param k r v := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqNRel, qqRel] at H
    · simp [qqNRel] at H; rcases H with ⟨rfl, rfl, rfl, rfl⟩; rfl
    · simp [qqNRel, qqVerum] at H
    · simp [qqNRel, qqFalsum] at H
    · simp [qqNRel, qqAnd] at H
    · simp [qqNRel, qqOr] at H
    · simp [qqNRel, qqAll] at H
    · simp [qqNRel, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_verum_iff {y} :
    c.Graph param ^⊤ y ↔ y = c.verum param := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, rfl⟩ | ⟨H, _⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqVerum, qqRel] at H
    · simp [qqVerum, qqNRel] at H
    · simp [qqVerum, qqVerum] at H; rcases H; rfl
    · simp [qqVerum, qqFalsum] at H
    · simp [qqVerum, qqAnd] at H
    · simp [qqVerum, qqOr] at H
    · simp [qqVerum, qqAll] at H
    · simp [qqVerum, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_falsum_iff {y} :
    c.Graph param ^⊥ y ↔ y = c.falsum param := by
  constructor
  · intro h
    rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, rfl⟩ |
      ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
    · simp [qqFalsum, qqRel] at H
    · simp [qqFalsum, qqNRel] at H
    · simp [qqFalsum, qqVerum] at H
    · simp [qqFalsum, qqFalsum] at H; rcases H; rfl
    · simp [qqFalsum, qqAnd] at H
    · simp [qqFalsum, qqOr] at H
    · simp [qqFalsum, qqAll] at H
    · simp [qqFalsum, qqEx] at H
  · rintro rfl; exact (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_rel {k r v} (hkr : L.Rel k r) (hv : L.IsUTermVec k v) :
    c.Graph param (^rel k r v) (c.rel param k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_nrel {k r v} (hkr : L.Rel k r) (hv : L.IsUTermVec k v) :
    c.Graph param (^nrel k r v) (c.nrel param k r v) :=
  (Graph.case_iff).mpr ⟨by simp [hkr, hv], Or.inr <| Or.inl ⟨k, r, v, rfl, rfl⟩⟩

lemma graph_verum :
    c.Graph param ^⊤ (c.verum param) := (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_falsum :
    c.Graph param ^⊥ (c.falsum param) := (Graph.case_iff).mpr ⟨by simp, Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩⟩

lemma graph_and {p₁ p₂ r₁ r₂ : V} (hp₁ : L.IsUFormula p₁) (hp₂ : L.IsUFormula p₂)
    (h₁ : c.Graph param p₁ r₁) (h₂ : c.Graph param p₂ r₂) :
    c.Graph param (p₁ ^⋏ p₂) (c.and param p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_and_inv {p₁ p₂ r : V} :
    c.Graph param (p₁ ^⋏ p₂) r → ∃ r₁ r₂, c.Graph param p₁ r₁ ∧ c.Graph param p₂ r₂ ∧ r = c.and param p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqAnd, qqRel] at H
  · simp [qqAnd, qqNRel] at H
  · simp [qqAnd, qqVerum] at H
  · simp [qqAnd, qqFalsum] at H
  · simp [qqAnd, qqAnd] at H; rcases H with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqAnd, qqOr] at H
  · simp [qqAnd, qqAll] at H
  · simp [qqAnd, qqEx] at H

lemma graph_or {p₁ p₂ r₁ r₂ : V} (hp₁ : L.IsUFormula p₁) (hp₂ : L.IsUFormula p₂)
    (h₁ : c.Graph param p₁ r₁) (h₂ : c.Graph param p₂ r₂) :
    c.Graph param (p₁ ^⋎ p₂) (c.or param p₁ p₂ r₁ r₂) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁, hp₂], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, p₂, r₁, r₂, h₁, h₂, rfl, rfl⟩⟩

lemma graph_or_inv {p₁ p₂ r : V} :
    c.Graph param (p₁ ^⋎ p₂) r → ∃ r₁ r₂, c.Graph param p₁ r₁ ∧ c.Graph param p₂ r₂ ∧ r = c.or param p₁ p₂ r₁ r₂ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, rfl⟩ | ⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqOr, qqRel] at H
  · simp [qqOr, qqNRel] at H
  · simp [qqOr, qqVerum] at H
  · simp [qqOr, qqFalsum] at H
  · simp [qqOr, qqAnd] at H
  · simp [qqOr, qqOr] at H; rcases H with ⟨rfl, rfl, rfl⟩
    exact ⟨_, _, by assumption, by assumption, rfl⟩
  · simp [qqOr, qqAll] at H
  · simp [qqOr, qqEx] at H

lemma graph_all {p₁ r₁ : V} (hp₁ : L.IsUFormula p₁) (h₁ : c.Graph (c.allChanges param) p₁ r₁) :
    c.Graph param (^∀ p₁) (c.all param p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_all_inv {p₁ r : V} :
    c.Graph param (^∀ p₁) r → ∃ r₁, c.Graph (c.allChanges param) p₁ r₁ ∧ r = c.all param p₁ r₁ := by
  intro h
  rcases Graph.case_iff.mp h with ⟨_, (⟨_, _, _, H, _⟩ | ⟨_, _, _, H, _⟩ | ⟨H, _⟩ | ⟨H, _⟩ |
    ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, _, _, _, H, _⟩ | ⟨_, _, _, H, rfl⟩ | ⟨_, _, _, H, _⟩)⟩
  · simp [qqAll, qqRel] at H
  · simp [qqAll, qqNRel] at H
  · simp [qqAll, qqVerum] at H
  · simp [qqAll, qqFalsum] at H
  · simp [qqAll, qqAnd] at H
  · simp [qqAll, qqOr] at H
  · simp [qqAll, qqAll] at H; rcases H with ⟨rfl, rfl⟩
    exact ⟨_, by assumption, rfl⟩
  · simp [qqAll, qqEx] at H

lemma graph_ex {p₁ r₁ : V} (hp₁ : L.IsUFormula p₁) (h₁ : c.Graph (c.exChanges param) p₁ r₁) :
    c.Graph param (^∃ p₁) (c.ex param p₁ r₁) :=
  (Graph.case_iff).mpr ⟨by simp [hp₁], Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨p₁, r₁, h₁, rfl, rfl⟩⟩

lemma graph_ex_inv {p₁ r : V} :
    c.Graph param (^∃ p₁) r → ∃ r₁, c.Graph (c.exChanges param) p₁ r₁ ∧ r = c.ex param p₁ r₁ := by
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
  · simp [qqEx, qqEx] at H; rcases H with ⟨rfl, rfl⟩
    exact ⟨_, by assumption, rfl⟩

variable (param)

lemma graph_exists {p : V} : L.IsUFormula p → ∃ y, c.Graph param p y := by
  haveI : 𝚺₁-Function₁ c.allChanges := c.allChanges_defined.to_definable
  haveI : 𝚺₁-Function₁ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V := fun _ param ↦ Max.max param (Max.max (c.allChanges param) (c.exChanges param))
  have hf : 𝚺₁-Function₂ f := by simp [f]; definability
  apply sigma₁_order_ball_induction hf ?_ ?_ p param
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

lemma graph_unique {p : V} : L.IsUFormula p → ∀ {param r r'}, c.Graph param p r → c.Graph param p r' → r = r' := by
  apply Language.IsUFormula.induction 𝚷 (P := fun p ↦ ∀ {param r r'}, c.Graph param p r → c.Graph param p r' → r = r')
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

lemma exists_unique {p : V} (hp : L.IsUFormula p) : ∃! r, c.Graph param p r := by
  rcases c.graph_exists param hp with ⟨r, hr⟩
  exact ExistsUnique.intro r hr (fun r' hr' ↦ c.graph_unique hp hr' hr)

lemma exists_unique_all (p : V) : ∃! r, (L.IsUFormula p → c.Graph param p r) ∧ (¬L.IsUFormula p → r = 0) := by
  by_cases hp : L.IsUFormula p <;> simp [hp, exists_unique]

def result (p : V) : V := Classical.choose! (c.exists_unique_all param p)

lemma result_prop {p : V} (hp : L.IsUFormula p) : c.Graph param p (c.result param p) :=
  Classical.choose!_spec (c.exists_unique_all param p) |>.1 hp

lemma result_prop_not {p : V} (hp : ¬L.IsUFormula p) : c.result param p = 0 :=
  Classical.choose!_spec (c.exists_unique_all param p) |>.2 hp

variable {param}

lemma result_eq_of_graph {p r} (h : c.Graph param p r) : c.result param p = r := Eq.symm <|
  Classical.choose_uniq (c.exists_unique_all param p) (by simp [c.graph_dom_uformula h, h])

@[simp] lemma result_rel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    c.result param (^rel k R v) = c.rel param k R v :=
  c.result_eq_of_graph (c.graph_rel hR hv)

@[simp] lemma result_nrel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    c.result param (^nrel k R v) = c.nrel param k R v :=
  c.result_eq_of_graph (c.graph_nrel hR hv)

@[simp] lemma result_verum : c.result param ^⊤ = c.verum param := c.result_eq_of_graph c.graph_verum

@[simp] lemma result_falsum : c.result param ^⊥ = c.falsum param := c.result_eq_of_graph c.graph_falsum

@[simp] lemma result_and {p q}
    (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    c.result param (p ^⋏ q) = c.and param p q (c.result param p) (c.result param q) :=
  c.result_eq_of_graph (c.graph_and hp hq (c.result_prop param hp) (c.result_prop param hq))

@[simp] lemma result_or {p q}
    (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    c.result param (p ^⋎ q) = c.or param p q (c.result param p) (c.result param q) :=
  c.result_eq_of_graph (c.graph_or hp hq (c.result_prop param hp) (c.result_prop param hq))

@[simp] lemma result_all {p} (hp : L.IsUFormula p) :
    c.result param (^∀ p) = c.all param p (c.result (c.allChanges param) p) :=
  c.result_eq_of_graph (c.graph_all hp (c.result_prop (c.allChanges param) hp))

@[simp] lemma result_ex {p} (hp : L.IsUFormula p) :
    c.result param (^∃ p) = c.ex param p (c.result (c.exChanges param) p) :=
  c.result_eq_of_graph (c.graph_ex hp (c.result_prop _ hp))

section

lemma result_defined : 𝚺₁-Function₂ c.result via β.result := by
  intro v
  simp [Blueprint.result, HierarchySymbol.Semiformula.val_sigma, L.isUFormula_defined.df.iff, L.isUFormula_defined.proper.iff', c.eval_graphDef]
  exact Classical.choose!_eq_iff (c.exists_unique_all (v 1) (v 2))

instance result_definable : 𝚺-[0 + 1]-Function₂ c.result := c.result_defined.to_definable

end

lemma uformula_result_induction {P : V → V → V → Prop} (hP : 𝚺₁-Relation₃ P)
    (hRel : ∀ param k R v, L.Rel k R → L.IsUTermVec k v → P param (^rel k R v) (c.rel param k R v))
    (hNRel : ∀ param k R v, L.Rel k R → L.IsUTermVec k v → P param (^nrel k R v) (c.nrel param k R v))
    (hverum : ∀ param, P param ^⊤ (c.verum param))
    (hfalsum : ∀ param, P param ^⊥ (c.falsum param))
    (hand : ∀ param p q, L.IsUFormula p → L.IsUFormula q →
      P param p (c.result param p) → P param q (c.result param q) → P param (p ^⋏ q) (c.and param p q (c.result param p) (c.result param q)))
    (hor : ∀ param p q, L.IsUFormula p → L.IsUFormula q →
      P param p (c.result param p) → P param q (c.result param q) → P param (p ^⋎ q) (c.or param p q (c.result param p) (c.result param q)))
    (hall : ∀ param p, L.IsUFormula p →
      P (c.allChanges param) p (c.result (c.allChanges param) p) →
      P param (^∀ p) (c.all param p (c.result (c.allChanges param) p)))
    (hex : ∀ param p, L.IsUFormula p →
      P (c.exChanges param) p (c.result (c.exChanges param) p) →
      P param (^∃ p) (c.ex param p (c.result (c.exChanges param) p))) :
    ∀ {param p : V}, L.IsUFormula p → P param p (c.result param p) := by
  haveI : 𝚺₁-Function₂ c.result := c.result_definable
  intro param p
  haveI : 𝚺₁-Function₁ c.allChanges := c.allChanges_defined.to_definable
  haveI : 𝚺₁-Function₁ c.exChanges := c.exChanges_defined.to_definable
  let f : V → V → V := fun _ param ↦ Max.max param (Max.max (c.allChanges param) (c.exChanges param))
  have hf : 𝚺₁-Function₂ f := by simp [f]; definability
  apply sigma₁_order_ball_induction hf ?_ ?_ p param
  · apply HierarchySymbol.Boldface.imp
      (HierarchySymbol.Boldface.comp₁ (HierarchySymbol.BoldfaceFunction.var _))
      (HierarchySymbol.Boldface.comp₃
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.var _)
        (HierarchySymbol.BoldfaceFunction.comp₂ (HierarchySymbol.BoldfaceFunction.var _) (HierarchySymbol.BoldfaceFunction.var _)))
  intro p param ih hp
  rcases hp.case with
    (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ |
    rfl | rfl | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, p₂, hp₁, hp₂, rfl⟩ | ⟨p₁, hp₁, rfl⟩ | ⟨p₁, hp₁, rfl⟩)
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
    (hRel : ∀ param k R v, L.Rel k R → L.SemitermVec k n v → P param (^rel n k R v) (c.rel param k R v))
    (hNRel : ∀ param k R v, L.Rel k R → L.SemitermVec k n v → P param (^nrel n k R v) (c.nrel param k R v))
    (hverum : ∀ param, P param (^⊤[n]) (c.verum param))
    (hfalsum : ∀ param, P param (^⊥[n]) (c.falsum param))
    (hand : ∀ param p q, L.Semiformula n p → L.Semiformula n q →
      P param p (c.result param p) → P param q (c.result param q) → P param (p ^⋏ q) (c.and param p q (c.result param p) (c.result param q)))
    (hor : ∀ param p q, L.Semiformula n p → L.Semiformula n q →
      P param p (c.result param p) → P param q (c.result param q) → P param (p ^⋎ q) (c.or param p q (c.result param p) (c.result param q)))
    (hall : ∀ param p, L.Semiformula (n + 1) p →
      P (c.allChanges param) (n + 1) p (c.result (c.allChanges param) p) →
      P param (^∀ p) (c.all param p (c.result (c.allChanges param) p)))
    (hex : ∀ param p, L.Semiformula (n + 1) p →
      P (c.exChanges param) (n + 1) p (c.result (c.exChanges param) p) →
      P param (^∃ p) (c.ex param p (c.result (c.exChanges param) p))) :
    ∀ {param p : V}, L.Semiformula n p → P param p (c.result param p) := by
  suffices ∀ {param p : V}, L.IsUFormula p → ∀ n ≤ p, n = fstIdx p → P param p (c.result param p)
  by intro param p hp; exact @this param p hp.1 n (by simp [hp.2]) hp.2
  intro param p hp
  apply c.uformula_result_induction (P := fun param p y ↦ ∀ n ≤ p, n = fstIdx p → P param p y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · apply HierarchySymbol.Boldface.ball_le (HierarchySymbol.BoldfaceFunction.var _)
    simp_all only [zero_add, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.succ_one_eq_two,
      Fin.succ_zero_eq_one]
    apply LO.FirstOrder.Arith.HierarchySymbol.Boldface.imp
    · simp_all only [SigmaPiDelta.alt_sigma, Fin.isValue]
      apply LO.FirstOrder.Arith.HierarchySymbol.Boldface.comp₂
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue]
        apply LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction.comp₁
        simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
    · apply LO.FirstOrder.Arith.HierarchySymbol.Boldface.comp₄
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue]
        apply LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction.comp₁
        simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
      · simp_all only [zero_add, Fin.isValue, HierarchySymbol.BoldfaceFunction.var]
  · rintro param k R v hkR hv _ _ rfl; simpa using hRel param k R v hkR hv
  · rintro param k R v hkR hv _ _ rfl; simpa using hNRel param k R v hkR hv
  · rintro param _ _ rfl; simpa using hverum param
  · rintro param _ _ rfl; simpa using hfalsum param
  · rintro param p q hp hq ihp ihq _ _ rfl
    have ihp : P param p (c.result param p) := ihp n (by simp [hp.2]) hp.2
    have ihq : P param q (c.result param q) := ihq n (by simp [hq.2]) hq.2
    simpa using hand param p q hp hq ihp ihq
  · rintro param p q hp hq ihp ihq _ _ rfl
    have ihp : P param p (c.result param p) := ihp n (by simp [hp.2]) hp.2
    have ihq : P param q (c.result param q) := ihq n (by simp [hq.2]) hq.2
    simpa using hor param p q hp hq ihp ihq
  · rintro param p hp ihp _ _ rfl
    have ihp : P (c.allChanges param) (n + 1) p (c.result (c.allChanges param) p) := ihp (n + 1) (by simp [hp.2]) hp.2
    simpa using hall param p hp ihp
  · rintro param p hp ihp _ _ rfl
    have ihp : P (c.exChanges param) (n + 1) p (c.result (c.exChanges param) p) := ihp (n + 1) (by simp [hp.2]) hp.2
    simpa using hex param p hp ihp
-/

end Construction

end Language.UformulaRec1

section bv

namespace BV

def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel := .mkSigma “y param k R v | ∃ M, !pL.termBVVecDef M k v ∧ !listMaxDef y M” (by simp)
  nrel := .mkSigma “y param k R v | ∃ M, !pL.termBVVecDef M k v ∧ !listMaxDef y M” (by simp)
  verum := .mkSigma “y param | y = 0” (by simp)
  falsum := .mkSigma “y param | y = 0” (by simp)
  and := .mkSigma “y param p₁ p₂ y₁ y₂ | !max y y₁ y₂” (by simp)
  or := .mkSigma “y param p₁ p₂ y₁ y₂ | !max y y₁ y₂” (by simp)
  all := .mkSigma “y param p₁ y₁ | !subDef y y₁ 1” (by simp)
  ex := .mkSigma “y param p₁ y₁ | !subDef y y₁ 1” (by simp)
  allChanges := .mkSigma “param' param | param' = 0” (by simp)
  exChanges := .mkSigma “param' param | param' = 0” (by simp)

variable (L)

def construction : Language.UformulaRec1.Construction V L (blueprint pL) where
  rel {_} := fun k _ v ↦ listMax (L.termBVVec k v)
  nrel {_} := fun k _ v ↦ listMax (L.termBVVec k v)
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  or {_} := fun _ _ y₁ y₂ ↦ Max.max y₁ y₂
  all {_} := fun _ y₁ ↦ y₁ - 1
  ex {_} := fun _ y₁ ↦ y₁ - 1
  allChanges := fun _ ↦ 0
  exChanges := fun _ ↦ 0
  rel_defined := by intro v; simp [blueprint, L.termBVVec_defined.df.iff]; rfl
  nrel_defined := by intro v; simp [blueprint, L.termBVVec_defined.df.iff]; rfl
  verum_defined := by intro v; simp [blueprint]
  falsum_defined := by intro v; simp [blueprint]
  and_defined := by intro v; simp [blueprint]; rfl
  or_defined := by intro v; simp [blueprint]; rfl
  all_defined := by intro v; simp [blueprint]; rfl
  ex_defined := by intro v; simp [blueprint]; rfl
  allChanges_defined := by intro v; simp [blueprint]
  exChanges_defined := by intro v; simp [blueprint]

end BV

open BV

variable (L)

def Language.bv (p : V) : V := (construction L).result 0 p

variable {L}

section

def _root_.LO.FirstOrder.Arith.LDef.bvDef (pL : LDef) : 𝚺₁.Semisentence 2 := (blueprint pL).result.rew (Rew.substs ![#0, ‘0’, #1])

variable (L)

lemma Language.bv_defined : 𝚺₁-Function₁ L.bv via pL.bvDef := fun v ↦ by
  simpa [LDef.bvDef] using (construction L).result_defined ![v 0, 0, v 1]

instance Language.bv_definable : 𝚺₁-Function₁ L.bv := L.bv_defined.to_definable

instance Language.neg_definable' (Γ) : Γ-[m + 1]-Function₁ L.bv := L.bv_definable.of_sigmaOne

end

@[simp] lemma bv_rel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.bv (^rel k R v) = listMax (L.termBVVec k v) := by simp [Language.bv, hR, hv, construction]

@[simp] lemma bv_nrel {k R v} (hR : L.Rel k R) (hv : L.IsUTermVec k v) :
    L.bv (^nrel k R v) = listMax (L.termBVVec k v) := by simp [Language.bv, hR, hv, construction]

@[simp] lemma bv_verum : L.bv ^⊤ = 0 := by simp [Language.bv, construction]

@[simp] lemma bv_falsum : L.bv ^⊥ = 0 := by simp [Language.bv, construction]

@[simp] lemma bv_and {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.bv (p ^⋏ q) = Max.max (L.bv p) (L.bv q) := by simp [Language.bv, hp, hq, construction]

@[simp] lemma bv_or {p q} (hp : L.IsUFormula p) (hq : L.IsUFormula q) :
    L.bv (p ^⋎ q) = Max.max (L.bv p) (L.bv q) := by simp [Language.bv, hp, hq, construction]

@[simp] lemma bv_all {p} (hp : L.IsUFormula p) : L.bv (^∀ p) = L.bv p - 1 := by simp [Language.bv, hp, construction]

@[simp] lemma bv_ex {p} (hp : L.IsUFormula p) : L.bv (^∃ p) = L.bv p - 1 := by simp [Language.bv, hp, construction]

lemma bv_eq_of_not_isUFormula {p} (h : ¬L.IsUFormula p) : L.bv p = 0 := (construction L).result_prop_not _ h

end bv

section isSemiformula

variable (L)

structure Language.IsSemiformula (n p : V) : Prop where
  isUFormula : L.IsUFormula p
  bv : L.bv p ≤ n

abbrev Language.IsFormula (p : V) : Prop := L.IsSemiformula 0 p

variable {L}

@[simp] lemma Language.IsSemiformula.rel {n k r v : V} :
    L.IsSemiformula n (^rel k r v) ↔ L.Rel k r ∧ L.IsSemitermVec k n v := by
  constructor
  · intro h
    have hrv : L.Rel k r ∧ L.IsUTermVec k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun i hi ↦ by
      have : listMax (L.termBVVec k v) ≤ n := by simpa [hrv] using h.bv
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_rel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma Language.IsSemiformula.nrel {n k r v : V} :
    L.IsSemiformula n (^nrel k r v) ↔ L.Rel k r ∧ L.IsSemitermVec k n v := by
  constructor
  · intro h
    have hrv : L.Rel k r ∧ L.IsUTermVec k v := by simpa using h.isUFormula
    exact ⟨hrv.1, hrv.2, fun i hi ↦ by
      have : listMax (L.termBVVec k v) ≤ n := by simpa [hrv] using h.bv
      exact le_trans (le_trans (by simp_all) (nth_le_listMax (i := i) (by simp_all))) this⟩
  · rintro ⟨hr, hv⟩
    exact ⟨by simp [hr, hv.isUTerm], by
      rw [bv_nrel hr hv.isUTerm]
      apply listMaxss_le
      intro i hi
      have := hv.bv (i := i) (by simpa [hv.isUTerm] using hi)
      rwa [nth_termBVVec hv.isUTerm (by simpa [hv.isUTerm] using hi)]⟩

@[simp] lemma Language.IsSemiformula.verum {n} : L.IsSemiformula n ^⊤ := ⟨by simp, by simp⟩

@[simp] lemma Language.IsSemiformula.falsum {n} : L.IsSemiformula n ^⊥ := ⟨by simp, by simp⟩

@[simp] lemma Language.IsSemiformula.and {n p q : V} :
    L.IsSemiformula n (p ^⋏ q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q := by
  constructor
  · intro h
    have hpq : L.IsUFormula p ∧ L.IsUFormula q := by simpa using h.isUFormula
    have hbv : L.bv p ≤ n ∧ L.bv q ≤ n := by simpa [hpq] using h.bv
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv, hq.bv]⟩

@[simp] lemma Language.IsSemiformula.or {n p q : V} :
    L.IsSemiformula n (p ^⋎ q) ↔ L.IsSemiformula n p ∧ L.IsSemiformula n q := by
  constructor
  · intro h
    have hpq : L.IsUFormula p ∧ L.IsUFormula q := by simpa using h.isUFormula
    have hbv : L.bv p ≤ n ∧ L.bv q ≤ n := by simpa [hpq] using h.bv
    exact ⟨⟨hpq.1, hbv.1⟩, ⟨hpq.2, hbv.2⟩⟩
  · rintro ⟨hp, hq⟩
    exact ⟨by simp [hp.isUFormula, hq.isUFormula], by simp [hp.isUFormula, hq.isUFormula, hp.bv, hq.bv]⟩

@[simp] lemma Language.IsSemiformula.all {n p : V} :
    L.IsSemiformula n (^∀ p) ↔ L.IsSemiformula (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show L.IsUFormula p by simpa using h.isUFormula] using h.bv⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv]⟩

@[simp] lemma Language.IsSemiformula.ex {n p : V} :
    L.IsSemiformula n (^∃ p) ↔ L.IsSemiformula (n + 1) p := by
  constructor
  · intro h
    exact ⟨by simpa using h.isUFormula, by
      simpa [show L.IsUFormula p by simpa using h.isUFormula] using h.bv⟩
  · intro h
    exact ⟨by simp [h.isUFormula], by simp [h.isUFormula, h.bv]⟩

end isSemiformula

end LO.Arith

end
