module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Basic
public import Foundation.FirstOrder.Arithmetic.Induction.Basic

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

open FFL.FirstOrder.Bounding (HierarchySymbol)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def qqRel (k r v : V) : V := ⟪0, k, r, v⟫ + 1

noncomputable def qqNRel (k r v : V) : V := ⟪1, k, r, v⟫ + 1

noncomputable def qqVerum : V := ⟪2, 0⟫ + 1

noncomputable def qqFalsum : V := ⟪3, 0⟫ + 1

noncomputable def qqAnd (p q : V) : V := ⟪4, p, q⟫ + 1

noncomputable def qqOr (p q : V) : V := ⟪5, p, q⟫ + 1

noncomputable def qqAll (p : V) : V := ⟪6, p⟫ + 1

noncomputable def qqExs (p : V) : V := ⟪7, p⟫ + 1

scoped prefix:max "^rel " => qqRel

scoped prefix:max "^nrel " => qqNRel

scoped notation "^⊤" => qqVerum

scoped notation "^⊥" => qqFalsum

scoped notation p:69 " ^⋏ " q:70 => qqAnd p q

scoped notation p:68 " ^⋎ " q:69 => qqOr p q

scoped notation "^∀ " p:64 => qqAll p

scoped notation "^∃ " p:64 => qqExs p

section

def _root_.FFL.FirstOrder.Arithmetic.qqRelDef : 𝚺ᴬ₀.Semisentence 4 :=
  .mkSigma “p k r v. ∃ p' < p, !pair₄Def p' 0 k r v ∧ p = p' + 1”

def _root_.FFL.FirstOrder.Arithmetic.qqNRelDef : 𝚺ᴬ₀.Semisentence 4 :=
  .mkSigma “p k r v. ∃ p' < p, !pair₄Def p' 1 k r v ∧ p = p' + 1”

def _root_.FFL.FirstOrder.Arithmetic.qqVerumDef : 𝚺ᴬ₀.Semisentence 1 :=
  .mkSigma “p. ∃ p' < p, !pairDef p' 2 0 ∧ p = p' + 1”

def _root_.FFL.FirstOrder.Arithmetic.qqFalsumDef : 𝚺ᴬ₀.Semisentence 1 :=
  .mkSigma “p. ∃ p' < p, !pairDef p' 3 0 ∧ p = p' + 1”

def _root_.FFL.FirstOrder.Arithmetic.qqAndDef : 𝚺ᴬ₀.Semisentence 3 :=
  .mkSigma “r p q. ∃ r' < r, !pair₃Def r' 4 p q ∧ r = r' + 1”

def _root_.FFL.FirstOrder.Arithmetic.qqOrDef : 𝚺ᴬ₀.Semisentence 3 :=
  .mkSigma “r p q. ∃ r' < r, !pair₃Def r' 5 p q ∧ r = r' + 1”

def _root_.FFL.FirstOrder.Arithmetic.qqAllDef : 𝚺ᴬ₀.Semisentence 2 :=
  .mkSigma “r p. ∃ r' < r, !pairDef r' 6 p ∧ r = r' + 1”

def _root_.FFL.FirstOrder.Arithmetic.qqExsDef : 𝚺ᴬ₀.Semisentence 2 :=
  .mkSigma “r p. ∃ r' < r, !pairDef r' 7 p ∧ r = r' + 1”

instance qqRel_defined : 𝚺ᴬ₀-Function₃ (qqRel : V → V → V → V) via qqRelDef :=
  .mk fun v ↦ by simp_all [qqRelDef, qqRel]

instance qqNRel_defined : 𝚺ᴬ₀-Function₃ (qqNRel : V → V → V → V) via qqNRelDef :=
  .mk fun v ↦ by simp_all [qqNRelDef, qqNRel]

instance qqVerum_defined : 𝚺ᴬ₀-Function₀ (qqVerum : V) via qqVerumDef :=
  .mk fun v ↦ by simp_all [qqVerumDef, qqVerum]

instance qqFalsum_defined : 𝚺ᴬ₀-Function₀ (qqFalsum : V) via qqFalsumDef :=
  .mk fun v ↦ by simp_all [qqFalsumDef, qqFalsum]

instance qqAnd_defined : 𝚺ᴬ₀-Function₂ (qqAnd : V → V → V) via qqAndDef :=
  .mk fun v ↦ by simp_all [qqAndDef, qqAnd]

instance qqOr_defined : 𝚺ᴬ₀-Function₂ (qqOr : V → V → V) via qqOrDef :=
  .mk fun v ↦ by simp_all [qqOrDef, numeral_eq_natCast, qqOr]

instance qqForall_defined : 𝚺ᴬ₀-Function₁ (qqAll : V → V) via qqAllDef :=
  .mk fun v ↦ by simp_all [qqAllDef, numeral_eq_natCast, qqAll]

instance qqExsists_defined : 𝚺ᴬ₀-Function₁ (qqExs : V → V) via qqExsDef :=
  .mk fun v ↦ by simp_all [qqExsDef, numeral_eq_natCast, qqExs]

instance (ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₃ (qqRel : V → V → V → V) :=
  .of_zero qqRel_defined.to_definable

instance (ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₃ (qqNRel : V → V → V → V) :=
  .of_zero qqNRel_defined.to_definable

instance (ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂ (qqAnd : V → V → V) :=
  .of_zero qqAnd_defined.to_definable

instance (ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₂ (qqOr : V → V → V) :=
  .of_zero qqOr_defined.to_definable

instance (ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₁ (qqAll : V → V) :=
  .of_zero qqForall_defined.to_definable

instance (ℌ : HierarchySymbol ℬ[<, ℒₒᵣ]) :
    ℌ-Function₁ (qqExs : V → V) :=
  .of_zero qqExsists_defined.to_definable

end

@[simp] lemma qqRel_inj (k₁ r₁ v₁ k₂ r₂ v₂ : V) :
    ^rel k₁ r₁ v₁ = ^rel k₂ r₂ v₂ ↔ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqRel]
@[simp] lemma qqNRel_inj (k₁ r₁ v₁ k₂ r₂ v₂ : V) :
    ^nrel k₁ r₁ v₁ = ^nrel k₂ r₂ v₂ ↔ k₁ = k₂ ∧ r₁ = r₂ ∧ v₁ = v₂ := by simp [qqNRel]
@[simp] lemma qqAnd_inj (p₁ q₁ p₂ q₂ : V) :
    p₁ ^⋏ q₁ = p₂ ^⋏ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqAnd]
@[simp] lemma qqOr_inj (p₁ q₁ p₂ q₂ : V) :
    p₁ ^⋎ q₁ = p₂ ^⋎ q₂ ↔ p₁ = p₂ ∧ q₁ = q₂ := by simp [qqOr]
@[simp] lemma qqAll_inj (p₁ p₂ : V) : ^∀ p₁ = ^∀ p₂ ↔ p₁ = p₂ := by simp [qqAll]
@[simp] lemma qqExs_inj (p₁ p₂ : V) : ^∃ p₁ = ^∃ p₂ ↔ p₁ = p₂ := by simp [qqExs]

@[simp] lemma arity_lt_rel (k r v : V) : k < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left k ⟪r, v⟫) <| le_pair_right _ _
@[simp] lemma r_lt_rel (k r v : V) : r < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _
@[simp] lemma v_lt_rel (k r v : V) : v < ^rel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
    le_pair_right _ _

@[simp] lemma arity_lt_nrel (k r v : V) : k < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma r_lt_nrel (k r v : V) : r < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_left _ _) <| le_pair_right _ _) <|
    le_pair_right _ _
@[simp] lemma v_lt_nrel (k r v : V) : v < ^nrel k r v :=
  le_iff_lt_succ.mp <| le_trans (le_trans (le_pair_right _ _) <| le_pair_right _ _) <|
    le_pair_right _ _

lemma nth_lt_qqRel_of_lt {i k r v : V} (hi : i < len v) : v.[i] < ^rel k r v :=
  lt_trans (nth_lt_self hi) (v_lt_rel _ _ _)

lemma nth_lt_qqNRel_of_lt {i k r v : V} (hi : i < len v) : v.[i] < ^nrel k r v :=
  lt_trans (nth_lt_self hi) (v_lt_nrel _ _ _)

@[simp] lemma lt_K!_left (p q : V) : p < p ^⋏ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma lt_K!_right (p q : V) : q < p ^⋏ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

@[simp] lemma lt_or_left (p q : V) : p < p ^⋎ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_left _ _) <| le_pair_right _ _
@[simp] lemma lt_or_right (p q : V) : q < p ^⋎ q :=
  le_iff_lt_succ.mp <| le_trans (le_pair_right _ _) <| le_pair_right _ _

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
    rintro (⟨k, r, v, hkr, hv, rfl⟩ | ⟨k, r, v, hkr, hv, rfl⟩ | rfl | rfl |
      ⟨q, r, hp, hq, rfl⟩ | ⟨q, r, hp, hq, rfl⟩ | ⟨q, h, rfl⟩ | ⟨q, h, rfl⟩)
    · disj 1; refine ⟨k, ?_, r, ?_, v, ?_, hkr, hv, rfl⟩ <;> simp;
    · disj 2; refine ⟨k, ?_, r, ?_, v, ?_, hkr, hv, rfl⟩ <;> simp;
    · disj 3; rfl;
    · disj 4; rfl;
    · disj 5; refine ⟨q, ?_, r, ?_, hp, hq, rfl⟩ <;> simp;
    · disj 6; refine ⟨q, ?_, r, ?_, hp, hq, rfl⟩ <;> simp;
    · disj 7; refine ⟨q, ?_, h, rfl⟩; simp;
    · disj 8; refine ⟨q, ?_, h, rfl⟩; simp;
  mpr := by
    unfold Phi;
    rintro (⟨k, _, r, _, v, _, hkr, hv, rfl⟩ | ⟨k, _, r, _, v, _, hkr, hv, rfl⟩ | rfl | rfl |
      ⟨q, _, r, _, hq, hr, rfl⟩ | ⟨q, _, r, _, hq, hr, rfl⟩ | ⟨q, _, hq, rfl⟩ | ⟨q, _, hq, rfl⟩)
    · disj 1; exact ⟨k, r, v, hkr, hv, rfl⟩;
    · disj 2; exact ⟨k, r, v, hkr, hv, rfl⟩;
    · disj 3; rfl;
    · disj 4; rfl;
    · disj 5; exact ⟨q, r, hq, hr, rfl⟩;
    · disj 6; exact ⟨q, r, hq, hr, rfl⟩;
    · disj 7; exact ⟨q, hq, rfl⟩;
    · disj 8; exact ⟨q, hq, rfl⟩;

def formulaAux : 𝚺ᴬ₀.Semisentence 2 := .mkSigma
  “p C.
    !qqVerumDef p ∨
    !qqFalsumDef p ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqAndDef p p₁ p₂) ∨
    (∃ p₁ < p, ∃ p₂ < p, p₁ ∈ C ∧ p₂ ∈ C ∧ !qqOrDef p p₁ p₂) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqAllDef p p₁) ∨
    (∃ p₁ < p, p₁ ∈ C ∧ !qqExsDef p p₁)”

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
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
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint]
    · intro v
      symm
      simpa [blueprint, formulaAux] using phi_iff L _ _
  monotone := by
    unfold Phi;
    rintro C C' hC _ x (h | h | h | h | ⟨q, r, hqC, hrC, rfl⟩ | ⟨q, r, hqC, hrC, rfl⟩ |
      ⟨q, hqC, rfl⟩ | ⟨q, hqC, rfl⟩)
    · disj 1; exact h;
    · disj 2; exact h;
    · disj 3; exact h;
    · disj 4; exact h;
    · disj 5; exact ⟨q, r, hC hqC, hC hrC, rfl⟩;
    · disj 6; exact ⟨q, r, hC hqC, hC hrC, rfl⟩;
    · disj 7; exact ⟨q, hC hqC, rfl⟩;
    · disj 8; exact ⟨q, hC hqC, rfl⟩;

instance : (construction L).StrongFinite V where
  strong_finite := by
    unfold construction Phi;
    rintro C _ x (h | h | h | h | ⟨q, r, hqC, hrC, rfl⟩ | ⟨q, r, hqC, hrC, rfl⟩ |
      ⟨q, hqC, rfl⟩ | ⟨q, hqC, rfl⟩)
    · disj 1; exact h;
    · disj 2; exact h;
    · disj 3; exact h;
    · disj 4; exact h;
    · disj 5; exact ⟨q, r, by simp [hqC], by simp [hrC], rfl⟩;
    · disj 6; exact ⟨q, r, by simp [hqC], by simp [hrC], rfl⟩;
    · disj 7; exact ⟨q, by simp [hqC], rfl⟩;
    · disj 8; exact ⟨q, by simp [hqC], rfl⟩;

end FormalizedFormula

variable (L)

def IsUFormula : V → Prop := (FormalizedFormula.construction L).Fixpoint ![]

noncomputable def isUFormula : 𝚫ᴬ₁.Semisentence 1 := (FormalizedFormula.blueprint L).fixpointDefΔ₁

variable {L}

namespace IsUFormula

open FormalizedFormula

section

instance defined : 𝚫ᴬ₁-Predicate IsUFormula (V := V) L via isUFormula L :=
  (construction L).fixpoint_definedΔ₁

instance definable : 𝚫ᴬ₁-Predicate IsUFormula (V := V) L := IsUFormula.defined.to_definable

instance definable' (Γ m) : Γᴬ-[m + 1]-Predicate IsUFormula (V := V) L :=
  IsUFormula.definable.of_deltaOne

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
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact mk <| by disj 1; exact ⟨k, r, v, hkr, hv, rfl⟩⟩

set_option linter.flexible false in
@[simp] lemma nrel {k r v : V} :
    IsUFormula L (^nrel k r v) ↔ L.IsRel k r ∧ IsUTermVec L k v :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨k, r, v, hkr, hv, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hkr, hv⟩,
   by rintro ⟨hkr, hv⟩
      exact mk <| by disj 2; exact ⟨k, r, v, hkr, hv, rfl⟩⟩

@[simp] lemma verum : IsUFormula L (^⊤ : V) :=
  mk <| by disj 3; rfl

@[simp] lemma falsum : IsUFormula L (^⊥ : V) :=
  mk <| by disj 4; rfl

set_option linter.flexible false in
@[simp] lemma and {p q : V} :
    IsUFormula L (p ^⋏ q) ↔ IsUFormula L p ∧ IsUFormula L q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, hp, hq, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact mk <| by disj 5; exact ⟨p, q, hp, hq, rfl⟩⟩

set_option linter.flexible false in
@[simp] lemma or {p q : V} :
    IsUFormula L (p ^⋎ q) ↔ IsUFormula L p ∧ IsUFormula L q :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, hp, hq, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨hp, hq⟩,
   by rintro ⟨hp, hq⟩
      exact mk <| by disj 6; exact ⟨p, q, hp, hq, rfl⟩⟩

set_option linter.flexible false in
@[simp] lemma all {p : V} :
    IsUFormula L (^∀ p) ↔ IsUFormula L p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, hp, h⟩ | ⟨_, _, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact hp,
   by rintro hp
      exact mk <| by disj 7; exact ⟨p, hp, rfl⟩⟩

set_option linter.flexible false in
@[simp] lemma ex {p : V} :
    IsUFormula L (^∃ p) ↔ IsUFormula L p :=
  ⟨by intro h
      rcases h.case with (⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ | h | h |
        ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, hp, h⟩) <;>
          simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs] at h
      · rcases h with ⟨rfl, rfl, rfl, rfl⟩; exact hp,
   by rintro hp
      exact mk <| by disj 8; exact ⟨p, hp, rfl⟩⟩

lemma pos {p : V} (h : IsUFormula L p) : 0 < p := by
  rcases h.case with (⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ |
    ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;>
    simp [qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]

--lemma IsSemiformula.pos {n p : V} (h : Semiformula L n p) : 0 < p := h.1.pos

@[simp] lemma not_zero : ¬IsUFormula L (0 : V) := by intro h; simpa using h.pos

-- @[simp] lemma IsSemiformula.not_zero (m : V) : ¬Semiformula L m (0 : V) := by
--   intro h; simpa using h.pos

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
@[simp] lemma IsSemiformula.all {n p : V} :
    Semiformula L n (^∀ p) ↔ Semiformula L (n + 1) p := by simp [IsSemiformula]
@[simp] lemma IsSemiformula.exs {n p : V} :
    Semiformula L n (^∃ p) ↔ Semiformula L (n + 1) p := by simp [IsSemiformula]
-/

lemma induction1 (Γ : Polarity) {P : V → Prop} (hP : Γᴬ-[1]-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hexs : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
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
    · exact hexs p (hC p hp).1 (hC p hp).2)

lemma ISigma1.sigma1_succ_induction {P : V → Prop} (hP : 𝚺ᴬ₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hexs : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p :=
  induction1 𝚺 hP hrel hnrel hverum hfalsum hand hor hall hexs

lemma ISigma1.pi1_succ_induction {P : V → Prop} (hP : 𝚷ᴬ₁-Predicate P)
    (hrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^rel k r v))
    (hnrel : ∀ k r v, L.IsRel k r → IsUTermVec L k v → P (^nrel k r v))
    (hverum : P ^⊤)
    (hfalsum : P ^⊥)
    (hand : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋏ q))
    (hor : ∀ p q, IsUFormula L p → IsUFormula L q → P p → P q → P (p ^⋎ q))
    (hall : ∀ p, IsUFormula L p → P p → P (^∀ p))
    (hexs : ∀ p, IsUFormula L p → P p → P (^∃ p)) :
    ∀ p, IsUFormula L p → P p :=
  induction1 𝚷 hP hrel hnrel hverum hfalsum hand hor hall hexs

/-
lemma IsSemiformula.induction (Γ) {P : V → V → Prop} (hP : Γᴬ-[1]-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, Semiformula L n p → P n p := by
  suffices ∀ p, IsUFormula L p → ∀ n ≤ p, fstIdx p = n → P n p
  by rintro n p ⟨h, rfl⟩; exact this p h (fstIdx p) (by simp) rfl
  apply IsUFormula.induction (P := fun p ↦ ∀ n ≤ p, fstIdx p = n → P n p) Γ
  · apply Bounding.HierarchySymbol.Definable.arithmetic_ball_le (by definability)
    apply Bounding.HierarchySymbol.Definable.imp (by definability)
    simp; exact hP
  · rintro n k r v hr hv _ _ rfl; simpa using hrel n k r v hr hv
  · rintro n k r v hr hv _ _ rfl; simpa using hnrel n k r v hr hv
  · rintro n _ _ rfl; simpa using hverum n
  · rintro n _ _ rfl; simpa using hfalsum n
  · rintro n p q hp hq ihp ihq _ _ rfl
    simpa using hand n p q hp hq
      (by simpa [hp.2] using ihp (fstIdx p) (by simp) rfl)
      (by simpa [hq.2] using ihq (fstIdx q) (by simp) rfl)
  · rintro n p q hp hq ihp ihq _ _ rfl
    simpa using hor n p q hp hq
      (by simpa [hp.2] using ihp (fstIdx p) (by simp) rfl)
      (by simpa [hq.2] using ihq (fstIdx q) (by simp) rfl)
  · rintro n p hp ih _ _ rfl
    simpa using hall n p hp (by simpa [hp.2] using ih (fstIdx p) (by simp) rfl)
  · rintro n p hp ih _ _ rfl
    simpa using hexs n p hp (by simpa [hp.2] using ih (fstIdx p) (by simp) rfl)

lemma IsSemiformula.induction_sigma₁ {P : V → V → Prop} (hP : 𝚺ᴬ₁-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, Semiformula L n p → P n p :=
  IsSemiformula.induction 𝚺 hP hrel hnrel hverum hfalsum hand hor hall hexs

lemma IsSemiformula.pi1_structural_induction {P : V → V → Prop} (hP : 𝚷ᴬ₁-Relation P)
    (hrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^rel n k r v))
    (hnrel : ∀ n k r v, L.IsRel k r → SemitermVec L k n v → P n (^nrel n k r v))
    (hverum : ∀ n, P n ^⊤[n])
    (hfalsum : ∀ n, P n ^⊥[n])
    (hand : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋏ q))
    (hor : ∀ n p q, Semiformula L n p → Semiformula L n q → P n p → P n q → P n (p ^⋎ q))
    (hall : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∀ p))
    (hexs : ∀ n p, Semiformula L (n + 1) p → P (n + 1) p → P n (^∃ p)) :
    ∀ n p, Semiformula L n p → P n p :=
  IsSemiformula.induction 𝚷 hP hrel hnrel hverum hfalsum hand hor hall hexs
-/

end IsUFormula

end FFL.FirstOrder.Arithmetic.Bootstrapping
