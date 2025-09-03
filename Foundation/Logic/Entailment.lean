import Foundation.Logic.LogicSymbol
import Foundation.Logic.Semantics
import Foundation.Vorspiel.AdjunctiveSet

/-!
# Basic definitions and properties of proof system related notions

This file defines a characterization of the system/proof/provability/calculus of formulae.
Also defines soundness and completeness.

## Main Definitions
* `LO.Entailment F S`: a general framework of deductive system `S` for formulae `F`.
* `LO.Entailment.Inconsistent 𝓢`: a proposition that states that all formulae in `F` is provable from `𝓢`.
* `LO.Entailment.Consistent 𝓢`: a proposition that states that `𝓢` is not inconsistent.
* `LO.Entailment.Sound 𝓢 𝓜`: provability from `𝓢` implies satisfiability on `𝓜`.
* `LO.Entailment.Complete 𝓢 𝓜`: satisfiability on `𝓜` implies provability from `𝓢`.

## Notation
* `𝓢 ⊢ φ`: a type of formalized proofs of `φ : F` from deductive system `𝓢 : S`.
* `𝓢 ⊢! φ`: a proposition that states there is a proof of `φ` from `𝓢`, i.e. `φ` is provable from `𝓢`.
* `𝓢 ⊬ φ`: a proposition that states `φ` is not provable from `𝓢`.
* `𝓢 ⊢* T`: a type of formalized proofs for each formulae in a set `T` from `𝓢`.
* `𝓢 ⊢!* T`: a proposition that states each formulae in `T` is provable from `𝓢`.

-/

namespace LO

/-- Entailment relation on proof system `S` and formula `F` -/
class Entailment (F : outParam Type*) (S : Type*) where
  Prf : S → F → Type*

infix:45 " ⊢ " => Entailment.Prf

namespace Entailment

variable {F : Type*} {S T U : Type*} [Entailment F S] [Entailment F T] [Entailment F U]

section

variable (𝓢 : S)

/-- Proposition that states `φ` is provable. -/
def Provable (φ : F) : Prop := Nonempty (𝓢 ⊢ φ)

/-- Abbreviation for unprovability. -/
abbrev Unprovable (φ : F) : Prop := ¬Provable 𝓢 φ

infix:45 " ⊢! " => Provable

infix:45 " ⊬ " => Unprovable

/-- Proofs of set of formulae. -/
def PrfSet (s : Set F) : Type _ := {φ : F} → φ ∈ s → 𝓢 ⊢ φ

/-- Proposition for existance of proofs of set of formulae. -/
def ProvableSet (s : Set F) : Prop := ∀ {φ}, φ ∈ s → 𝓢 ⊢! φ

infix:45 " ⊢* " => PrfSet

infix:45 " ⊢!* " => ProvableSet

/-- Set of all provable formulae. -/
def theory : Set F := {φ | 𝓢 ⊢! φ}

end

lemma unprovable_iff_isEmpty {𝓢 : S} {φ : F} :
    𝓢 ⊬ φ ↔ IsEmpty (𝓢 ⊢ φ) := by simp [Provable, Unprovable]

noncomputable def Provable.get {𝓢 : S} {φ : F} (h : 𝓢 ⊢! φ) : 𝓢 ⊢ φ :=
  Classical.choice h

lemma provableSet_iff {𝓢 : S} {s : Set F} :
    𝓢 ⊢!* s ↔ Nonempty (𝓢 ⊢* s) := by
  simp [ProvableSet, PrfSet, Provable, Classical.nonempty_pi, ←imp_iff_not_or]

noncomputable def ProvableSet.get {𝓢 : S} {s : Set F} (h : 𝓢 ⊢!* s) : 𝓢 ⊢* s :=
  Classical.choice (α := 𝓢 ⊢* s) (provableSet_iff.mp h : Nonempty (𝓢 ⊢* s))

/-- Provability strength relation of proof systems -/
class WeakerThan (𝓢 : S) (𝓣 : T) : Prop where
  subset : theory 𝓢 ⊆ theory 𝓣

infix:40 " ⪯ " => WeakerThan

/-- Strict provability strength relation of proof systems -/
class StrictlyWeakerThan (𝓢 : S) (𝓣 : T) : Prop where
   weakerThan : 𝓢 ⪯ 𝓣
   notWT : ¬𝓣 ⪯ 𝓢

infix:40 " ⪱ " => StrictlyWeakerThan

/-- Provability equivalence relation of proof systems -/
class Equiv (𝓢 : S) (𝓣 : T) : Prop where
  eq : theory 𝓢 = theory 𝓣

infix:40 " ≊ " => Equiv

/-! ### Provability strength -/

section WeakerThan

variable {𝓢 : S} {𝓣 : T} {𝓤 : U}

@[instance, simp, refl] protected lemma WeakerThan.refl (𝓢 : S) : 𝓢 ⪯ 𝓢 := ⟨Set.Subset.refl _⟩

lemma WeakerThan.wk (h : 𝓢 ⪯ 𝓣) {φ} : 𝓢 ⊢! φ → 𝓣 ⊢! φ := @h.subset φ

lemma WeakerThan.pbl [h : 𝓢 ⪯ 𝓣] {φ} : 𝓢 ⊢! φ → 𝓣 ⊢! φ := @h.subset φ

@[trans] lemma WeakerThan.trans : 𝓢 ⪯ 𝓣 → 𝓣 ⪯ 𝓤 → 𝓢 ⪯ 𝓤 := fun w₁ w₂ ↦ ⟨Set.Subset.trans w₁.subset w₂.subset⟩

instance : Trans (α := S) (β := T) (γ := U) (· ⪯ ·) (· ⪯ ·) (· ⪯ ·) where
  trans := WeakerThan.trans

lemma weakerThan_iff : 𝓢 ⪯ 𝓣 ↔ (∀ {φ}, 𝓢 ⊢! φ → 𝓣 ⊢! φ) :=
  ⟨fun h _ hf ↦ h.subset hf, fun h ↦ ⟨fun _ hf ↦ h hf⟩⟩

lemma not_weakerThan_iff : ¬𝓢 ⪯ 𝓣 ↔ (∃ φ, 𝓢 ⊢! φ ∧ 𝓣 ⊬ φ) := by simp [weakerThan_iff, Unprovable];

lemma strictlyWeakerThan_iff : 𝓢 ⪱ 𝓣 ↔ (∀ {φ}, 𝓢 ⊢! φ → 𝓣 ⊢! φ) ∧ (∃ φ, 𝓢 ⊬ φ ∧ 𝓣 ⊢! φ) := by
  constructor
  · rintro ⟨wt, nwt⟩
    exact ⟨weakerThan_iff.mp wt, by rcases not_weakerThan_iff.mp nwt with ⟨φ, ht, hs⟩; exact ⟨φ, hs, ht⟩⟩
  · rintro ⟨h, φ, hs, ht⟩
    exact ⟨weakerThan_iff.mpr h, not_weakerThan_iff.mpr ⟨φ, ht, hs⟩⟩

lemma swt_of_swt_of_wt : 𝓢 ⪱ 𝓣 → 𝓣 ⪯ 𝓤 → 𝓢 ⪱ 𝓤 := by
  rintro ⟨h₁, nh₁⟩ h₂
  constructor
  . exact WeakerThan.trans h₁ h₂
  · intro h
    exact nh₁ (WeakerThan.trans h₂ h)

lemma swt_of_wt_of_swt : 𝓢 ⪯ 𝓣 → 𝓣 ⪱ 𝓤 → 𝓢 ⪱ 𝓤 := by
  rintro h₁ ⟨h₂, nh₂⟩
  constructor
  . exact WeakerThan.trans h₁ h₂
  · intro h
    exact nh₂ (WeakerThan.trans h h₁)

instance [𝓢 ⪱ 𝓣] : 𝓢 ⪯ 𝓣 := StrictlyWeakerThan.weakerThan

lemma StrictlyWeakerThan.trans : 𝓢 ⪱ 𝓣 → 𝓣 ⪱ 𝓤 → 𝓢 ⪱ 𝓤 := fun h₁ h₂ ↦ swt_of_swt_of_wt h₁ h₂.weakerThan

instance : Trans (α := S) (β := T) (γ := U) (· ⪱ ·) (· ⪯ ·) (· ⪱ ·) where
  trans := swt_of_swt_of_wt

instance : Trans (α := S) (β := T) (γ := U) (· ⪯ ·) (· ⪱ ·) (· ⪱ ·) where
  trans := swt_of_wt_of_swt

instance : Trans (α := S) (β := T) (γ := U) (· ⪱ ·) (· ⪱ ·) (· ⪱ ·) where
  trans := StrictlyWeakerThan.trans

lemma weakening (h : 𝓢 ⪯ 𝓣) {φ} : 𝓢 ⊢! φ → 𝓣 ⊢! φ := weakerThan_iff.mp h

lemma StrictlyWeakerThan.of_unprovable_provable {𝓢 : S} {𝓣 : T} [𝓢 ⪯ 𝓣] {φ : F}
    (hS : 𝓢 ⊬ φ) (hT : 𝓣 ⊢! φ) : 𝓢 ⪱ 𝓣 := ⟨inferInstance, fun h ↦ hS (h.wk hT)⟩

lemma Equiv.iff : 𝓢 ≊ 𝓣 ↔ (∀ φ, 𝓢 ⊢! φ ↔ 𝓣 ⊢! φ) :=
  ⟨fun e ↦ by simpa [Set.ext_iff, theory] using e.eq, fun e ↦ ⟨by simpa [Set.ext_iff, theory] using e⟩⟩

@[instance, simp, refl] protected lemma Equiv.refl (𝓢 : S) : 𝓢 ≊ 𝓢 := ⟨rfl⟩

@[symm] lemma Equiv.symm : 𝓢 ≊ 𝓣 → 𝓣 ≊ 𝓢 := fun e ↦ ⟨Eq.symm e.eq⟩

@[trans] lemma Equiv.trans : 𝓢 ≊ 𝓣 → 𝓣 ≊ 𝓤 → 𝓢 ≊ 𝓤 := fun e₁ e₂ ↦ ⟨Eq.trans e₁.eq e₂.eq⟩

lemma Equiv.antisymm_iff : 𝓢 ≊ 𝓣 ↔ 𝓢 ⪯ 𝓣 ∧ 𝓣 ⪯ 𝓢 := by
  constructor
  · intro e
    exact ⟨⟨Set.Subset.antisymm_iff.mp e.eq |>.1⟩, ⟨Set.Subset.antisymm_iff.mp e.eq |>.2⟩⟩
  · rintro ⟨w₁, w₂⟩
    exact ⟨Set.Subset.antisymm w₁.subset w₂.subset⟩

alias ⟨_, Equiv.antisymm⟩ := Equiv.antisymm_iff

lemma Equiv.le : 𝓢 ≊ 𝓣 → 𝓢 ⪯ 𝓣 := fun e ↦ ⟨by rw [e.eq]⟩

instance : Trans (α := S) (β := T) (γ := U) (· ≊ ·) (· ≊ ·) (· ≊ ·) where
  trans := Equiv.trans

instance : Trans (α := S) (β := T) (γ := U) (· ≊ ·) (· ⪯ ·) (· ⪯ ·) where
  trans h₁ h₂ := WeakerThan.trans h₁.le h₂

instance : Trans (α := S) (β := T) (γ := U) (· ≊ ·) (· ≊ ·) (· ⪯ ·) where
  trans h₁ h₂ := WeakerThan.trans h₁.le h₂.le

instance : Trans (α := S) (β := T) (γ := U) (· ⪯ ·) (· ≊ ·) (· ⪯ ·) where
  trans h₁ h₂ := WeakerThan.trans h₁ h₂.le

instance : Trans (α := S) (β := T) (γ := U) (· ≊ ·) (· ⪱ ·) (· ⪱ ·) where
  trans h₁ h₂ := swt_of_wt_of_swt h₁.le h₂

instance : Trans (α := S) (β := T) (γ := U) (· ⪱ ·) (· ≊ ·) (· ⪱ ·) where
  trans h₁ h₂ := swt_of_swt_of_wt h₁ h₂.le

end WeakerThan

/-! ### Consistency and inconsistency -/

@[simp] lemma provableSet_theory (𝓢 : S) : 𝓢 ⊢!* theory 𝓢 := fun hf ↦ hf

def Inconsistent (𝓢 : S) : Prop := ∀ φ, 𝓢 ⊢! φ

class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢

lemma inconsistent_def {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∀ φ, 𝓢 ⊢! φ := by simp [Inconsistent]

lemma inconsistent_iff_theory_eq {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by
  simp [Inconsistent, Set.ext_iff, theory]

lemma not_inconsistent_iff_consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩

alias ⟨_, Consistent.not_inc⟩ := not_inconsistent_iff_consistent

lemma not_consistent_iff_inconsistent {𝓢 : S} :
    ¬Consistent 𝓢 ↔ Inconsistent 𝓢 := by simp [←not_inconsistent_iff_consistent]

alias ⟨_, Inconsistent.not_con⟩ := not_consistent_iff_inconsistent

lemma consistent_iff_exists_unprovable {𝓢 : S} :
    Consistent 𝓢 ↔ ∃ φ, 𝓢 ⊬ φ := by
  simp [←not_inconsistent_iff_consistent, inconsistent_def]

alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable

lemma Consistent.of_unprovable {𝓢 : S} {φ} (h : 𝓢 ⊬ φ) : Consistent 𝓢 :=
  ⟨fun hp ↦ h (hp φ)⟩

lemma inconsistent_iff_theory_eq_univ {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by simp [inconsistent_def, theory, Set.ext_iff]

alias ⟨Inconsistent.theory_eq, _⟩ := inconsistent_iff_theory_eq_univ

lemma Inconsistent.of_ge {𝓢 : S} {𝓣 : T} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⪯ 𝓣) : Inconsistent 𝓣 :=
  fun φ ↦ h.subset (h𝓢 φ)

lemma Consistent.of_le {𝓢 : S} {𝓣 : T} (h𝓢 : Consistent 𝓢) (h : 𝓣 ⪯ 𝓢) : Consistent 𝓣 :=
  ⟨fun H ↦ not_consistent_iff_inconsistent.mpr (H.of_ge h) h𝓢⟩

variable (S)

class DeductiveExplosion [LogicalConnective F] where
  dexp {𝓢 : S} : 𝓢 ⊢ ⊥ → (φ : F) → 𝓢 ⊢ φ

variable {S}

section

variable [LogicalConnective F] [DeductiveExplosion S]

def DeductiveExplosion.dexp! {𝓢 : S} (h : 𝓢 ⊢! ⊥) (φ : F) : 𝓢 ⊢! φ := by
  rcases h with ⟨b⟩; exact ⟨dexp b φ⟩

lemma inconsistent_iff_provable_bot {𝓢 : S} :
    Inconsistent 𝓢 ↔ 𝓢 ⊢! ⊥ := ⟨fun h ↦ h ⊥, fun h φ ↦ DeductiveExplosion.dexp! h φ⟩

alias ⟨_, inconsistent_of_provable⟩ := inconsistent_iff_provable_bot

lemma consistent_iff_unprovable_bot {𝓢 : S} :
    Consistent 𝓢 ↔ 𝓢 ⊬ ⊥ := by
  simp [inconsistent_iff_provable_bot, ←not_inconsistent_iff_consistent]

alias ⟨Consistent.not_bot, _⟩ := consistent_iff_unprovable_bot

end

/-! ### Completeness and incompleteness -/

section

variable [LogicalConnective F] (𝓢 : S)

class Complete : Prop where
  con : ∀ φ, 𝓢 ⊢! φ ∨ 𝓢 ⊢! ∼φ

def Independent (φ : F) : Prop := 𝓢 ⊬ φ ∧ 𝓢 ⊬ ∼φ

class Incomplete : Prop where
  indep : ∃ φ, Independent 𝓢 φ

variable {𝓢}

lemma complete_def : Complete 𝓢 ↔ ∀ φ, 𝓢 ⊢! φ ∨ 𝓢 ⊢! ∼φ :=
  ⟨fun h ↦ h.con, Complete.mk⟩

lemma incomplete_def : Incomplete 𝓢 ↔ ∃ φ, Independent 𝓢 φ :=
  ⟨fun h ↦ h.indep, Incomplete.mk⟩

@[simp] lemma not_complete_iff_incomplete : ¬Complete 𝓢 ↔ Incomplete 𝓢 := by
  simp [complete_def, incomplete_def, Independent, not_or]

@[simp] lemma not_incomplete_iff_complete : ¬Incomplete 𝓢 ↔ Complete 𝓢 :=
  Iff.symm <| iff_not_comm.mp not_complete_iff_incomplete.symm

instance consistent_of_incomplete [h : Incomplete 𝓢] : Consistent 𝓢 :=
  consistent_iff_exists_unprovable.mpr <| by rcases h.indep with ⟨φ, hφ⟩; exact ⟨φ, hφ.1⟩

end

/-! ### Axiomatized provability -/

variable (S T)

class Axiomatized [AdjunctiveSet F S] where
  prfAxm {𝓢 : S} : 𝓢 ⊢* AdjunctiveSet.set 𝓢
  weakening {𝓢 𝓣 : S} : 𝓢 ⊆ 𝓣 → 𝓢 ⊢ φ → 𝓣 ⊢ φ

alias byAxm := Axiomatized.prfAxm
alias wk := Axiomatized.weakening

class StrongCut [AdjunctiveSet F T] where
  cut {𝓢 : S} {𝓣 : T} {φ} : 𝓢 ⊢* AdjunctiveSet.set 𝓣 → 𝓣 ⊢ φ → 𝓢 ⊢ φ

variable {S T}

section Axiomatized

namespace Axiomatized

variable [AdjunctiveSet F S] [Axiomatized S] {𝓢 𝓣 : S}

@[simp] lemma provable_axm (𝓢 : S) : 𝓢 ⊢!* AdjunctiveSet.set 𝓢 := fun hf ↦ ⟨prfAxm hf⟩

lemma axm_subset (𝓢 : S) : AdjunctiveSet.set 𝓢 ⊆ theory 𝓢 := fun _ hp ↦ provable_axm 𝓢 hp

protected def adjoin (φ : F) (𝓢 : S) : adjoin φ 𝓢 ⊢ φ := prfAxm (by simp)

@[simp] def adjoin! (φ : F) (𝓢 : S) : adjoin φ 𝓢 ⊢! φ := provable_axm _ (by simp)

lemma le_of_subset (h : 𝓢 ⊆ 𝓣) : 𝓢 ⪯ 𝓣 := ⟨by rintro φ ⟨b⟩; exact ⟨weakening h b⟩⟩

lemma weakening! (h : 𝓢 ⊆ 𝓣 := by simp) {φ} : 𝓢 ⊢! φ → 𝓣 ⊢! φ := by rintro ⟨b⟩; exact ⟨weakening h b⟩

def weakerThanOfSubset (h : 𝓢 ⊆ 𝓣) : 𝓢 ⪯ 𝓣 := ⟨fun _ ↦ weakening! h⟩

end Axiomatized

alias by_axm := Axiomatized.provable_axm
alias wk! := Axiomatized.weakening!

section axiomatized

variable [AdjunctiveSet F S] [AdjunctiveSet F T] [Axiomatized S]

def FiniteAxiomatizable (𝓢 : S) : Prop := ∃ 𝓕 : S, AdjunctiveSet.Finite 𝓕 ∧ 𝓕 ≊ 𝓢

lemma Consistent.of_subset {𝓢 𝓣 : S} (h𝓢 : Consistent 𝓢) (h : 𝓣 ⊆ 𝓢) : Consistent 𝓣 :=
  h𝓢.of_le (Axiomatized.le_of_subset h)

lemma Inconsistent.of_supset {𝓢 𝓣 : S} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⊆ 𝓣) : Inconsistent 𝓣 :=
  h𝓢.of_ge (Axiomatized.le_of_subset h)

end axiomatized

namespace StrongCut

variable [AdjunctiveSet F T] [StrongCut S T]

lemma cut! {𝓢 : S} {𝓣 : T} {φ : F} (H : 𝓢 ⊢!* AdjunctiveSet.set 𝓣) (hp : 𝓣 ⊢! φ) : 𝓢 ⊢! φ := by
  rcases hp with ⟨b⟩; exact ⟨StrongCut.cut H.get b⟩

end StrongCut

noncomputable def WeakerThan.ofAxm! [AdjunctiveSet F S] [StrongCut S S] {𝓢₁ 𝓢₂ : S} (B : 𝓢₂ ⊢!* AdjunctiveSet.set 𝓢₁) :
    𝓢₁ ⪯ 𝓢₂ := ⟨fun _ b ↦ StrongCut.cut! B b⟩

def WeakerThan.ofSubset [AdjunctiveSet F S] [Axiomatized S] {𝓢 𝓣 : S} (h : 𝓢 ⊆ 𝓣) : 𝓢 ⪯ 𝓣 := ⟨fun _ ↦ wk! h⟩

/-! ### Compactness -/

variable (S)

class Compact [AdjunctiveSet F S] where
  Γ {𝓢 : S} {φ : F} : 𝓢 ⊢ φ → S
  ΓPrf {𝓢 : S} {φ : F} (b : 𝓢 ⊢ φ) : Γ b ⊢ φ
  Γ_subset {𝓢 : S} {φ : F} (b : 𝓢 ⊢ φ) : Γ b ⊆ 𝓢
  Γ_finite {𝓢 : S} {φ : F} (b : 𝓢 ⊢ φ) : AdjunctiveSet.Finite (Γ b)

variable {S}

namespace Compact

variable [AdjunctiveSet F S] [Compact S]

lemma finite_provable {𝓢 : S} (h : 𝓢 ⊢! φ) : ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ AdjunctiveSet.Finite 𝓕 ∧ 𝓕 ⊢! φ := by
  rcases h with ⟨b⟩
  exact ⟨Γ b, Γ_subset b, Γ_finite b, ⟨ΓPrf b⟩⟩

end Compact

end Axiomatized

end Entailment

namespace Entailment

variable {S : Type*} {F : Type*} [LogicalConnective F] [Entailment F S]

section

variable [DeductiveExplosion S] [AdjunctiveSet F S] [Axiomatized S] [Compact S]

lemma inconsistent_compact {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ AdjunctiveSet.Finite 𝓕 ∧ Inconsistent 𝓕 :=
  ⟨fun H ↦ by rcases Compact.finite_provable (H ⊥) with ⟨𝓕, h𝓕, fin, h⟩; exact ⟨𝓕, h𝓕, fin, inconsistent_of_provable h⟩, by
    rintro ⟨𝓕, h𝓕, _, H⟩; exact H.of_supset h𝓕⟩

lemma consistent_compact {𝓢 : S} :
    Consistent 𝓢 ↔ ∀ 𝓕 : S, 𝓕 ⊆ 𝓢 → AdjunctiveSet.Finite 𝓕 → Consistent 𝓕 := by
  simp [←not_inconsistent_iff_consistent, inconsistent_compact (𝓢 := 𝓢)]

end

/-! ### Deduction theorem -/

variable (S)

class Deduction [Adjoin F S] where
  ofInsert {φ ψ : F} {𝓢 : S} : adjoin φ 𝓢 ⊢ ψ → 𝓢 ⊢ φ ➝ ψ
  inv {φ ψ : F} {𝓢 : S} : 𝓢 ⊢ φ ➝ ψ → adjoin φ 𝓢 ⊢ ψ

variable {S}

section deduction

variable [Adjoin F S] [Deduction S] {𝓢 : S} {φ ψ : F}

alias deduction := Deduction.ofInsert

lemma Deduction.of_insert! (h : adjoin φ 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ➝ ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.ofInsert b⟩

alias deduction! := Deduction.of_insert!

lemma Deduction.inv! (h : 𝓢 ⊢! φ ➝ ψ) : adjoin φ 𝓢 ⊢! ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.inv b⟩

lemma deduction_iff : adjoin φ 𝓢 ⊢! ψ ↔ 𝓢 ⊢! φ ➝ ψ := ⟨deduction!, Deduction.inv!⟩

end deduction

end Entailment

/-! ### Soundness and Completeness -/

section

variable {S : Type*} {F : Type*} [Entailment F S] {M : Type*} [Semantics F M]

class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {φ : F}, 𝓢 ⊢! φ → 𝓜 ⊧ φ

class Complete (𝓢 : S) (𝓜 : M) : Prop where
  complete : ∀ {φ : F}, 𝓜 ⊧ φ → 𝓢 ⊢! φ

namespace Sound

section

variable {𝓢 𝓣 : S} {𝓜 𝓝 : M} [Sound 𝓢 𝓜] [Sound 𝓣 𝓝]

lemma not_provable_of_countermodel {φ : F} (hp : ¬𝓜 ⊧ φ) : 𝓢 ⊬ φ :=
  fun b ↦ hp (Sound.sound b)

lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → Entailment.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨φ, hf⟩; exact hf (Sound.sound (h φ))⟩

lemma consistent_of_model [LogicalConnective F] [Semantics.Bot M] (𝓜 : M) [Sound 𝓢 𝓜] : Entailment.Consistent 𝓢 :=
  consistent_of_meaningful (𝓜 := 𝓜) inferInstance

lemma realizeSet_of_prfSet {T : Set F} (b : 𝓢 ⊢!* T) : 𝓜 ⊧* T :=
  ⟨fun _ hf ↦ sound (b hf)⟩

end

section

variable {𝓢 : S} {T : Set F} [Sound 𝓢 (Semantics.models M T)]

lemma consequence_of_provable {φ : F} : 𝓢 ⊢! φ → T ⊨[M] φ := sound

lemma consistent_of_satisfiable [LogicalConnective F] [∀ 𝓜 : M, Semantics.Meaningful 𝓜] : Semantics.Satisfiable M T → Entailment.Consistent 𝓢 :=
  fun H ↦ consistent_of_meaningful (Semantics.meaningful_iff_satisfiableSet.mp H)

end

end Sound

namespace Complete

section

variable {𝓢 : S} {𝓜 : M} [Complete 𝓢 𝓜]

lemma exists_countermodel_of_not_provable {φ : F} (h : 𝓢 ⊬ φ) : ¬𝓜 ⊧ φ := by
  contrapose! h;
  simpa using Complete.complete (𝓢 := 𝓢) h;

lemma meaningful_of_consistent : Entailment.Consistent 𝓢 → Semantics.Meaningful 𝓜 := by
  contrapose
  suffices (∀ (φ : F), 𝓜 ⊧ φ) → Entailment.Inconsistent 𝓢 by
    simpa [Semantics.not_meaningful_iff, Entailment.not_consistent_iff_inconsistent]
  exact fun h φ ↦ Complete.complete (h φ)

end

section

variable {𝓢 : S} {s : Set F} [Complete 𝓢 (Semantics.models M s)]

lemma provable_of_consequence {φ : F} : s ⊨[M] φ → 𝓢 ⊢! φ := complete

lemma provable_iff_consequence [Sound 𝓢 (Semantics.models M s)] {φ : F} : s ⊨[M] φ ↔ 𝓢 ⊢! φ := ⟨complete, Sound.sound⟩


section

variable [LogicalConnective F] [∀ 𝓜 : M, Semantics.Meaningful 𝓜]

lemma satisfiable_of_consistent :
    Entailment.Consistent 𝓢 → Semantics.Satisfiable M s :=
  fun H ↦ Semantics.meaningful_iff_satisfiableSet.mpr (meaningful_of_consistent H)

lemma inconsistent_of_unsatisfiable :
    ¬Semantics.Satisfiable M s → Entailment.Inconsistent 𝓢 := by
  contrapose; simpa [←Entailment.not_consistent_iff_inconsistent] using satisfiable_of_consistent

lemma consistent_iff_satisfiable [Sound 𝓢 (Semantics.models M s)] : Entailment.Consistent 𝓢 ↔ Semantics.Satisfiable M s :=
  ⟨satisfiable_of_consistent, Sound.consistent_of_satisfiable⟩

end

lemma weakerthan_of_models {𝓣 : S} {t : Set F} [Sound 𝓣 (Semantics.models M t)]
    (H : ∀ 𝓜 : M, 𝓜 ⊧* s → 𝓜 ⊧* t) : 𝓣 ⪯ 𝓢 :=
  Entailment.weakerThan_iff.mpr <| fun h ↦ provable_of_consequence <| fun 𝓜 h𝓜 ↦ Sound.consequence_of_provable (M := M) (T := t) h (H 𝓜 h𝓜)

end

end Complete

end

end LO
