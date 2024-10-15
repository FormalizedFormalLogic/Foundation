import Foundation.Logic.LogicSymbol
import Foundation.Logic.Semantics
import Foundation.Vorspiel.Collection

/-!
# Basic definitions and properties of proof system related notions

This file defines a characterization of the system/proof/provability/calculus of formulae.
Also defines soundness and completeness.

## Main Definitions
* `LO.System F S`: a general framework of deductive system `S` for formulae `F`.
* `LO.System.Inconsistent 𝓢`: a proposition that states that all formulae in `F` is provable from `𝓢`.
* `LO.System.Consistent 𝓢`: a proposition that states that `𝓢` is not inconsistent.
* `LO.System.Sound 𝓢 𝓜`: provability from `𝓢` implies satisfiability on `𝓜`.
* `LO.System.Complete 𝓢 𝓜`: satisfiability on `𝓜` implies provability from `𝓢`.

## Notation
* `𝓢 ⊢ p`: a type of formalized proofs of `p : F` from deductive system `𝓢 : S`.
* `𝓢 ⊢! p`: a proposition that states there is a proof of `p` from `𝓢`, i.e. `p` is provable from `𝓢`.
* `𝓢 ⊬ p`: a proposition that states `p` is not provable from `𝓢`.
* `𝓢 ⊢* T`: a type of formalized proofs for each formulae in a set `T` from `𝓢`.
* `𝓢 ⊢!* T`: a proposition that states each formulae in `T` is provable from `𝓢`.

-/

namespace LO

class System (F : outParam Type*) (S : Type*) where
  Prf : S → F → Type*

infix:45 " ⊢ " => System.Prf

namespace System

variable {F : Type*} {S T U : Type*} [System F S] [System F T] [System F U]

section

variable (𝓢 : S)

def Provable (f : F) : Prop := Nonempty (𝓢 ⊢ f)

abbrev Unprovable (f : F) : Prop := ¬Provable 𝓢 f

infix:45 " ⊢! " => Provable

infix:45 " ⊬ " => Unprovable

def PrfSet (s : Set F) : Type _ := {f : F} → f ∈ s → 𝓢 ⊢ f

def ProvableSet (s : Set F) : Prop := ∀ {f}, f ∈ s → 𝓢 ⊢! f

infix:45 " ⊢* " => PrfSet

infix:45 " ⊢!* " => ProvableSet

def theory : Set F := {f | 𝓢 ⊢! f}

end

lemma unprovable_iff_isEmpty {𝓢 : S} {f : F} :
    𝓢 ⊬ f ↔ IsEmpty (𝓢 ⊢ f) := by simp [Provable, Unprovable]

noncomputable def Provable.get {𝓢 : S} {f : F} (h : 𝓢 ⊢! f) : 𝓢 ⊢ f :=
  Classical.choice h

lemma provableSet_iff {𝓢 : S} {s : Set F} :
    𝓢 ⊢!* s ↔ Nonempty (𝓢 ⊢* s) := by
  simp [ProvableSet, PrfSet, Provable, Classical.nonempty_pi, ←imp_iff_not_or]

noncomputable def ProvableSet.get {𝓢 : S} {s : Set F} (h : 𝓢 ⊢!* s) : 𝓢 ⊢* s :=
  Classical.choice (α := 𝓢 ⊢* s) (provableSet_iff.mp h : Nonempty (𝓢 ⊢* s))

def WeakerThan (𝓢 : S) (𝓣 : T) : Prop := theory 𝓢 ⊆ theory 𝓣

infix:40 " ≤ₛ " => WeakerThan

def StrictlyWeakerThan (𝓢 : S) (𝓣 : T) : Prop := 𝓢 ≤ₛ 𝓣 ∧ ¬𝓣 ≤ₛ 𝓢

infix:40 " <ₛ " => StrictlyWeakerThan

def Equiv (𝓢 : S) (𝓣 : T) : Prop := theory 𝓢 = theory 𝓣

infix:40 " =ₛ " => Equiv

section

variable {𝓢 : S} {𝓣 : T} {𝓤 : U}

@[simp, refl] protected lemma WeakerThan.refl (𝓢 : S) : 𝓢 ≤ₛ 𝓢 := Set.Subset.refl _

@[trans] lemma WeakerThan.trans : 𝓢 ≤ₛ 𝓣 → 𝓣 ≤ₛ 𝓤 → 𝓢 ≤ₛ 𝓤 := Set.Subset.trans

lemma weakerThan_iff : 𝓢 ≤ₛ 𝓣 ↔ (∀ {f}, 𝓢 ⊢! f → 𝓣 ⊢! f) :=
  ⟨fun h _ hf ↦ h hf, fun h _ hf ↦ h hf⟩

lemma not_weakerThan_iff : ¬𝓢 ≤ₛ 𝓣 ↔ (∃ f, 𝓢 ⊢! f ∧ 𝓣 ⊬ f) := by simp [weakerThan_iff, Unprovable];

lemma strictlyWeakerThan_iff : 𝓢 <ₛ 𝓣 ↔ (∀ {f}, 𝓢 ⊢! f → 𝓣 ⊢! f) ∧ (∃ f, 𝓢 ⊬ f ∧ 𝓣 ⊢! f) := by
  simp [StrictlyWeakerThan, weakerThan_iff]; intro _
  exact exists_congr (fun _ ↦ by simp [and_comm])

@[trans]
lemma strictlyWeakerThan.trans : 𝓢 <ₛ 𝓣 → 𝓣 <ₛ 𝓤 → 𝓢 <ₛ 𝓤 := by
  rintro ⟨h₁, nh₁⟩ ⟨h₂, _⟩;
  constructor;
  . exact WeakerThan.trans h₁ h₂;
  . apply not_weakerThan_iff.mpr;
    obtain ⟨f, hf₁, hf₂⟩ := not_weakerThan_iff.mp nh₁;
    use f;
    constructor;
    . apply weakerThan_iff.mp h₂;
      assumption;
    . assumption;

lemma weakening (h : 𝓢 ≤ₛ 𝓣) {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := weakerThan_iff.mp h

lemma Equiv.iff : 𝓢 =ₛ 𝓣 ↔ (∀ f, 𝓢 ⊢! f ↔ 𝓣 ⊢! f) := by simp [Equiv, Set.ext_iff, theory]

@[simp, refl] protected lemma Equiv.refl (𝓢 : S) : 𝓢 =ₛ 𝓢 := rfl

@[symm] lemma Equiv.symm : 𝓢 =ₛ 𝓣 → 𝓣 =ₛ 𝓢 := Eq.symm

@[trans] lemma Equiv.trans : 𝓢 =ₛ 𝓣 → 𝓣 =ₛ 𝓤 → 𝓢 =ₛ 𝓤 := Eq.trans

lemma Equiv.antisymm_iff : 𝓢 =ₛ 𝓣 ↔ 𝓢 ≤ₛ 𝓣 ∧ 𝓣 ≤ₛ 𝓢 := Set.Subset.antisymm_iff

alias ⟨_, Equiv.antisymm⟩ := Equiv.antisymm_iff

lemma Equiv.le : 𝓢 =ₛ 𝓣 → 𝓢 ≤ₛ 𝓣 := by simp [Equiv, WeakerThan]; intro e; rw [e]

end

variable (S)

instance equiv : Setoid S where
  r := (· =ₛ ·)
  iseqv := { refl := fun _ ↦ rfl, symm := Eq.symm, trans := Eq.trans }

abbrev Logic := Quotient (equiv S)

variable {S}

lemma equiv_def {𝓢 𝓣 : S} : 𝓢 ≈ 𝓣 ↔ theory 𝓢 = theory 𝓣 := iff_of_eq rfl

namespace Logic

@[simp] lemma of_eq_of {𝓢 𝓣 : S} : (⟦𝓢⟧ : Logic S) = ⟦𝓣⟧ ↔ 𝓢 ≈ 𝓣 := Quotient.eq

instance : LE (Logic S) :=
  ⟨Quotient.lift₂ (· ≤ₛ ·) (fun 𝓢₁ 𝓣₁ 𝓢₂ 𝓣₂ h𝓢 h𝓣 ↦ by simp [WeakerThan, equiv_def.mp h𝓢, equiv_def.mp h𝓣])⟩

@[simp] lemma le_iff {𝓢 𝓣 : S} : (⟦𝓢⟧ : Logic S) ≤ ⟦𝓣⟧ ↔ 𝓢 ≤ₛ 𝓣 := iff_of_eq rfl

instance : PartialOrder (Logic S) where
  le_refl := fun Λ ↦ by induction Λ using Quotient.ind; simp
  le_trans := fun Λ₁ Λ₂ Λ₃ ↦ by
    induction Λ₁ using Quotient.ind
    induction Λ₂ using Quotient.ind
    induction Λ₃ using Quotient.ind
    simp; exact WeakerThan.trans
  le_antisymm := fun Λ₁ Λ₂ ↦ by
    induction Λ₁ using Quotient.ind
    induction Λ₂ using Quotient.ind
    simp; exact le_antisymm

@[simp] lemma lt_iff {𝓢 𝓣 : S} : (⟦𝓢⟧ : Logic S) < ⟦𝓣⟧ ↔ 𝓢 <ₛ 𝓣 := iff_of_eq rfl

end Logic

@[simp] lemma provableSet_theory (𝓢 : S) : 𝓢 ⊢!* theory 𝓢 := fun hf ↦ hf

def Inconsistent (𝓢 : S) : Prop := ∀ f, 𝓢 ⊢! f

class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢

lemma inconsistent_def {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∀ f, 𝓢 ⊢! f := by simp [Inconsistent]

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
    Consistent 𝓢 ↔ ∃ f, 𝓢 ⊬ f := by
  simp [←not_inconsistent_iff_consistent, inconsistent_def]

alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable

lemma Consistent.of_unprovable {𝓢 : S} {f} (h : 𝓢 ⊬ f) : Consistent 𝓢 :=
  ⟨fun hp ↦ h (hp f)⟩

lemma inconsistent_iff_theory_eq_univ {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by simp [inconsistent_def, theory, Set.ext_iff]

alias ⟨Inconsistent.theory_eq, _⟩ := inconsistent_iff_theory_eq_univ

lemma Inconsistent.equiv {𝓢 𝓣 : S} (h : Inconsistent 𝓢) (h' : Inconsistent 𝓣) : 𝓢 ≈ 𝓣 :=
  Set.ext fun f ↦ by simp [h.theory_eq, h'.theory_eq]

lemma Inconsistent.of_ge {𝓢 : S} {𝓣 : T} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ≤ₛ 𝓣) : Inconsistent 𝓣 :=
  fun f ↦ h (h𝓢 f)

lemma Consistent.of_le {𝓢 : S} {𝓣 : T} (h𝓢 : Consistent 𝓢) (h : 𝓣 ≤ₛ 𝓢) : Consistent 𝓣 :=
  ⟨fun H ↦ not_consistent_iff_inconsistent.mpr (H.of_ge h) h𝓢⟩

namespace Logic

protected def Inconsistent (Λ : Logic S) : Prop :=
  Quotient.lift Inconsistent (fun 𝓢 𝓣 h ↦ by simp [inconsistent_iff_theory_eq, equiv_def.mp h]) Λ

@[simp] lemma inconsistent_mk (𝓢 : S) : Logic.Inconsistent (⟦𝓢⟧ : Logic S) ↔ Inconsistent 𝓢 := iff_of_eq rfl

protected def Consistent (Λ : Logic S) : Prop :=
  Quotient.lift Consistent (fun 𝓢 𝓣 h ↦ by simp [←not_inconsistent_iff_consistent, inconsistent_iff_theory_eq, equiv_def.mp h]) Λ

@[simp] lemma consistent_mk (𝓢 : S) : Logic.Consistent (⟦𝓢⟧ : Logic S) ↔ Consistent 𝓢 := iff_of_eq rfl

end Logic

@[ext] structure Translation {S S' F F'} [System F S] [System F' S'] (𝓢 : S) (𝓣 : S') where
  toFun : F → F'
  prf {f} : 𝓢 ⊢ f → 𝓣 ⊢ toFun f

infix:40 " ↝ " => Translation

@[ext] structure Bitranslation {S S' F F'} [System F S] [System F' S'] (𝓢 : S) (𝓣 : S') where
  r : 𝓢 ↝ 𝓣
  l : 𝓣 ↝ 𝓢
  r_l : r.toFun ∘ l.toFun = id
  l_r : l.toFun ∘ r.toFun = id

infix:40 " ↭ " => Bitranslation

@[ext] structure FaithfulTranslation {S S' F F'} [System F S] [System F' S'] (𝓢 : S) (𝓣 : S') extends 𝓢 ↝ 𝓣 where
  prfInv {f} : 𝓣 ⊢ toFun f → 𝓢 ⊢ f

infix:40 " ↝¹ " => FaithfulTranslation

namespace Translation

variable {S S' S'' : Type*} {F F' F'' : Type*} [System F S] [System F' S'] [System F'' S'']

instance (𝓢 : S) (𝓣 : S') : CoeFun (𝓢 ↝ 𝓣) (fun _ ↦ F → F') := ⟨Translation.toFun⟩

protected def id (𝓢 : S) : 𝓢 ↝ 𝓢 where
  toFun := id
  prf := id

@[simp] lemma id_app (𝓢 : S) (f : F) : Translation.id 𝓢 f = f := rfl

def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝ 𝓤) (ψ : 𝓢 ↝ 𝓣) : 𝓢 ↝ 𝓤 where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf

@[simp] lemma comp_app {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝ 𝓤) (ψ : 𝓢 ↝ 𝓣) (f : F) :
    φ.comp ψ f = φ (ψ f) := rfl

lemma provable {𝓢 : S} {𝓣 : S'} (φ : 𝓢 ↝ 𝓣) {p} (h : 𝓢 ⊢! p) : 𝓣 ⊢! φ p := ⟨φ.prf h.get⟩

end Translation

namespace Bitranslation

variable {S S' S'' : Type*} {F F' F'' : Type*} [System F S] [System F' S'] [System F'' S'']

@[simp] lemma r_l_app {𝓢 : S} {𝓣 : S'} (φ : 𝓢 ↭ 𝓣) (p : F') : φ.r (φ.l p) = p := congr_fun φ.r_l p

@[simp] lemma l_r_app {𝓢 : S} {𝓣 : S'} (φ : 𝓢 ↭ 𝓣) (p : F) : φ.l (φ.r p) = p := congr_fun φ.l_r p

protected def id (𝓢 : S) : 𝓢 ↭ 𝓢 where
  r := Translation.id 𝓢
  l := Translation.id 𝓢
  r_l := by ext; simp
  l_r := by ext; simp

protected def symm {𝓢 : S} {𝓣 : S'} (φ : 𝓢 ↭ 𝓣) : 𝓣 ↭ 𝓢 where
  r := φ.l
  l := φ.r
  r_l := φ.l_r
  l_r := φ.r_l

def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↭ 𝓤) (ψ : 𝓢 ↭ 𝓣) : 𝓢 ↭ 𝓤 where
  r := φ.r.comp ψ.r
  l := ψ.l.comp φ.l
  r_l := by ext; simp
  l_r := by ext; simp

end Bitranslation

namespace FaithfulTranslation

variable {S S' S'' : Type*} {F F' F'' : Type*} [System F S] [System F' S'] [System F'' S'']

instance (𝓢 : S) (𝓣 : S') : CoeFun (𝓢 ↝¹ 𝓣) (fun _ ↦ F → F') := ⟨fun t ↦ t.toFun⟩

protected def id (𝓢 : S) : 𝓢 ↝¹ 𝓢 where
  toFun := id
  prf := id
  prfInv := id

@[simp] lemma id_app (𝓢 : S) (f : F) : FaithfulTranslation.id 𝓢 f = f := rfl

def comp {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝¹ 𝓤) (ψ : 𝓢 ↝¹ 𝓣) : 𝓢 ↝¹ 𝓤 where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf
  prfInv := ψ.prfInv ∘ φ.prfInv

@[simp] lemma comp_app {𝓢 : S} {𝓣 : S'} {𝓤 : S''} (φ : 𝓣 ↝¹ 𝓤) (ψ : 𝓢 ↝¹ 𝓣) (f : F) :
    φ.comp ψ f = φ (ψ f) := rfl

lemma provable {𝓢 : S} {𝓣 : S'} (φ : 𝓢 ↝¹ 𝓣) {p} (h : 𝓢 ⊢! p) : 𝓣 ⊢! φ p := ⟨φ.prf h.get⟩

lemma provable_iff {𝓢 : S} {𝓣 : S'} (φ : 𝓢 ↝¹ 𝓣) {p} : 𝓣 ⊢! φ p ↔ 𝓢 ⊢! p :=
  ⟨fun h ↦ ⟨φ.prfInv h.get⟩, fun h ↦ ⟨φ.prf h.get⟩⟩

end FaithfulTranslation

class Subtheory (𝓢 𝓣 : S) where
  prf {f} : 𝓢 ⊢ f → 𝓣 ⊢ f

infix:40 " ≼ " => Subtheory

namespace Subtheory

variable {𝓢 𝓣 𝓤 : S}

protected instance id : 𝓢 ≼ 𝓢 := ⟨id⟩

def comp (t' : 𝓣 ≼ 𝓤) (t : 𝓢 ≼ 𝓣) : 𝓢 ≼ 𝓤 := ⟨t'.prf ∘ t.prf⟩

def translation [𝓢 ≼ 𝓣] : 𝓢 ↝ 𝓣 where
  toFun := id
  prf := prf

def ofTranslation (t : 𝓢 ↝ 𝓣) (h : ∀ p, t p = p) : 𝓢 ≼ 𝓣 := ⟨fun {p} b ↦ h p ▸ (t.prf b)⟩

lemma prf! [𝓢 ≼ 𝓣] {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := λ ⟨p⟩ ↦ ⟨Subtheory.prf p⟩

end Subtheory

section

variable [LogicalConnective F]

variable (𝓢 : S)

def Complete : Prop := ∀ f, 𝓢 ⊢! f ∨ 𝓢 ⊢! ∼f

def Undecidable (f : F) : Prop := 𝓢 ⊬ f ∧ 𝓢 ⊬ ∼f

end

lemma incomplete_iff_exists_undecidable [LogicalConnective F] {𝓢 : S} :
    ¬System.Complete 𝓢 ↔ ∃ f, Undecidable 𝓢 f := by simp [Complete, Undecidable, not_or]

variable (S T)

class Axiomatized [Collection F S] where
  prfAxm {𝓢 : S} : 𝓢 ⊢* Collection.set 𝓢
  weakening {𝓢 𝓣 : S} : 𝓢 ⊆ 𝓣 → 𝓢 ⊢ f → 𝓣 ⊢ f

alias byAxm := Axiomatized.prfAxm
alias wk := Axiomatized.weakening

class StrongCut [Collection F T] where
  cut {𝓢 : S} {𝓣 : T} {p} : 𝓢 ⊢* Collection.set 𝓣 → 𝓣 ⊢ p → 𝓢 ⊢ p

variable {S T}

section Axiomatized

namespace Axiomatized

variable [Collection F S] [Axiomatized S] {𝓢 𝓣 : S}

@[simp] lemma provable_axm (𝓢 : S) : 𝓢 ⊢!* Collection.set 𝓢 := fun hf ↦ ⟨prfAxm hf⟩

lemma axm_subset (𝓢 : S) : Collection.set 𝓢 ⊆ theory 𝓢 := fun _ hp ↦ provable_axm 𝓢 hp

lemma le_of_subset (h : 𝓢 ⊆ 𝓣) : 𝓢 ≤ₛ 𝓣 := by rintro f ⟨b⟩; exact ⟨weakening h b⟩

lemma weakening! (h : 𝓢 ⊆ 𝓣) {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := by rintro ⟨b⟩; exact ⟨weakening h b⟩

def subtheoryOfSubset (h : 𝓢 ⊆ 𝓣) : 𝓢 ≼ 𝓣 := ⟨weakening h⟩

def translation (h : 𝓢 ⊆ 𝓣) : 𝓢 ↝ 𝓣 where
  toFun := id
  prf := weakening h

end Axiomatized

alias by_axm := Axiomatized.provable_axm
alias wk! := Axiomatized.weakening!

variable [Collection F S] [Collection F T] [Axiomatized S]

def FiniteAxiomatizable (𝓢 : S) : Prop := ∃ 𝓕 : S, Collection.Finite 𝓕 ∧ 𝓕 ≈ 𝓢

lemma Consistent.of_subset {𝓢 𝓣 : S} (h𝓢 : Consistent 𝓢) (h : 𝓣 ⊆ 𝓢) : Consistent 𝓣 :=
  h𝓢.of_le (Axiomatized.le_of_subset h)

lemma Inconsistent.of_supset {𝓢 𝓣 : S} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⊆ 𝓣) : Inconsistent 𝓣 :=
  h𝓢.of_ge (Axiomatized.le_of_subset h)

namespace StrongCut

variable [StrongCut S T]

lemma cut! {𝓢 : S} {𝓣 : T} {p : F} (H : 𝓢 ⊢!* Collection.set 𝓣) (hp : 𝓣 ⊢! p) : 𝓢 ⊢! p := by
  rcases hp with ⟨b⟩; exact ⟨StrongCut.cut H.get b⟩

def translation {𝓢 : S} {𝓣 : T} (B : 𝓢 ⊢* Collection.set 𝓣) : 𝓣 ↝ 𝓢 where
  toFun := id
  prf := StrongCut.cut B

end StrongCut

def Subtheory.ofAxm [StrongCut S S] {𝓢₁ 𝓢₂ : S} (B : 𝓢₂ ⊢* Collection.set 𝓢₁) : 𝓢₁ ≼ 𝓢₂ := ⟨fun b ↦ StrongCut.cut B b⟩

noncomputable def Subtheory.ofAxm! [StrongCut S S] {𝓢₁ 𝓢₂ : S} (B : 𝓢₂ ⊢!* Collection.set 𝓢₁) : 𝓢₁ ≼ 𝓢₂ := ⟨fun b ↦ StrongCut.cut B.get b⟩

def Subtheory.ofSubset {𝓢 𝓣 : S} (h : 𝓢 ⊆ 𝓣) : 𝓢 ≼ 𝓣 := ⟨wk h⟩

variable (S)

class Compact where
  φ {𝓢 : S} {f : F} : 𝓢 ⊢ f → S
  φPrf {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : φ b ⊢ f
  φ_subset {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : φ b ⊆ 𝓢
  φ_finite {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : Collection.Finite (φ b)

variable {S}

namespace Compact

variable [Compact S]

lemma finite_provable {𝓢 : S} (h : 𝓢 ⊢! f) : ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ Collection.Finite 𝓕 ∧ 𝓕 ⊢! f := by
  rcases h with ⟨b⟩
  exact ⟨φ b, φ_subset b, φ_finite b, ⟨φPrf b⟩⟩

end Compact

end Axiomatized

end System

namespace System

variable {S : Type*} {F : Type*} [LogicalConnective F] [System F S]

variable (S)

class DeductiveExplosion where
  dexp {𝓢 : S} : 𝓢 ⊢ ⊥ → (p : F) → 𝓢 ⊢ p

variable {S}

section

variable [DeductiveExplosion S]

def DeductiveExplosion.dexp! {𝓢 : S} (h : 𝓢 ⊢! ⊥) (f : F) : 𝓢 ⊢! f := by
  rcases h with ⟨b⟩; exact ⟨dexp b f⟩

lemma inconsistent_iff_provable_bot {𝓢 : S} :
    Inconsistent 𝓢 ↔ 𝓢 ⊢! ⊥ := ⟨fun h ↦ h ⊥, fun h f ↦ DeductiveExplosion.dexp! h f⟩

alias ⟨_, inconsistent_of_provable⟩ := inconsistent_iff_provable_bot

lemma consistent_iff_unprovable_bot {𝓢 : S} :
    Consistent 𝓢 ↔ 𝓢 ⊬ ⊥ := by
  simp [inconsistent_iff_provable_bot, ←not_inconsistent_iff_consistent]

alias ⟨Consistent.not_bot, _⟩ := consistent_iff_unprovable_bot

variable [Collection F S] [Axiomatized S] [Compact S]

lemma inconsistent_compact {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∃ 𝓕 : S, 𝓕 ⊆ 𝓢 ∧ Collection.Finite 𝓕 ∧ Inconsistent 𝓕 :=
  ⟨fun H ↦ by rcases Compact.finite_provable (H ⊥) with ⟨𝓕, h𝓕, fin, h⟩; exact ⟨𝓕, h𝓕, fin, inconsistent_of_provable h⟩, by
    rintro ⟨𝓕, h𝓕, _, H⟩; exact H.of_supset h𝓕⟩

lemma consistent_compact {𝓢 : S} :
    Consistent 𝓢 ↔ ∀ 𝓕 : S, 𝓕 ⊆ 𝓢 → Collection.Finite 𝓕 → Consistent 𝓕 := by
  simp [←not_inconsistent_iff_consistent, inconsistent_compact (𝓢 := 𝓢)]

end

variable (S)

class Deduction [Cons F S] where
  ofInsert {p q : F} {𝓢 : S} : cons p 𝓢 ⊢ q → 𝓢 ⊢ p ➝ q
  inv {p q : F} {𝓢 : S} : 𝓢 ⊢ p ➝ q → cons p 𝓢 ⊢ q

variable {S}

section deduction

variable [Cons F S] [Deduction S] {𝓢 : S} {p q : F}

alias deduction := Deduction.ofInsert

lemma Deduction.of_insert! (h : cons p 𝓢 ⊢! q) : 𝓢 ⊢! p ➝ q := by
  rcases h with ⟨b⟩; exact ⟨Deduction.ofInsert b⟩

alias deduction! := Deduction.of_insert!

lemma Deduction.inv! (h : 𝓢 ⊢! p ➝ q) : cons p 𝓢 ⊢! q := by
  rcases h with ⟨b⟩; exact ⟨Deduction.inv b⟩

def Deduction.translation (p : F) (𝓢 : S) : cons p 𝓢 ↝ 𝓢 where
  toFun := fun q ↦ p ➝ q
  prf := deduction

lemma deduction_iff : cons p 𝓢 ⊢! q ↔ 𝓢 ⊢! p ➝ q := ⟨deduction!, Deduction.inv!⟩

end deduction

end System

section

variable {S : Type*} {F : Type*} [LogicalConnective F] [System F S] {M : Type*} [Semantics F M]

class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {f : F}, 𝓢 ⊢! f → 𝓜 ⊧ f

class Complete (𝓢 : S) (𝓜 : M) : Prop where
  complete : ∀ {f : F}, 𝓜 ⊧ f → 𝓢 ⊢! f

namespace Sound

section

variable {𝓢 𝓣 : S} {𝓜 𝓝 : M} [Sound 𝓢 𝓜] [Sound 𝓣 𝓝]

lemma not_provable_of_countermodel {p : F} (hp : ¬𝓜 ⊧ p) : 𝓢 ⊬ p :=
  fun b ↦ hp (Sound.sound b)

lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → System.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨f, hf⟩; exact hf (Sound.sound (h f))⟩

lemma consistent_of_model [Semantics.Bot M] : System.Consistent 𝓢 :=
  consistent_of_meaningful (𝓜 := 𝓜) inferInstance

lemma realizeSet_of_prfSet {T : Set F} (b : 𝓢 ⊢!* T) : 𝓜 ⊧* T :=
  ⟨fun _ hf => sound (b hf)⟩

end

section

variable [∀ 𝓜 : M, Semantics.Meaningful 𝓜] {𝓢 : S} {T : Set F} [Sound 𝓢 (Semantics.models M T)]

lemma consequence_of_provable {f : F} : 𝓢 ⊢! f → T ⊨[M] f := sound

lemma consistent_of_satisfiable : Semantics.Satisfiable M T → System.Consistent 𝓢 :=
  fun H ↦ consistent_of_meaningful (Semantics.meaningful_iff_satisfiableSet.mp H)

end

end Sound

namespace Complete

section

variable {𝓢 : S} {𝓜 : M} [Complete 𝓢 𝓜]

lemma meaningful_of_consistent : System.Consistent 𝓢 → Semantics.Meaningful 𝓜 := by
  contrapose; intro h
  simp [Semantics.not_meaningful_iff, System.not_consistent_iff_inconsistent] at h ⊢
  intro f; exact Complete.complete (h f)

end

section

variable [∀ 𝓜 : M, Semantics.Meaningful 𝓜] {𝓢 : S} {T : Set F} [Complete 𝓢 (Semantics.models M T)]

lemma provable_of_consequence {f : F} : T ⊨[M] f → 𝓢 ⊢! f := complete

lemma satisfiable_of_consistent : System.Consistent 𝓢 → Semantics.Satisfiable M T :=
  fun H ↦ Semantics.meaningful_iff_satisfiableSet.mpr (meaningful_of_consistent H)

lemma inconsistent_of_unsatisfiable : ¬Semantics.Satisfiable M T → System.Inconsistent 𝓢 := by
  contrapose; simpa [←System.not_consistent_iff_inconsistent] using satisfiable_of_consistent

variable [Sound 𝓢 (Semantics.models M T)]

lemma provable_iff_consequence {f : F} : T ⊨[M] f ↔ 𝓢 ⊢! f := ⟨complete, Sound.sound⟩

lemma consistent_iff_satisfiable : System.Consistent 𝓢 ↔ Semantics.Satisfiable M T :=
  ⟨satisfiable_of_consistent, Sound.consistent_of_satisfiable⟩

end

end Complete

end

end LO
