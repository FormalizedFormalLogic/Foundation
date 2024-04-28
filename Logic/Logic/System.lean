import Logic.Logic.LogicSymbol
import Logic.Logic.Semantics
/-!
# Basic definitions and properties of proof system related notions

This file defines a characterization of the system/proof/provability/calculus of formulas.
Also defines soundness and completeness.

## Main Definitions
* `LO.System`: Proof system of logic.
* `LO.System.Inconsistent`
* `LO.System.Consistent`
* `LO.System.Translation`
* `LO.System.Compact`
* `LO.Sound`: Soundness of the proof system.
* `LO.Complete`: Completeness of the proof system.

-/

namespace LO

class System (S : Type*) (F : outParam Type*) where
  Prf : S → F → Type*

infix:45 " ⊢ " => System.Prf

namespace System

variable {S : Type*} {F : Type*} [System S F]

section

variable (𝓢 : S)

def Provable (f : F) : Prop := Nonempty (𝓢 ⊢ f)

abbrev Unprovable (f : F) : Prop := ¬Provable 𝓢 f

infix:45 " ⊢! " => Provable

infix:45 " ⊬! " => Unprovable

def PrfSet (s : Set F) : Type _ := {f : F} → f ∈ s → 𝓢 ⊢ f

def ProvableSet (s : Set F) : Prop := ∀ f ∈ s, 𝓢 ⊢! f

infix:45 " ⊢* " => PrfSet

infix:45 " ⊢*! " => ProvableSet

def theory : Set F := {f | 𝓢 ⊢! f}

end

lemma unprovable_iff_isEmpty {𝓢 : S} {f : F} :
    𝓢 ⊬! f ↔ IsEmpty (𝓢 ⊢ f) := by simp [Provable, Unprovable]

noncomputable def Provable.prf {𝓢 : S} {f : F} (h : 𝓢 ⊢! f) : 𝓢 ⊢ f :=
  Classical.choice h

lemma provableSet_iff {𝓢 : S} {s : Set F} :
    𝓢 ⊢*! s ↔ Nonempty (𝓢 ⊢* s) := by
  simp [ProvableSet, PrfSet, Provable, Classical.nonempty_pi, ←imp_iff_not_or]

noncomputable def ProvableSet.prfSet {𝓢 : S} {s : Set F} (h : 𝓢 ⊢*! s) : 𝓢 ⊢* s :=
  Classical.choice (α := 𝓢 ⊢* s) (provableSet_iff.mp h : Nonempty (𝓢 ⊢* s))

instance : Preorder S where
  le := fun 𝓢 𝓢' ↦ theory 𝓢 ⊆ theory 𝓢'
  le_refl := fun 𝓢 ↦ Set.Subset.refl _
  le_trans := fun _ _ _ h₁ h₂ ↦ Set.Subset.trans h₁ h₂

lemma le_iff {𝓢 𝓢' : S} : 𝓢 ≤ 𝓢' ↔ (∀ {f}, 𝓢 ⊢! f → 𝓢' ⊢! f) :=
  ⟨fun h _ hf ↦ h hf, fun h _ hf ↦ h hf⟩

lemma lt_iff {𝓢 𝓢' : S} : 𝓢 < 𝓢' ↔ (∀ {f}, 𝓢 ⊢! f → 𝓢' ⊢! f) ∧ (∃ f, 𝓢 ⊬! f ∧ 𝓢' ⊢! f) := by
  simp [lt_iff_le_not_le, le_iff]; intro _
  exact exists_congr (fun _ ↦ by simp [and_comm])

lemma weakening {𝓢 𝓢' : S} (h : 𝓢 ≤ 𝓢') {f} : 𝓢 ⊢! f → 𝓢' ⊢! f := le_iff.mp h

instance : Setoid S where
  r := fun 𝓢 𝓢' ↦ theory 𝓢 = theory 𝓢'
  iseqv := { refl := fun _ ↦ rfl, symm := Eq.symm, trans := Eq.trans }

lemma equiv_def {𝓢 𝓢' : S} : 𝓢 ≈ 𝓢' ↔ theory 𝓢 = theory 𝓢' := iff_of_eq rfl

lemma equiv_iff {𝓢 𝓢' : S} : 𝓢 ≈ 𝓢' ↔ (∀ f, 𝓢 ⊢! f ↔ 𝓢' ⊢! f) := by simp [equiv_def, Set.ext_iff, theory]

lemma le_antisymm {𝓢 𝓢' : S} (h : 𝓢 ≤ 𝓢') (h' : 𝓢' ≤ 𝓢) : 𝓢 ≈ 𝓢' :=
  equiv_iff.mpr (fun _ ↦ ⟨fun hf ↦ le_iff.mp h hf, fun hf ↦ le_iff.mp h' hf⟩)

@[simp] lemma provableSet_theory (𝓢 : S) : 𝓢 ⊢*! theory 𝓢 := fun _ hf ↦ hf

def Inconsistent (𝓢 : S) : Prop := ∀ f, 𝓢 ⊢! f

class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢

lemma inconsistent_def {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∀ f, 𝓢 ⊢! f := by simp [Inconsistent]

lemma not_inconsistent_iff_consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩

alias ⟨_, Consistent.not_inc⟩ := not_inconsistent_iff_consistent

lemma not_consistent_iff_inconsistent {𝓢 : S} :
    ¬Consistent 𝓢 ↔ Inconsistent 𝓢 := by simp [←not_inconsistent_iff_consistent]

alias ⟨_, Inconsistent.not_con⟩ := not_consistent_iff_inconsistent

lemma consistent_iff_exists_unprovable {𝓢 : S} :
    Consistent 𝓢 ↔ ∃ f, 𝓢 ⊬! f := by
  simp [←not_inconsistent_iff_consistent, inconsistent_def]

alias ⟨Consistent.exists_unprovable, _⟩ := consistent_iff_exists_unprovable

lemma Consistent.of_unprovable {𝓢 : S} {f} (h : 𝓢 ⊬! f) : Consistent 𝓢 :=
  ⟨fun hp ↦ h (hp f)⟩

lemma inconsistent_iff_theory_eq_univ {𝓢 : S} :
    Inconsistent 𝓢 ↔ theory 𝓢 = Set.univ := by simp [inconsistent_def, theory, Set.ext_iff]

alias ⟨Inconsistent.theory_eq, _⟩ := inconsistent_iff_theory_eq_univ

lemma Inconsistent.equiv {𝓢 𝓢' : S} (h : Inconsistent 𝓢) (h' : Inconsistent 𝓢') : 𝓢 ≈ 𝓢' :=
  Set.ext fun f ↦ by simp [h.theory_eq, h'.theory_eq]

lemma Inconsistent.of_ge {𝓢 𝓢' : S} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ≤ 𝓢') : Inconsistent 𝓢' :=
  fun f ↦ h (h𝓢 f)

lemma Consistent.of_le {𝓢 𝓢' : S} (h𝓢 : Consistent 𝓢) (h : 𝓢' ≤ 𝓢) : Consistent 𝓢' :=
  ⟨fun H ↦ not_consistent_iff_inconsistent.mpr (H.of_ge h) h𝓢⟩

structure Translation {S S' F F'} [System S F] [System S' F'] (𝓢 : S) (𝓢' : S') where
  toFun : F → F'
  prf {f} : 𝓢 ⊢ f → 𝓢' ⊢ toFun f

infix:40 " ↝ " => Translation

namespace Translation

variable {S S' S'' : Type*} {F F' F'' : Type*} [System S F] [System S' F'] [System S'' F'']

instance (𝓢 : S) (𝓢' : S') : CoeFun (Translation 𝓢 𝓢') (fun _ ↦ F → F') := ⟨Translation.toFun⟩

protected def id (𝓢 : S) : 𝓢 ↝ 𝓢 where
  toFun := id
  prf := id

@[simp] lemma id_app (𝓢 : S) (f : F) : Translation.id 𝓢 f = f := rfl

def comp {𝓢 : S} {𝓢' : S'} {𝓢'' : S''} (φ : 𝓢' ↝ 𝓢'') (ψ : 𝓢 ↝ 𝓢') : 𝓢 ↝ 𝓢'' where
  toFun := φ.toFun ∘ ψ.toFun
  prf := φ.prf ∘ ψ.prf

@[simp] lemma comp_app {𝓢 : S} {𝓢' : S'} {𝓢'' : S''} (φ : 𝓢' ↝ 𝓢'') (ψ : 𝓢 ↝ 𝓢') (f : F) :
    φ.comp ψ f = φ (ψ f) := rfl

end Translation

section

variable [LogicalConnective F]

variable (𝓢 : S)

def Complete : Prop := ∀ f, 𝓢 ⊢! f ∨ 𝓢 ⊢! ~f

def Undecidable (f : F) : Prop := 𝓢 ⊬! f ∧ 𝓢 ⊬! ~f

end

variable (S)

class Axiomatized where
  axm : S → Set F
  prfAxm (𝓢 : S) : 𝓢 ⊢* axm 𝓢
  weakening {𝓢 𝓢' : S} : axm 𝓢 ⊆ axm 𝓢' → 𝓢 ⊢ f → 𝓢' ⊢ f

class StrongCut [Axiomatized S] where
  cut {𝓢 𝓣 : S} {p} : 𝓢 ⊢* Axiomatized.axm 𝓣 → 𝓣 ⊢ p → 𝓢 ⊢ p

variable {S}

section Axiomatized

namespace Axiomatized

variable [Axiomatized S] {𝓢 𝓢' : S}

@[simp] lemma provable_axm (𝓢 : S) : 𝓢 ⊢*! axm 𝓢 := fun _ hf ↦ ⟨prfAxm 𝓢 hf⟩

lemma axm_subset (𝓢 : S) : axm 𝓢 ⊆ theory 𝓢 := fun p hp ↦ provable_axm 𝓢 p hp

abbrev AxmSubset (𝓢 𝓢' : S) : Prop := axm 𝓢 ⊆ axm 𝓢'

infix:45 " ⊆ₐₓ " => AxmSubset

lemma le_of_subset_axm (h : 𝓢 ⊆ₐₓ 𝓢') : 𝓢 ≤ 𝓢' := by rintro f ⟨b⟩; exact ⟨weakening h b⟩

end Axiomatized

variable [Axiomatized S]

abbrev Finite (𝓢 : S) : Prop := (Axiomatized.axm 𝓢).Finite

def FiniteAxiomatizable (𝓢 : S) : Prop := ∃ 𝓕 : S, Finite 𝓕 ∧ 𝓕 ≈ 𝓢

lemma Consistent.of_subset {𝓢 𝓢' : S} (h𝓢 : Consistent 𝓢) (h : 𝓢' ⊆ₐₓ 𝓢) : Consistent 𝓢' :=
  h𝓢.of_le (Axiomatized.le_of_subset_axm h)

lemma Inconsistent.of_supset {𝓢 𝓢' : S} (h𝓢 : Inconsistent 𝓢) (h : 𝓢 ⊆ₐₓ 𝓢') : Inconsistent 𝓢' :=
  h𝓢.of_ge (Axiomatized.le_of_subset_axm h)

namespace StrongCut

variable [StrongCut S]

lemma cut! {𝓢 𝓣 : S} {p : F} (H : 𝓢 ⊢*! Axiomatized.axm 𝓣) (hp : 𝓣 ⊢! p) : 𝓢 ⊢! p := by
  rcases hp with ⟨b⟩; exact ⟨StrongCut.cut H.prfSet b⟩

def translation {𝓢 𝓣 : S} (B : 𝓢 ⊢* Axiomatized.axm 𝓣) : 𝓣 ↝ 𝓢 where
  toFun := id
  prf := StrongCut.cut B

end StrongCut

variable (S)

class Compact where
  φ {𝓢 : S} {f : F} : 𝓢 ⊢ f → S
  φPrf {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : φ b ⊢ f
  φ_subset {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : φ b ⊆ₐₓ 𝓢
  φ_finite {𝓢 : S} {f : F} (b : 𝓢 ⊢ f) : Finite (φ b)

variable {S}

namespace Compact

variable [Compact S]

lemma finite_provable {𝓢 : S} (h : 𝓢 ⊢! f) : ∃ 𝓕 : S, 𝓕 ⊆ₐₓ 𝓢 ∧ Finite 𝓕 ∧ 𝓕 ⊢! f := by
  rcases h with ⟨b⟩
  exact ⟨φ b, φ_subset b, φ_finite b, ⟨φPrf b⟩⟩

end Compact

end Axiomatized

end System

section

variable {S : Type*} {F : Type*} [LogicalConnective F] [System S F] {M : Type*} [Semantics M F]

class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {f : F}, 𝓢 ⊢! f → 𝓜 ⊧ f

class Complete (𝓢 : S) (𝓜 : M) : Prop where
  complete : ∀ {f : F}, 𝓜 ⊧ f → 𝓢 ⊢! f

namespace Sound

section

variable {𝓢 : S} {𝓜 : M} [Sound 𝓢 𝓜]

lemma not_provable_of_countermodel {p : F} (hp : ¬𝓜 ⊧ p) : 𝓢 ⊬! p :=
  fun b ↦ hp (Sound.sound b)

lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → System.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨f, hf⟩; exact hf (Sound.sound (h f))⟩

lemma consistent_of_model [Semantics.Bot M] : System.Consistent 𝓢 :=
  consistent_of_meaningful (𝓜 := 𝓜) inferInstance

lemma realizeSet_of_prfSet {T : Set F} (b : 𝓢 ⊢*! T) : 𝓜 ⊧* T :=
  ⟨fun _ hf => sound (b _ hf)⟩

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

variable [Sound 𝓢 (Semantics.models M T)]

lemma provable_iff_consequence {f : F} : T ⊨[M] f ↔ 𝓢 ⊢! f := ⟨complete, Sound.sound⟩

lemma consistent_iff_satisfiable : System.Consistent 𝓢 ↔ Semantics.Satisfiable M T :=
  ⟨satisfiable_of_consistent, Sound.consistent_of_satisfiable⟩

end

end Complete

end

namespace System

variable {S : Type*} {F : Type*} [LogicalConnective F] [System S F]

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
    Consistent 𝓢 ↔ 𝓢 ⊬! ⊥ := by
  simp [inconsistent_iff_provable_bot, ←not_inconsistent_iff_consistent]

alias ⟨Consistent.not_bot, _⟩ := consistent_iff_unprovable_bot

variable [Axiomatized S] [Compact S]

lemma consistent_compact {𝓢 : S} :
    Consistent 𝓢 ↔ ∀ 𝓕 : S, 𝓕 ⊆ₐₓ 𝓢 → Finite 𝓕 → Consistent 𝓕 :=
  ⟨fun H 𝓕 h𝓕 _ ↦ H.of_subset h𝓕,
   fun H ↦ consistent_iff_unprovable_bot.mpr <| fun b ↦ by
      rcases Compact.finite_provable b with ⟨𝓕, fin, h𝓕, h⟩
      exact (H 𝓕 fin h𝓕).not_bot h⟩

lemma inconsistent_compact {𝓢 : S} :
    Inconsistent 𝓢 ↔ ∃ 𝓕 : S, 𝓕 ⊆ₐₓ 𝓢 ∧ Finite 𝓕 ∧ Inconsistent 𝓕 := by
  simp [←not_consistent_iff_inconsistent, consistent_compact (𝓢 := 𝓢)]
  tauto

end

variable (S)

class Deduction [Insert F S] where
  ofInsert {p q : F} {𝓢 : S} : insert p 𝓢 ⊢ q → 𝓢 ⊢ p ⟶ q
  inv {p q : F} {𝓢 : S} : 𝓢 ⊢ p ⟶ q → insert p 𝓢 ⊢ q

variable {S}

section

variable [Insert F S] [Deduction S]

alias deduction := Deduction.ofInsert

lemma Deduction.of_insert! {p q : F} {𝓢 : S} (h : insert p 𝓢 ⊢! q) : 𝓢 ⊢! p ⟶ q := by
  rcases h with ⟨b⟩; exact ⟨Deduction.ofInsert b⟩

alias deduction! := Deduction.of_insert!

lemma Deduction.inv! {p q : F} {𝓢 : S} (h : 𝓢 ⊢! p ⟶ q) : insert p 𝓢 ⊢! q := by
  rcases h with ⟨b⟩; exact ⟨Deduction.inv b⟩

end

end System

end LO
