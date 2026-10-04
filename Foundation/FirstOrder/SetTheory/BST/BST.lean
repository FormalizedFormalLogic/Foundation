module

public import Foundation.FirstOrder.SetTheory.BST.Basic
public import Foundation.FirstOrder.SetTheory.Basic.Model
public import Foundation.Vorspiel.ExistsUnique

/-!
# BasicSetTheory set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth" [Sch14]
-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗕𝗦𝗧]

/-! ## Axiom of extensionality -/

lemma mem_ext_iff {x y : V} : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y := by
  have := by
    simpa [models_iff, BasicSetTheory.extensionality] using
      Theory.models V 𝗕𝗦𝗧 BasicSetTheory.extensionality
  exact this x y

alias ⟨_, mem_ext⟩ := mem_ext_iff

attribute [ext] mem_ext

@[grind ->] lemma subset_antisymm {x y : V} (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y := by
  ext z; constructor
  · exact hxy z
  · exact hyx z

@[grind .] lemma subset_antisymm_iff {x y : V} : x ⊆ y ∧ y ⊆ x ↔ x = y := by aesop

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗕𝗦𝗧] in
lemma subset_of_eq {x y : V} (h : x = y) : x ⊆ y := h ▸ subset_refl x

lemma SSubset.iff {x y : V} : x ⊊ y ↔ x ⊆ y ∧ ∃ z ∈ y, z ∉ x := by
  constructor
  · rintro ⟨ss, eq⟩
    refine ⟨ss, ?_⟩
    contrapose eq
    push Not at *
    apply subset_antisymm ss eq
  · rintro ⟨ss, ⟨z, hzy, hzx⟩⟩
    refine ⟨ss, ?_⟩
    rintro rfl
    contradiction

lemma SSubset.exists_not_mem {x y : V} (hxy : x ⊊ y) : ∃ z ∈ y, z ∉ x := (SSubset.iff.mp hxy).2

lemma SSubset.of_subset_of_not_mem_of_mem {x y z : V} (ss : x ⊆ y) (hzx : z ∉ x) (hzy : z ∈ y) :
    x ⊊ y :=
  SSubset.iff.mpr ⟨ss, z, hzy, hzx⟩

/-! ## Axiom of empty set -/

lemma empty_exists : ∃ e : V, IsEmpty e := by
  simpa [models_iff] using! Theory.models V 𝗕𝗦𝗧 BasicSetTheory.empty_set

lemma empty_existsUnique : ∃! e : V, IsEmpty e := by
  rcases empty_exists (V := V) with ⟨e, he⟩
  apply ExistsUnique.intro e he
  intro x hx
  ext y
  simp [hx.not_mem, he.not_mem]

noncomputable scoped instance : EmptyCollection V := ⟨Classical.choose! empty_existsUnique⟩

noncomputable instance : Inhabited V := Inhabited.mk ∅

@[simp] lemma IsEmpty.empty : IsEmpty (∅ : V) := Classical.choose!_spec empty_existsUnique

@[simp] lemma not_mem_empty {x} : x ∉ (∅ : V) := IsEmpty.empty.not_mem

@[simp] lemma isEmpty_iff_eq_empty {x : V} :
    IsEmpty x ↔ x = ∅ := ⟨by intro h; ext; simp[h.not_mem], by rintro rfl; simp⟩

@[simp] lemma ne_empty_iff_isNonempty {x : V} :
    x ≠ ∅ ↔ IsNonempty x := by simp [←isEmpty_iff_eq_empty]

lemma eq_empty_or_isNonempty (x : V) : x = ∅ ∨ IsNonempty x := by
  by_cases hx : x = ∅
  · simp_all
  · right; exact ne_empty_iff_isNonempty.mp hx

@[simp] lemma empty_subset (x : V) : ∅ ⊆ x := by simp [subset_def]

@[simp] lemma subset_empty_iff_eq_empty {x : V} : x ⊆ ∅ ↔ x = ∅ := by simp [mem_ext_iff, subset_def]

/-! ## Axiom of pairing -/

lemma pairing_exists : ∀ x y : V, ∃ z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  simpa [models_iff, BasicSetTheory.pairing] using Theory.models V 𝗕𝗦𝗧 BasicSetTheory.pairing

lemma pairing_existsUnique (x y : V) : ∃! z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  rcases pairing_exists x y with ⟨p, hp⟩
  apply ExistsUnique.intro p hp
  intro q hq
  ext z; simp_all

noncomputable def doubleton (x y : V) : V := Classical.choose! (pairing_existsUnique x y)

@[simp] lemma mem_doubleton_iff {x y z : V} : z ∈ doubleton x y ↔ z = x ∨ z = y :=
  Classical.choose!_spec (pairing_existsUnique x y) z

def doubleton.dfn : SetTheorySemisentence 3 := “p x y. ∀ z, z ∈ p ↔ z = x ∨ z = y”

instance doubleton.defined : ℒₛₑₜ-function₂[V] doubleton via doubleton.dfn :=
  ⟨by intro v; simp [doubleton.dfn, doubleton]⟩

instance doubleton.definable : ℒₛₑₜ-function₂[V] doubleton := doubleton.defined.to_definable

@[simp] instance doubleton_isNonempty (x y : V) : IsNonempty (doubleton x y) := ⟨x, by simp⟩

noncomputable def singleton (x : V) : V := doubleton x x

noncomputable scoped instance : Singleton V V := ⟨singleton⟩

lemma singleton_def (x : V) : ({x} : V) = doubleton x x := rfl

@[simp] lemma mem_singleton_iff {x z : V} : z ∈ ({x} : V) ↔ z = x := by simp [singleton_def]

def singleton.dfn : SetTheorySemisentence 2 := “p x. !doubleton.dfn p x x”

instance singleton.defined : ℒₛₑₜ-function₁[V] Singleton.singleton via singleton.dfn :=
  ⟨by intro v; simp [singleton.dfn]; rfl⟩

instance singleton.definable : ℒₛₑₜ-function₁[V] Singleton.singleton :=
  singleton.defined.to_definable

@[simp] instance singleton_isNonempty (x : V) : IsNonempty ({x} : V) := ⟨x, by simp⟩

@[simp] lemma singleton_subset_iff_mem {x y : V} : {x} ⊆ y ↔ x ∈ y := by simp [subset_def]

@[simp] lemma singleton_ext_iff {x y : V} : ({x} : V) = {y} ↔ x = y := by
  simp [mem_ext_iff (x := {x})]

/-! ## Axiom of union -/

lemma union_exists : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := by
  simpa [models_iff, BasicSetTheory.union] using Theory.models V 𝗕𝗦𝗧 BasicSetTheory.union

lemma union_existsUnique (x : V) : ∃! y : V, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := by
  rcases union_exists x with ⟨u, hu⟩
  apply ExistsUnique.intro u hu
  intro v hv
  ext z; simp_all

noncomputable def sUnion (x : V) : V := Classical.choose! (union_existsUnique x)

prefix:110 "⋃ˢ " => sUnion

lemma mem_sUnion_iff {x z : V} : z ∈ ⋃ˢ x ↔ ∃ y ∈ x, z ∈ y :=
  Classical.choose!_spec (union_existsUnique x) z

def sUnion.dfn : SetTheorySemisentence 2 := “u x. ∀ z, z ∈ u ↔ ∃ w ∈ x, z ∈ w”

instance sUnion.defined : ℒₛₑₜ-function₁[V] sUnion via sUnion.dfn :=
  ⟨by intro v; simp [sUnion.dfn, mem_sUnion_iff, mem_ext_iff]⟩

instance sUnion.definable : ℒₛₑₜ-function₁[V] sUnion := sUnion.defined.to_definable

@[simp] lemma sUnion_empty_eq_empty : ⋃ˢ (∅ : V) = ∅ := by ext; simp [mem_sUnion_iff]

@[simp] lemma sUnion_singleton_eq (x : V) : ⋃ˢ ({x} : V) = x := by ext; simp [mem_sUnion_iff]

@[simp] lemma IsNonempty_sUnion_iff {x : V} : IsNonempty (⋃ˢ x) ↔ ∃ y ∈ x, IsNonempty y := by
  simp only [isNonempty_def, mem_sUnion_iff]
  grind

lemma subset_sUnion_of_mem {x y : V} (h : x ∈ y) : x ⊆ ⋃ˢ y := fun z hz ↦ by
  simp only [mem_sUnion_iff]; grind

/-! ### Union of two sets -/

noncomputable def union (x y : V) : V := ⋃ˢ (doubleton x y)

noncomputable scoped instance : Union V := ⟨union⟩

lemma union_def (x y : V) : x ∪ y = ⋃ˢ (doubleton x y) := rfl

def union.dfn : SetTheorySemisentence 3 := “u x y. ∀ d, !doubleton.dfn d x y → !sUnion.dfn u d”

instance union.defined : ℒₛₑₜ-function₂[V] Union.union via union.dfn :=
  ⟨by intro v; simp [union.dfn, union_def]⟩

instance union.definable : ℒₛₑₜ-function₂[V] Union.union := union.defined.to_definable

@[simp] lemma mem_union_iff {x y z : V} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by
  simp [union_def, mem_sUnion_iff]

@[simp] lemma union_self_eq (x : V) : x ∪ x = x := by ext; simp

lemma union_comm (x y : V) : x ∪ y = y ∪ x := by ext; simp; tauto

lemma union_assoc (x y z : V) : (x ∪ y) ∪ z = x ∪ (y ∪ z) := by ext; simp; tauto

@[simp] lemma union_empty (x : V) : x ∪ ∅ = x := by ext; simp

@[simp] lemma empty_union (x : V) : ∅ ∪ x = x := by ext; simp

@[simp] lemma IsNonempty_union_iff {x y : V} :
    IsNonempty (x ∪ y) ↔ IsNonempty x ∨ IsNonempty y := by
  simp only [isNonempty_def, mem_union_iff]; grind

@[simp] lemma subset_union_left (x y : V) : x ⊆ x ∪ y := fun z hz ↦ by simp [hz]

@[simp] lemma subset_union_right (x y : V) : y ⊆ x ∪ y := fun z hz ↦ by simp [hz]

@[simp] lemma union_eq_iff_right {x y : V} : x ∪ y = x ↔ y ⊆ x := by simp [mem_ext_iff, subset_def]

@[simp] lemma union_eq_iff_left {x y : V} : x ∪ y = y ↔ x ⊆ y := by simp [mem_ext_iff, subset_def]

/-! ### Insert -/

protected noncomputable def insert (x y : V) : V := {x} ∪ y

noncomputable scoped instance : Insert V V := ⟨SetTheory.insert⟩

lemma insert_def (x y : V) : insert x y = {x} ∪ y := rfl

def insert.dfn : SetTheorySemisentence 3 := “u x y. ∀ s, !singleton.dfn s x → !union.dfn u s y”

instance insert.defined : ℒₛₑₜ-function₂[V] insert via insert.dfn :=
  ⟨by intro v; simp [insert.dfn, insert_def]⟩

instance insert.definable : ℒₛₑₜ-function₂[V] insert := insert.defined.to_definable

@[simp] lemma mem_insert {x y z : V} : z ∈ insert x y ↔ z = x ∨ z ∈ y := by simp [insert_def]

@[simp] lemma insert_empty_eq (x : V) : (insert x ∅ : V) = {x} := by ext; simp

lemma union_insert (x y z : V) : x ∪ insert y z = insert y (x ∪ z) := by ext; simp; tauto

lemma pair_eq_doubleton (x y : V) : {x, y} = doubleton x y := by ext; simp

@[simp] lemma sUnion_insert (x y : V) : ⋃ˢ insert x y = x ∪ ⋃ˢ y := by ext; simp [mem_sUnion_iff]

@[simp] lemma subset_insert (x y : V) : y ⊆ insert x y := by simp [insert_def]

@[simp] instance insert_isNonempty (x y : V) : IsNonempty (insert x y) := ⟨x, by simp⟩

@[simp] lemma intsert_union (x y z : V) :
    insert x y ∪ z = insert x (y ∪ z) := by
  ext; simp only [mem_union_iff, mem_insert]; grind

@[simp] lemma singleton_inter (x y : V) :
    {x} ∪ y = insert x y := by
  ext; simp

@[simp, grind =] lemma insert_eq_self_of_mem {x y : V} (hx : x ∈ y) : insert x y = y := by
  ext; simp only [mem_insert, or_iff_right_iff_imp]; grind

/-! ## Axiom of power set -/

lemma power_exists : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ z ⊆ x := by
  simpa [models_iff, BasicSetTheory.power_set] using Theory.models V 𝗕𝗦𝗧 BasicSetTheory.power_set

lemma power_existsUnique (x : V) : ∃! y : V, ∀ z, z ∈ y ↔ z ⊆ x := by
  rcases power_exists x with ⟨p, hp⟩
  apply ExistsUnique.intro p hp
  intro q hq
  ext; simp_all

noncomputable def power (x : V) : V := Classical.choose! (power_existsUnique x)

prefix:110 "℘ " => power

@[simp] lemma mem_power_iff {x z : V} : z ∈ ℘ x ↔ z ⊆ x :=
  Classical.choose!_spec (power_existsUnique x) z

def power.dfn : SetTheorySemisentence 2 := “p x. ∀ z, z ∈ p ↔ z ⊆ x”

instance power.defined : ℒₛₑₜ-function₁[V] power via power.dfn :=
  ⟨by intro v; simp [power.dfn, power]⟩

instance power.definable : ℒₛₑₜ-function₁[V] power := power.defined.to_definable

@[simp] lemma empty_mem_power (x : V) : ∅ ∈ ℘ x := by simp [mem_power_iff]

@[simp] lemma self_mem_power (x : V) : x ∈ ℘ x := by simp [mem_power_iff]

@[simp] lemma power_empty : ℘ (∅ : V) = {∅} := by ext; simp [mem_power_iff]

@[simp] instance power_nonempty (x : V) : IsNonempty (℘ x) := ⟨x, by simp⟩

end FFL.FirstOrder.SetTheory
