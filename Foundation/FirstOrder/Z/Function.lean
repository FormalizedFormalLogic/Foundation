import Foundation.FirstOrder.Z.Basic

/-!
# Relations and functions in Zermelo set theory
-/

namespace LO.Zermelo

open FirstOrder SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

noncomputable def domain (R : V) : V := {x ∈ ⋃ˢ ⋃ˢ R ; ∃ y, kpair x y ∈ R}

noncomputable def range (R : V) : V := {y ∈ ⋃ˢ ⋃ˢ R ; ∃ x, kpair x y ∈ R}

section domain

lemma mem_sUnion_sUnion_of_kpair_mem_left {x y R : V} (h : kpair x y ∈ R) : x ∈ ⋃ˢ ⋃ˢ R := by
  simp only [mem_sUnion_iff]
  refine ⟨{x, y}, ⟨kpair x y, h, by simp [kpair]⟩, by simp⟩

lemma mem_domain_iff {R x : V} : x ∈ domain R ↔ ∃ y, kpair x y ∈ R := by
  simpa [domain] using fun _ ↦  mem_sUnion_sUnion_of_kpair_mem_left

def domain.dfn : Semisentence ℒₛₑₜ 2 := f“d R. ∀ x, x ∈ d ↔ ∃ y, !kpair.dfn x y ∈ R”

instance domain.defined : ℒₛₑₜ-function₁[V] domain via domain.dfn := ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := domain _), mem_domain_iff]⟩

instance domain.definable : ℒₛₑₜ-function₁[V] domain := domain.defined.to_definable

lemma mem_domain_of_kpair_mem {R x y : V} (h : kpair x y ∈ R) : x ∈ domain R := mem_domain_iff.mpr ⟨y, h⟩

@[simp] lemma domain_empty : domain (∅ : V) = ∅ := by ext; simp [mem_domain_iff]

@[simp] lemma domain_prod (x y : V) [IsNonempty y] : domain (x ×ˢ y) = x := by
  ext z
  suffices z ∈ x → ∃ x, x ∈ y by simpa [mem_domain_iff]
  intro _
  exact IsNonempty.nonempty

lemma domain_subset_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) : domain R ⊆ X := by
  intro x hx
  have : ∃ y, kpair x y ∈ R := by simpa [mem_domain_iff] using hx
  rcases this with ⟨y, hy⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using h _ hy
  exact this.1

@[simp, grind =] lemma domain_insert {x y R : V} : domain (Insert.insert (kpair x y) R) = Insert.insert x (domain R) := by
  ext z; simp only [mem_domain_iff, mem_insert, kpair_iff]; grind

end domain

section range

lemma mem_sUnion_sUnion_of_kpair_mem_right {x y R : V} (h : kpair x y ∈ R) : y ∈ ⋃ˢ ⋃ˢ R := by
  simp only [mem_sUnion_iff]
  refine ⟨{x, y}, ⟨kpair x y, h, by simp [kpair]⟩, by simp⟩

lemma mem_range_iff {R y : V} : y ∈ range R ↔ ∃ x, kpair x y ∈ R := by
  simpa [range] using fun _ ↦ mem_sUnion_sUnion_of_kpair_mem_right

def range.dfn : Semisentence ℒₛₑₜ 2 := f“r R. ∀ y, y ∈ r ↔ ∃ x, !kpair.dfn x y ∈ R”

instance range.defined : ℒₛₑₜ-function₁[V] range via range.dfn := ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := range _), mem_range_iff]⟩

instance range.definable : ℒₛₑₜ-function₁[V] range := range.defined.to_definable

lemma mem_range_of_kpair_mem {R x y : V} (h : kpair x y ∈ R) : y ∈ range R := mem_range_iff.mpr ⟨x, h⟩

@[simp] lemma range_empty : range (∅ : V) = ∅ := by ext; simp [mem_range_iff]

@[simp] lemma range_prod (x y : V) [IsNonempty x] : range (x ×ˢ y) = y := by
  ext z
  suffices z ∈ y → ∃ v, v ∈ x by simpa [mem_range_iff]
  intro _
  exact IsNonempty.nonempty

lemma range_subset_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) : range R ⊆ Y := by
  intro y hy
  have : ∃ x, kpair x y ∈ R := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hx⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using h _ hx
  exact this.2

@[simp, grind =] lemma range_insert {x y R : V} : range (Insert.insert (kpair x y) R) = Insert.insert y (range R) := by
  ext z; simp only [mem_range_iff, mem_insert, kpair_iff]; grind

end range

noncomputable def function (Y X : V) : V := {f ∈ ℘ (X ×ˢ Y) ; ∀ x ∈ X, ∃! y ∈ Y, kpair x y ∈ f}

noncomputable instance : Pow V V := ⟨fun Y X ↦ function Y X⟩

lemma function_def {Y X : V} : Y ^ X = function Y X := rfl

lemma mem_function_iff {f Y X : V} : f ∈ Y ^ X ↔ f ⊆ X ×ˢ Y ∧ ∀ x ∈ X, ∃! y ∈ Y, kpair x y ∈ f := by simp [function, function_def]

def function.dfn : Semisentence ℒₛₑₜ 3 := f“F Y X. ∀ f, f ∈ F ↔ f ⊆ !prod.dfn X Y ∧ ∀ x ∈ X, ∃! y, y ∈ Y ∧ !kpair.dfn x y ∈ f”

instance function.defined : ℒₛₑₜ-function₂[V] (·^·) via function.dfn :=
  ⟨fun v ↦ by simp [function.dfn, mem_ext_iff (y := (v 1)^(v 2)), mem_function_iff]⟩

instance function.definable : ℒₛₑₜ-function₂[V] (·^·) := function.defined.to_definable

lemma mem_function.intro {f X Y : V} (prod : f ⊆ X ×ˢ Y) (total : ∀ x ∈ X, ∃! y ∈ Y, kpair x y ∈ f) : f ∈ Y ^ X :=
  mem_function_iff.mpr ⟨prod, total⟩

lemma subset_prod_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : f ⊆ X ×ˢ Y := mem_function_iff.mp h |>.1

lemma total_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃! y ∈ Y, kpair x y ∈ f := mem_function_iff.mp h |>.2

lemma domain_eq_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : domain f = X := by
  ext x
  suffices (∃ y, kpair x y ∈ f) ↔ x ∈ X by simpa [mem_domain_iff]
  constructor
  · rintro ⟨y, hxy⟩
    have : x ∈ X ∧ y ∈ Y := by simpa using subset_prod_of_mem_function h _ hxy
    exact this.1
  · intro hx
    have : ∃! y, y ∈ Y ∧ kpair x y ∈ f := total_of_mem_function h x hx
    rcases this.exists with ⟨y, _, hy⟩
    exact ⟨y, hy⟩

lemma range_subset_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : range f ⊆ Y := by
  intro y hy
  have : ∃ x, kpair x y ∈ f := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hxy⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using subset_prod_of_mem_function h _ hxy
  exact this.2

lemma mem_function_range_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : f ∈ range f ^ X := by
  have : f ⊆ X ×ˢ range f := by
    intro p hp
    have : ∃ x ∈ X, ∃ y ∈ Y, p = kpair x y := by
      simpa [mem_prod_iff] using subset_prod_of_mem_function h _ hp
    rcases this with ⟨x, hx, y, hy, rfl⟩
    simpa [hx, mem_range_iff] using ⟨x, hp⟩
  apply mem_function.intro this
  intro x hx
  rcases total_of_mem_function h x hx |>.exists with ⟨y, hy, hf⟩
  apply ExistsUnique.intro y ⟨by simpa [mem_range_iff] using ⟨x, hf⟩, hf⟩
  intro y' ⟨hy', hf'⟩
  have : y' ∈ Y := by
    have : x ∈ X ∧ y' ∈ Y := by simpa using subset_prod_of_mem_function h _ hf'
    exact this.2
  have : y' = y := total_of_mem_function h x hx |>.unique (y₁ := y') (y₂ := y) ⟨this, hf'⟩ ⟨hy, hf⟩
  assumption

lemma mem_function_of_mem_function_of_subset {f X Y₁ Y₂ : V} (h : f ∈ Y₁ ^ X) (hY : Y₁ ⊆ Y₂) : f ∈ Y₂ ^ X := by
  have : f ⊆ X ×ˢ Y₂ := calc
    f ⊆ X ×ˢ Y₁ := subset_prod_of_mem_function h
    _ ⊆ X ×ˢ Y₂ := prod_subset_prod_of_subset (by rfl) hY
  apply mem_function.intro this
  intro x hx
  rcases total_of_mem_function h x hx |>.exists with ⟨y, hy, hf⟩
  apply ExistsUnique.intro y ⟨hY _ hy, hf⟩
  intro y' ⟨hy', hf'⟩
  have : y' ∈ Y₁ := by
    have : x ∈ X ∧ y' ∈ Y₁ := by simpa using subset_prod_of_mem_function h _ hf'
    exact this.2
  have : y' = y := total_of_mem_function h x hx |>.unique (y₁ := y') (y₂ := y) ⟨this, hf'⟩ ⟨hy, hf⟩
  assumption

lemma function_subset_function_of_subset {Y₁ Y₂ : V} (hY : Y₁ ⊆ Y₂) (X : V) : Y₁ ^ X ⊆ Y₂ ^ X :=
  fun _ hf ↦ mem_function_of_mem_function_of_subset hf hY

@[simp] lemma empty_function_empty : (∅ : V) ^ (∅ : V) = {∅} := by ext z; simp [mem_function_iff]

class IsFunction (f : V) : Prop where
  mem_func : ∃ X Y : V, f ∈ Y ^ X

lemma isFunction_def {f : V} : IsFunction f ↔ ∃ X Y : V, f ∈ Y ^ X := ⟨fun h ↦ h.mem_func, fun h ↦ ⟨h⟩⟩

def IsFunction.dfn : Semisentence ℒₛₑₜ 1 := f“f. ∃ X Y, f ∈ !function.dfn Y X”

instance IsFunction.defined : ℒₛₑₜ-predicate[V] IsFunction via dfn := ⟨fun v ↦ by simp [isFunction_def, dfn]⟩

instance IsFunction.definable : ℒₛₑₜ-predicate[V] IsFunction := defined.to_definable

lemma isFunction_iff {f : V} : IsFunction f ↔ f ∈ range f ^ domain f := by
  constructor
  · rintro ⟨X, Y, hf⟩
    simpa [domain_eq_of_mem_function hf] using mem_function_range_of_mem_function hf
  · intro h
    exact ⟨_, _, h⟩

namespace IsFunction

lemma mem_function (f : V) [hf : IsFunction f] : f ∈ range f ^ domain f := isFunction_iff.mp hf

lemma unique {f : V} [hf : IsFunction f] {x y₁ y₂} (h₁ : kpair x y₁ ∈ f) (h₂ : kpair x y₂ ∈ f) : y₁ = y₂ := by
  have : ∃! y, y ∈ range f ∧ kpair x y ∈ f := total_of_mem_function (isFunction_iff.mp hf) x (mem_domain_of_kpair_mem h₁)
  exact this.unique ⟨mem_range_of_kpair_mem h₁, h₁⟩ ⟨mem_range_of_kpair_mem h₂, h₂⟩

@[simp] instance empty : IsFunction (∅ : V) := ⟨∅, ∅, by simp⟩

instance insert (f x y : V) (hx : x ∉ domain f) [hf : IsFunction f] : IsFunction (Insert.insert (kpair x y) f) := by
  refine ⟨Insert.insert x (domain f), Insert.insert y (range f), ?_⟩
  apply mem_function.intro
  · have : f ⊆ domain f ×ˢ range f := subset_prod_of_mem_function hf.mem_function
    exact insert_kpair_subset_insert_prod_insert_of_subset_prod this x y
  · intro z hz
    rcases show z = x ∨ z ∈ domain f by simpa using hz with (rfl | hz)
    · apply ExistsUnique.intro y (by simp)
      rintro y' ⟨hy', H'⟩
      rcases show y' = y ∨ kpair z y' ∈ f by simpa using H' with (rfl | H')
      · rfl
      have : z ∈ domain f := mem_domain_of_kpair_mem H'
      contradiction
    · rcases mem_domain_iff.mp hz with ⟨v, hzv⟩
      have : v ∈ range f := mem_range_of_kpair_mem hzv
      apply ExistsUnique.intro v ⟨by simp [this], by simp [hzv]⟩
      rintro w ⟨hw, Hw⟩
      rcases show z = x ∧ w = y ∨ kpair z w ∈ f by simpa using Hw with (⟨rfl, rfl⟩ | Hw)
      · have : z ∈ domain f := mem_domain_of_kpair_mem hzv
        contradiction
      exact hf.unique Hw hzv

@[simp] instance (x y : V) : IsFunction ({kpair x y} : V) := by simpa using insert ∅ x y (by simp)

end IsFunction

end LO.Zermelo
