module

public import Foundation.FirstOrder.SetTheory.ZF

@[expose] public section
/-!
# Basic definitions and lemmata for relations and functions
-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

/-! ### Relations -/

noncomputable def domain (R : V) : V := {x ∈ ⋃ˢ ⋃ˢ R ; ∃ y, ⟨x, y⟩ₖ ∈ R}

noncomputable def range (R : V) : V := {y ∈ ⋃ˢ ⋃ˢ R ; ∃ x, ⟨x, y⟩ₖ ∈ R}

section domain

lemma mem_sUnion_sUnion_of_kpair_mem_left {x y R : V} (h : ⟨x, y⟩ₖ ∈ R) : x ∈ ⋃ˢ ⋃ˢ R := by
  simp only [mem_sUnion_iff]
  refine ⟨{x, y}, ⟨⟨x, y⟩ₖ, h, by simp [kpair]⟩, by simp⟩

lemma mem_domain_iff {R x : V} : x ∈ domain R ↔ ∃ y, ⟨x, y⟩ₖ ∈ R := by
  simpa [domain] using fun _ ↦  mem_sUnion_sUnion_of_kpair_mem_left

def domain.dfn : Semisentence ℒₛₑₜ 2 := f“d R. ∀ x, x ∈ d ↔ ∃ y, !kpair.dfn x y ∈ R”

instance domain.defined : ℒₛₑₜ-function₁[V] domain via domain.dfn := ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := domain _), mem_domain_iff]⟩

instance domain.definable : ℒₛₑₜ-function₁[V] domain := domain.defined.to_definable

lemma mem_domain_of_kpair_mem {R x y : V} (h : ⟨x, y⟩ₖ ∈ R) : x ∈ domain R := mem_domain_iff.mpr ⟨y, h⟩

@[simp] lemma domain_empty : domain (∅ : V) = ∅ := by ext; simp [mem_domain_iff]

@[simp] lemma domain_prod (x y : V) [IsNonempty y] : domain (x ×ˢ y) = x := by
  ext z
  suffices z ∈ x → ∃ x, x ∈ y by simpa [mem_domain_iff]
  intro _
  exact IsNonempty.nonempty

lemma domain_subset_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) : domain R ⊆ X := by
  intro x hx
  have : ∃ y, ⟨x, y⟩ₖ ∈ R := by simpa [mem_domain_iff] using hx
  rcases this with ⟨y, hy⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using h _ hy
  exact this.1

@[simp]
lemma domain_union {R₁ R₂ : V} : domain (R₁ ∪ R₂) = domain R₁ ∪ domain R₂ := by
  ext p
  constructor <;> (simp_all only [mem_union_iff, mem_domain_iff]; grind)

lemma domain_inter_subset {R₁ R₂ : V} : domain (R₁ ∩ R₂) ⊆ domain R₁ ∩ domain R₂ := by
  intro p; simp only [mem_domain_iff, mem_inter_iff]; grind

@[simp, grind .] lemma domain_insert {x y R : V} : domain (insert (⟨x, y⟩ₖ) R) = insert x (domain R) := by
  ext z; simp only [mem_domain_iff, mem_insert, kpair_iff]; grind

end domain

section range

lemma mem_sUnion_sUnion_of_kpair_mem_right {x y R : V} (h : ⟨x, y⟩ₖ ∈ R) : y ∈ ⋃ˢ ⋃ˢ R := by
  simp only [mem_sUnion_iff]
  refine ⟨{x, y}, ⟨⟨x, y⟩ₖ, h, by simp [kpair]⟩, by simp⟩

lemma mem_range_iff {R y : V} : y ∈ range R ↔ ∃ x, ⟨x, y⟩ₖ ∈ R := by
  simpa [range] using fun _ ↦ mem_sUnion_sUnion_of_kpair_mem_right

def range.dfn : Semisentence ℒₛₑₜ 2 := f“r R. ∀ y, y ∈ r ↔ ∃ x, !kpair.dfn x y ∈ R”

instance range.defined : ℒₛₑₜ-function₁[V] range via range.dfn := ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := range _), mem_range_iff]⟩

instance range.definable : ℒₛₑₜ-function₁[V] range := range.defined.to_definable

lemma mem_range_of_kpair_mem {R x y : V} (h : ⟨x, y⟩ₖ ∈ R) : y ∈ range R := mem_range_iff.mpr ⟨x, h⟩

@[simp] lemma range_empty : range (∅ : V) = ∅ := by ext; simp [mem_range_iff]

@[simp] lemma range_prod (x y : V) [IsNonempty x] : range (x ×ˢ y) = y := by
  ext z
  suffices z ∈ y → ∃ v, v ∈ x by simpa [mem_range_iff]
  intro _
  exact IsNonempty.nonempty

lemma range_subset_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) : range R ⊆ Y := by
  intro y hy
  have : ∃ x, ⟨x, y⟩ₖ ∈ R := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hx⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using h _ hx
  exact this.2

@[simp]
lemma range_union {R₁ R₂ : V} : range (R₁ ∪ R₂) = range R₁ ∪ range R₂ := by
  ext p
  constructor <;> (simp_all only [mem_union_iff, mem_range_iff]; grind)

lemma range_inter_subset {R₁ R₂ : V} : range (R₁ ∩ R₂) ⊆ range R₁ ∩ range R₂ := by
  intro p; simp only [mem_range_iff, mem_inter_iff]; grind

@[simp, grind =] lemma range_insert {x y R : V} : range (insert (⟨x, y⟩ₖ) R) = insert y (range R) := by
  ext z; simp only [mem_range_iff, mem_insert, kpair_iff]; grind

end range

/-! ### Functions -/

noncomputable def function (Y X : V) : V := {f ∈ ℘ (X ×ˢ Y) ; ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f}

noncomputable instance : Pow V V := ⟨fun Y X ↦ function Y X⟩

lemma function_def {Y X : V} : Y ^ X = function Y X := rfl

lemma mem_function_iff {f Y X : V} : f ∈ Y ^ X ↔ f ⊆ X ×ˢ Y ∧ ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f := by simp [function, function_def]

def function.dfn : Semisentence ℒₛₑₜ 3 := f“F Y X. ∀ f, f ∈ F ↔ f ⊆ !prod.dfn X Y ∧ ∀ x ∈ X, ∃! y, !kpair.dfn x y ∈ f”

instance function.defined : ℒₛₑₜ-function₂[V] (·^·) via function.dfn :=
  ⟨fun v ↦ by simp [function.dfn, mem_ext_iff (y := (v 1)^(v 2)), mem_function_iff]⟩

instance function.definable : ℒₛₑₜ-function₂[V] (·^·) := function.defined.to_definable

lemma mem_function.intro {f X Y : V} (prod : f ⊆ X ×ˢ Y) (total : ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f) : f ∈ Y ^ X :=
  mem_function_iff.mpr ⟨prod, total⟩

lemma subset_prod_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : f ⊆ X ×ˢ Y := mem_function_iff.mp h |>.1

lemma mem_of_mem_functions {f X Y : V} (h : f ∈ Y ^ X) (hx : ⟨x, y⟩ₖ ∈ f) : x ∈ X ∧ y ∈ Y := by
  simpa using subset_prod_of_mem_function h _ hx

lemma function_subset_power_prod (X Y : V) : Y ^ X ⊆ ℘ (X ×ˢ Y) := fun f hf ↦ by simpa using subset_prod_of_mem_function hf

lemma exists_unique_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f := mem_function_iff.mp h |>.2

lemma exists_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃ y ∈ Y, ⟨x, y⟩ₖ ∈ f := by
  intro x hx
  rcases (exists_unique_of_mem_function h x hx).exists with ⟨y, hy⟩
  have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hy
  exact ⟨y, this.2, hy⟩

lemma domain_eq_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : domain f = X := by
  ext x
  suffices (∃ y, ⟨x, y⟩ₖ ∈ f) ↔ x ∈ X by simpa [mem_domain_iff]
  constructor
  · rintro ⟨y, hxy⟩
    have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hxy
    exact this.1
  · intro hx
    rcases exists_of_mem_function h x hx with ⟨y, hy⟩
    exact ⟨y, hy.2⟩

lemma range_subset_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : range f ⊆ Y := by
  intro y hy
  have : ∃ x, ⟨x, y⟩ₖ ∈ f := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hxy⟩
  have : x ∈ X ∧ y ∈ Y := mem_of_mem_functions h hxy
  exact this.2

lemma mem_function_range_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : f ∈ range f ^ X := by
  have : f ⊆ X ×ˢ range f := by
    intro p hp
    have : ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ := by
      simpa [mem_prod_iff] using subset_prod_of_mem_function h _ hp
    rcases this with ⟨x, hx, y, hy, rfl⟩
    simpa [hx, mem_range_iff] using ⟨x, hp⟩
  apply mem_function.intro this
  intro x hx
  rcases exists_unique_of_mem_function h x hx |>.exists with ⟨y, hf⟩
  apply ExistsUnique.intro y hf
  intro y' hf'
  have : y' = y := exists_unique_of_mem_function h x hx |>.unique hf' hf
  assumption

lemma mem_function_of_mem_function_of_subset {f X Y₁ Y₂ : V} (h : f ∈ Y₁ ^ X) (hY : Y₁ ⊆ Y₂) : f ∈ Y₂ ^ X := by
  have : f ⊆ X ×ˢ Y₂ := calc
    f ⊆ X ×ˢ Y₁ := subset_prod_of_mem_function h
    _ ⊆ X ×ˢ Y₂ := prod_subset_prod_of_subset (by rfl) hY
  apply mem_function.intro this
  intro x hx
  rcases exists_unique_of_mem_function h x hx |>.exists with ⟨y, hf⟩
  apply ExistsUnique.intro y hf
  intro y' hf'
  have : y' = y := exists_unique_of_mem_function h x hx |>.unique hf' hf
  assumption

lemma function_subset_function_of_subset {Y₁ Y₂ : V} (hY : Y₁ ⊆ Y₂) (X : V) : Y₁ ^ X ⊆ Y₂ ^ X :=
  fun _ hf ↦ mem_function_of_mem_function_of_subset hf hY

@[simp] lemma empty_function_empty : (∅ : V) ^ (∅ : V) = {∅} := by ext z; simp [mem_function_iff]

/-- Functions over arbitrary domain and range -/
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

lemma of_mem {f X Y : V} (h : f ∈ Y ^ X) : IsFunction f := ⟨X, Y, h⟩

lemma mem_function (f : V) [hf : IsFunction f] : f ∈ range f ^ domain f := isFunction_iff.mp hf

lemma unique {f : V} [hf : IsFunction f] {x y₁ y₂} (h₁ : ⟨x, y₁⟩ₖ ∈ f) (h₂ : ⟨x, y₂⟩ₖ ∈ f) : y₁ = y₂ := by
  have : ∃! y, ⟨x, y⟩ₖ ∈ f := exists_unique_of_mem_function (isFunction_iff.mp hf) x (mem_domain_of_kpair_mem h₁)
  exact this.unique h₁ h₂

@[simp] instance empty : IsFunction (∅ : V) := ⟨∅, ∅, by simp⟩

protected def insert (f x y : V) (hx : x ∉ domain f) [hf : IsFunction f] : IsFunction (insert ⟨x, y⟩ₖ f) := by
  refine ⟨insert x (domain f), insert y (range f), ?_⟩
  apply mem_function.intro
  · have : f ⊆ domain f ×ˢ range f := subset_prod_of_mem_function hf.mem_function
    exact insert_kpair_subset_insert_prod_insert_of_subset_prod this x y
  · intro z hz
    rcases show z = x ∨ z ∈ domain f by simpa using hz with (rfl | hz)
    · apply ExistsUnique.intro y (by simp)
      rintro y' H'
      rcases show y' = y ∨ ⟨z, y'⟩ₖ ∈ f by simpa using H' with (rfl | H')
      · rfl
      have : z ∈ domain f := mem_domain_of_kpair_mem H'
      contradiction
    · rcases mem_domain_iff.mp hz with ⟨v, hzv⟩
      have : v ∈ range f := mem_range_of_kpair_mem hzv
      apply ExistsUnique.intro v (by simp [hzv])
      rintro w Hw
      rcases show z = x ∧ w = y ∨ ⟨z, w⟩ₖ ∈ f by simpa using Hw with (⟨rfl, rfl⟩ | Hw)
      · have : z ∈ domain f := mem_domain_of_kpair_mem hzv
        contradiction
      exact hf.unique Hw hzv

@[simp] instance (x y : V) : IsFunction ({⟨x, y⟩ₖ} : V) := by simpa using IsFunction.insert ∅ x y (by simp)

end IsFunction

lemma function_eq_of_subset {X Y f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Y ^ X) (h : f ⊆ g) : f = g := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  apply subset_antisymm h
  intro p hp
  rcases show ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ from by
    simpa [mem_prod_iff] using subset_prod_of_mem_function hg _ hp with ⟨x, hx, y, hy, rfl⟩
  rcases show ∃ y' ∈ Y, ⟨x, y'⟩ₖ ∈ f from exists_of_mem_function hf x hx with ⟨y', hy', Hf⟩
  have : ⟨x, y'⟩ₖ ∈ g := h _ Hf
  rcases show y = y' from IsFunction.unique hp (h _ Hf)
  assumption

lemma function_ext {X Y f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Y ^ X)
    (h : ∀ x ∈ X, ∀ y ∈ Y, ⟨x, y⟩ₖ ∈ f → ⟨x, y⟩ₖ ∈ g) : f = g := by
  apply function_eq_of_subset hf hg
  intro p hp
  rcases show ∃ x ∈ X, ∃ y ∈ Y, p = ⟨x, y⟩ₖ from by
    simpa [mem_prod_iff] using subset_prod_of_mem_function hf _ hp with ⟨x, hx, y, hy, rfl⟩
  exact h x hx y hy hp

@[grind <=] lemma two_val_function_mem_iff_not {X f x : V} (hf : f ∈ (2 ^ X : V)) (hx : x ∈ X) : ⟨x, 0⟩ₖ ∈ f ↔ ⟨x, 1⟩ₖ ∉ f := by
  have : IsFunction f := IsFunction.of_mem hf
  constructor
  · intro h0 h1
    have : (0 : V) = 1 := IsFunction.unique h0 h1
    simp_all
  · intro h1
    rcases exists_of_mem_function hf x hx with ⟨i, hi, hf⟩
    rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
    · assumption
    · contradiction

def Injective (R : V) : Prop := ∀ x₁ x₂ y, ⟨x₁, y⟩ₖ ∈ R → ⟨x₂, y⟩ₖ ∈ R → x₁ = x₂

def Injective.dfn : Semisentence ℒₛₑₜ 1 := f“f. ∀ x₁ x₂ y, !kpair.dfn x₁ y ∈ f → !kpair.dfn x₂ y ∈ f → x₁ = x₂”

instance Injective.defined : ℒₛₑₜ-predicate[V] Injective via dfn := ⟨fun v ↦ by simp [Injective, dfn]⟩

instance Injective.definable : ℒₛₑₜ-predicate[V] Injective := defined.to_definable

lemma Injective.empty : Injective (∅ : V) := fun x₁ x₂ y ↦ by simp

/-- Identity -/
noncomputable def identity (X : V) : V := {p ∈ X ×ˢ X ; ∃ x ∈ X, p = ⟨x, x⟩ₖ}

lemma mem_identity_iff {X p : V} : p ∈ identity X ↔ ∃ x ∈ X, p = ⟨x, x⟩ₖ := by
  suffices ∀ x ∈ X, p = ⟨x, x⟩ₖ → p ∈ X ×ˢ X by simpa [identity]
  rintro x hx rfl
  simp [hx]

def identity.dfn : Semisentence ℒₛₑₜ 2 := f“i X. ∀ p, p ∈ i ↔ ∃ x ∈ X, p = !kpair.dfn x x”

instance identity.defined : ℒₛₑₜ-function₁[V] identity via dfn := ⟨fun v ↦ by simp [dfn, mem_ext_iff (y := identity (v 1)), mem_identity_iff]⟩

instance identity.definable : ℒₛₑₜ-function₁[V] identity := defined.to_definable

@[simp] lemma kpair_mem_identity_iff {X x : V} : ⟨x, y⟩ₖ ∈ identity X ↔ x ∈ X ∧ x = y := by
  simp only [mem_identity_iff, kpair_iff, exists_eq_right_right', and_congr_left_iff]
  grind

@[simp] lemma identity_mem_function (X : V) : identity X ∈ X ^ X := by
  refine mem_function.intro ?_ ?_
  · intro p hp
    have : ∃ x ∈ X, p = ⟨x, x⟩ₖ := by simpa [mem_identity_iff] using hp
    rcases this with ⟨x, hx, rfl⟩
    simp_all
  · intro x hx
    apply ExistsUnique.intro x (by simp [hx])
    simp only [kpair_mem_identity_iff, and_imp]
    grind

instance IsFunction.identity (X : V) : IsFunction (identity X) := IsFunction.of_mem (identity_mem_function X)

@[simp] lemma identity_injective (X : V) : Injective (identity X) := by
  intro x₁ x₂ y h₁ h₂
  rcases show x₁ ∈ X ∧ x₁ = y by simpa using h₁ with ⟨hx₁, rfl⟩
  rcases show x₂ ∈ X ∧ x₂ = x₁ by simpa using h₂ with ⟨hx₂, rfl⟩
  rfl

/-- Composition -/
noncomputable def compose (R S : V) : V := {p ∈ domain R ×ˢ range S ; ∃ x y z, ⟨x, y⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ S ∧ p = ⟨x, z⟩ₖ}

lemma mem_compose_iff {R S p : V} : p ∈ compose R S ↔ ∃ x y z, ⟨x, y⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ S ∧ p = ⟨x, z⟩ₖ := by
  simp only [compose, exists_and_left, mem_sep_iff, and_iff_right_iff_imp, forall_exists_index, and_imp]
  rintro x y hxy z hyz rfl
  simp [mem_domain_of_kpair_mem hxy, mem_range_of_kpair_mem hyz]

@[simp] lemma kpair_mem_compose_iff {R S x z : V} :
    ⟨x, z⟩ₖ ∈ compose R S ↔ ∃ y, ⟨x, y⟩ₖ ∈ R ∧ ⟨y, z⟩ₖ ∈ S := by
  simp only [mem_compose_iff, kpair_iff, exists_and_left, exists_eq_right_right']
  grind

lemma compose_subset_prod {X Y Z R S : V} (hR : R ⊆ X ×ˢ Y) (hS : S ⊆ Y ×ˢ Z) : compose R S ⊆ X ×ˢ Z := by
  intro p hp
  rcases mem_compose_iff.mp hp with ⟨x, y, z, hxy, hyz, rfl⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using hR _ hxy
  have : y ∈ Y ∧ z ∈ Z := by simpa using hS _ hyz
  simp_all

lemma compose_function {X Y Z f g : V} (hf : f ∈ Y ^ X) (hg : g ∈ Z ^ Y) : compose f g ∈ Z ^ X := by
  have : IsFunction f := IsFunction.of_mem hf
  have : IsFunction g := IsFunction.of_mem hg
  apply mem_function.intro ?_ ?_
  · exact compose_subset_prod (subset_prod_of_mem_function hf) (subset_prod_of_mem_function hg)
  · intro x hx
    have : ∃ y ∈ Y, ⟨x, y⟩ₖ ∈ f := exists_of_mem_function hf x hx
    rcases this with ⟨y, hy, hxy⟩
    have : ∃ z ∈ Z, ⟨y, z⟩ₖ ∈ g := exists_of_mem_function hg y hy
    rcases this with ⟨z, hz, hyz⟩
    apply ExistsUnique.intro z (by simpa using ⟨y, hxy, hyz⟩)
    intro z' hz'
    have : ∃ y', ⟨x, y'⟩ₖ ∈ f ∧ ⟨y', z'⟩ₖ ∈ g := by simpa using hz'
    rcases this with ⟨y', hxy', hy'z'⟩
    rcases IsFunction.unique hxy hxy'
    rcases IsFunction.unique hyz hy'z'
    rfl

lemma compose_injective {R S : V} (hR : Injective R) (hS : Injective S) : Injective (compose R S) := by
  intro x₁ x₂ z h₁ h₂
  have : ∃ y₁, ⟨x₁, y₁⟩ₖ ∈ R ∧ ⟨y₁, z⟩ₖ ∈ S := by simpa using h₁
  rcases this with ⟨y₁, hx₁y₁, hy₁z⟩
  have : ∃ y₂, ⟨x₂, y₂⟩ₖ ∈ R ∧ ⟨y₂, z⟩ₖ ∈ S := by simpa using h₂
  rcases this with ⟨y₂, hx₂y₂, hy₂z⟩
  have : y₁ = y₂ := hS y₁ y₂ z hy₁z hy₂z
  rcases this
  exact hR x₁ x₂ y₁ hx₁y₁ hx₂y₂

/- This definition of value is adapted from NM's contribution to Metamath: https://us.metamath.org/mpeuni/fv3.html -/
noncomputable def value (f x : V) := {z ∈ ⋃ˢ range f ; ∃ y, z ∈ y ∧ ⟨x, y⟩ₖ ∈ f}

/-- If `x` is in `domain f`, then `f ‘ x` is the value of `f` at `x`, else it is `∅`. -/
scoped notation f:arg " ‘ " x:arg => value f x

def value.dfn : Semisentence ℒₛₑₜ 3 := f“v f x. ∀ z, z ∈ v ↔ z ∈ !sUnion.dfn (!range.dfn f) ∧ ∃ y, z ∈ y ∧ !kpair.dfn x y ∈ f”

instance value.defined : ℒₛₑₜ-function₂[V] value via value.dfn :=
  ⟨fun v ↦ by simp [dfn, value]; simp only [mem_ext_iff, mem_sep_iff]⟩

instance value.definable : ℒₛₑₜ-function₂[V] value := value.defined.to_definable

lemma value_mem_range {f x : V} {X Y : V} (hf : f ∈ Y ^ X) (hx : x ∈ X) : f ‘ x ∈ range f := by
  simp_all only [mem_function_iff, value, mem_range_iff]
  obtain ⟨hfleft, hfright⟩ := hf
  specialize hfright x hx
  obtain ⟨y, hy⟩ := ExistsUnique.exists hfright
  have h1 {w : V} : ⟨x, w⟩ₖ ∈ f → w = y := by
    intro h; exact hfright.unique h hy
  have h2 : y = {z ∈ ⋃ˢ range f ; ∃ y, z ∈ y ∧ ⟨x, y⟩ₖ ∈ f} := by
    ext z
    simp only [mem_sep_iff, mem_sUnion_iff, mem_range_iff]
    constructor <;> intro h <;> grind
  grind

namespace IsFunction

lemma value_eq_of_kpair_mem (f x y : V) [IsFunction f] (hxy : ⟨x, y⟩ₖ ∈ f) :
    f ‘ x = y := by
  ext z
  constructor
  · intro hz
    rcases show z ∈ ⋃ˢ range f ∧ ∃ y', z ∈ y' ∧ ⟨x, y'⟩ₖ ∈ f by
        simpa [value, mem_sep_iff] using hz with
      ⟨-, y', hzy', hxy'⟩
    have : y' = y := IsFunction.unique hxy' hxy
    simpa [this] using hzy'
  · intro hzy
    have hyR : y ∈ range f := mem_range_of_kpair_mem hxy
    have hzU : z ∈ ⋃ˢ range f := mem_sUnion_iff.mpr ⟨y, hyR, hzy⟩
    exact mem_sep_iff.mpr ⟨hzU, y, hzy, hxy⟩

end IsFunction

/-- Restricting the domain of a relation -/
noncomputable def restrict (R A : V) : V := R ∩ (A ×ˢ range R)

/-- Restricting the domain of a relation -/
scoped notation R:arg " ↾ " A:arg => restrict R A

def restrict.dfn : Semisentence ℒₛₑₜ 3 := f“r R A. r = !inter.dfn R (!prod.dfn A (!range.dfn R))”

instance restrict.defined : ℒₛₑₜ-function₂[V] restrict via restrict.dfn :=
  ⟨fun v ↦ by simp [dfn, restrict]⟩

instance restrict.definable : ℒₛₑₜ-function₂[V] restrict := restrict.defined.to_definable

lemma mem_restrict_iff {R A p : V} :
    p ∈ (R ↾ A) ↔ p ∈ R ∧ ∃ x ∈ A, ∃ y, p = ⟨x, y⟩ₖ := by
  constructor
  · intro hp
    rcases show p ∈ R ∧ p ∈ A ×ˢ range R by simpa [restrict] using hp with ⟨hpR, hpP⟩
    rcases show ∃ x ∈ A, ∃ y ∈ range R, p = ⟨x, y⟩ₖ by simpa [mem_prod_iff] using hpP with
      ⟨x, hxA, y, -, rfl⟩
    exact ⟨hpR, x, hxA, y, rfl⟩
  · rintro ⟨hpR, x, hxA, y, rfl⟩
    have hyR : y ∈ range R := mem_range_of_kpair_mem hpR
    have hpP : ⟨x, y⟩ₖ ∈ A ×ˢ range R := by simpa [mem_prod_iff] using ⟨hxA, hyR⟩
    simpa [restrict] using And.intro hpR hpP

lemma IsFunction.restrict (f A : V) [hf : IsFunction f] : IsFunction (f ↾ A) := by
  have hff : f ∈ range f ^ domain f := hf.mem_function
  have : f ↾ A ∈ range f ^ (domain f ∩ A) := by
    apply mem_function.intro
    · intro p hp
      rcases mem_restrict_iff.mp hp with ⟨hpf, x, hxA, y, rfl⟩
      have hxd : x ∈ domain f := mem_domain_of_kpair_mem hpf
      have hyr : y ∈ range f := mem_range_of_kpair_mem hpf
      simpa [mem_prod_iff] using ⟨⟨hxd, hxA⟩, hyr⟩
    · intro x hx
      have ⟨hxd, hxA⟩ := show x ∈ domain f ∧ x ∈ A by simpa using hx
      rcases exists_unique_of_mem_function hff x hxd with ⟨y, hy, hyu⟩
      refine ExistsUnique.intro y ?_ ?_
      · exact mem_restrict_iff.mpr ⟨hy, x, hxA, y, rfl⟩
      · intro y' hy'
        have ⟨hy'f, _⟩ := mem_restrict_iff.mp hy'
        exact hyu y' hy'f
  exact IsFunction.of_mem this

lemma IsFunction.restrict_eq_self (f A : V) [hf : IsFunction f] (hA : domain f ⊆ A) : f ↾ A = f := by
  apply subset_antisymm
  · intro p hp
    exact (mem_restrict_iff.mp hp).1
  · intro p hp
    rcases show ∃ x ∈ domain f, ∃ y ∈ range f, p = ⟨x, y⟩ₖ from by
        simpa [mem_prod_iff] using subset_prod_of_mem_function hf.mem_function p hp with
      ⟨x, hxd, y, -, rfl⟩
    exact mem_restrict_iff.mpr ⟨hp, x, hA x hxd, y, rfl⟩

lemma domain_restrict_eq (R A : V) : domain (R ↾ A) = domain R ∩ A := by
  ext z
  apply Iff.intro <;> intro h
  · simp_all only [mem_domain_iff, mem_inter_iff, restrict]
    aesop
  · simp_all only [mem_domain_iff, mem_inter_iff, restrict]
    obtain ⟨⟨y, hy⟩, hzA⟩ := h
    use y
    simp_all only [kpair_mem_iff, true_and, mem_range_iff]
    use z

@[simp] lemma kpair_mem_restrict_iff {R A x y : V} :
    ⟨x, y⟩ₖ ∈ (R ↾ A) ↔ ⟨x, y⟩ₖ ∈ R ∧ x ∈ A := by
  simp [mem_restrict_iff]

lemma restrict_restrict_eq_restrict_inter (R A B : V) : (R ↾ A) ↾ B = R ↾ (A ∩ B) := by
  ext p
  simp only [mem_restrict_iff, mem_inter_iff]
  constructor
  · rintro ⟨⟨hpR, x, hxA, y, rfl⟩, x', hx'B, y', hxy⟩
    rcases kpair_inj hxy with ⟨rfl, rfl⟩
    exact ⟨hpR, x, ⟨hxA, hx'B⟩, y, rfl⟩
  · rintro ⟨hpR, x, hxAB, y, rfl⟩
    exact ⟨⟨hpR, x, hxAB.1, y, rfl⟩, x, hxAB.2, y, rfl⟩

lemma restrict_restrict_of_subset {R A B : V} (h : B ⊆ A) : (R ↾ A) ↾ B = R ↾ B := by
  simpa [inter_eq_right_of_subset h] using restrict_restrict_eq_restrict_inter R A B

/--
Restricting an inserted relation to a set that does not contain the inserted first coordinate
recovers the original restriction.
-/
lemma restrict_insert_kpair_eq_restrict_of_not_mem
    {f x y A : V} (hxA : x ∉ A) :
    (insert ⟨x, y⟩ₖ f) ↾ A = f ↾ A := by
  ext p
  constructor
  · intro hp
    rcases mem_restrict_iff.mp hp with ⟨hp', a, haA, b, rfl⟩
    rcases show ⟨a, b⟩ₖ = ⟨x, y⟩ₖ ∨ ⟨a, b⟩ₖ ∈ f by simpa using hp' with (hxy | hf)
    · rcases kpair_inj hxy with ⟨rfl, rfl⟩
      exact (hxA haA).elim
    · exact mem_restrict_iff.mpr ⟨hf, a, haA, b, rfl⟩
  · intro hp
    rcases mem_restrict_iff.mp hp with ⟨hf, a, haA, b, rfl⟩
    exact mem_restrict_iff.mpr ⟨by simp [hf], a, haA, b, rfl⟩

/-- Image of a set under a relation -/
noncomputable def image (R A : V) : V := range (restrict R A)

/-- Image of a set under a relation -/
scoped notation R:arg " “ " A:arg => image R A

def image.dfn : Semisentence ℒₛₑₜ 3 := f“B R A. B = !range.dfn (!restrict.dfn R A)”

instance image.defined : ℒₛₑₜ-function₂[V] image via image.dfn :=
  ⟨fun v ↦ by simp [dfn, image]⟩

instance image.definable : ℒₛₑₜ-function₂[V] image := image.defined.to_definable

/--
Graph construction from a function-like relation on a fixed set `X`.
-/
lemma replacement_graph_exists_on [V ⊧ₘ* 𝗭𝗙] (X : V) (R : V → V → Prop) (hR : ℒₛₑₜ-relation[V] R)
    (hfun : ∀ x : V, x ∈ X → ∃! y : V, R x y) :
    ∃ f : V, IsFunction f ∧ domain f = X ∧
      ∀ x ∈ X, ∀ y, ⟨x, y⟩ₖ ∈ f ↔ R x y := by
  let S : V → V → Prop := fun x p ↦ ∃ y : V, R x y ∧ p = ⟨x, y⟩ₖ
  have hS : ℒₛₑₜ-relation[V] S := by
    letI : ℒₛₑₜ-relation[V] R := hR
    change ℒₛₑₜ-relation[V] (fun x p ↦ ∃ y : V, R x y ∧ p = ⟨x, y⟩ₖ)
    definability
  have hfunS : ∀ x : V, x ∈ X → ∃! p : V, S x p := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hyu⟩
    refine ⟨⟨x, y⟩ₖ, ⟨y, hy, rfl⟩, ?_⟩
    intro p hp
    rcases hp with ⟨y', hy', hp⟩
    have : y' = y := hyu y' hy'
    rcases this
    simp [hp]
  rcases replacement_exists_on (X := X) S hS hfunS with ⟨f, hf⟩
  have hmem : ∀ p : V, p ∈ f ↔ ∃ x ∈ X, ∃ y, R x y ∧ p = ⟨x, y⟩ₖ := by
    intro p
    constructor
    · intro hp
      rcases (hf p).1 hp with ⟨x, hxX, hpS⟩
      rcases hpS with ⟨y, hy, rfl⟩
      exact ⟨x, hxX, y, hy, rfl⟩
    · rintro ⟨x, hxX, y, hy, rfl⟩
      exact (hf _).2 ⟨x, hxX, ⟨y, hy, rfl⟩⟩
  have hgraph : ∀ x ∈ X, ∀ y, ⟨x, y⟩ₖ ∈ f ↔ R x y := by
    intro x hxX y
    constructor
    · intro hxy
      rcases (hmem _).1 hxy with ⟨x', hx'X, y', hy', hxy'⟩
      rcases kpair_inj hxy' with ⟨rfl, rfl⟩
      exact hy'
    · intro hxy
      exact (hmem _).2 ⟨x, hxX, y, hxy, rfl⟩
  have hdomain : domain f = X := by
    apply subset_antisymm
    · intro x hx
      rcases mem_domain_iff.mp hx with ⟨y, hxy⟩
      rcases (hmem _).1 hxy with ⟨x', hx'X, y', -, hxy'⟩
      rcases kpair_inj hxy' with ⟨rfl, -⟩
      exact hx'X
    · intro x hxX
      rcases hfun x hxX with ⟨y, hy, -⟩
      exact mem_domain_iff.mpr ⟨y, (hgraph x hxX y).2 hy⟩
  have hfunc_mem : f ∈ range f ^ domain f := by
    apply mem_function.intro
    · intro p hp
      rcases (hmem _).1 hp with ⟨x, hxX, y, hy, rfl⟩
      have hxyf : ⟨x, y⟩ₖ ∈ f := (hgraph x hxX y).2 hy
      have hxd : x ∈ domain f := mem_domain_of_kpair_mem hxyf
      have hyr : y ∈ range f := mem_range_of_kpair_mem hxyf
      simpa [mem_prod_iff] using ⟨hxd, hyr⟩
    · intro x hx
      rcases mem_domain_iff.mp hx with ⟨y₀, hxy₀⟩
      refine ExistsUnique.intro y₀ hxy₀ ?_
      intro y₁ hxy₁
      have hxX : x ∈ X := by simpa [hdomain] using hx
      have hR₀ : R x y₀ := (hgraph x hxX y₀).1 hxy₀
      have hR₁ : R x y₁ := (hgraph x hxX y₁).1 hxy₁
      exact (hfun x hxX).unique hR₁ hR₀
  refine ⟨f, IsFunction.of_mem hfunc_mem, hdomain, hgraph⟩

/--
Graph construction from a definable unary function on a fixed set `X`.
-/
lemma replacement_graph_exists_on_of_definableFunction [V ⊧ₘ* 𝗭𝗙]
    (X : V) (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ∃ f : V, IsFunction f ∧ domain f = X ∧
      ∀ x ∈ X, ∀ y, ⟨x, y⟩ₖ ∈ f ↔ y = F x := by
  let R : V → V → Prop := fun x y ↦ Function.Graph F y x
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-function₁[V] F := hFdef
    change ℒₛₑₜ-relation[V] (fun x y ↦ Function.Graph F y x)
    definability
  have hfun : ∀ x : V, x ∈ X → ∃! y : V, R x y := by
    intro x _
    simpa [R] using functionGraph_functionLike F x
  rcases replacement_graph_exists_on (X := X) R hR hfun with ⟨f, hf, hdf, hgraph⟩
  refine ⟨f, hf, hdf, ?_⟩
  intro x hx y
  simpa [R, Function.Graph] using hgraph x hx y

/-! ### Cardinality comparison -/

@[simp] lemma kpair_mem_sUnion_iff {C x y : V} :
    ⟨x, y⟩ₖ ∈ ⋃ˢ C ↔ ∃ f ∈ C, ⟨x, y⟩ₖ ∈ f := by
  simp [mem_sUnion_iff]

lemma IsFunction.sUnion_of_coherent {C : V}
    (hfunc : ∀ f ∈ C, IsFunction f)
    (hcoh : ∀ f ∈ C, ∀ g ∈ C, ∀ x y₁ y₂,
      ⟨x, y₁⟩ₖ ∈ f → ⟨x, y₂⟩ₖ ∈ g → y₁ = y₂) :
    IsFunction (⋃ˢ C) := by
  have hmem : ⋃ˢ C ∈ range (⋃ˢ C) ^ domain (⋃ˢ C) := by
    apply mem_function.intro
    · intro p hp
      rcases mem_sUnion_iff.mp hp with ⟨f, hfC, hpf⟩
      have hff : IsFunction f := hfunc f hfC
      have hmem : f ∈ range f ^ domain f := IsFunction.mem_function f
      rcases show ∃ x ∈ domain f, ∃ y ∈ range f, p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function hmem p hpf with
        ⟨x, hxd, y, hyd, rfl⟩
      have hxyU : ⟨x, y⟩ₖ ∈ ⋃ˢ C := mem_sUnion_iff.mpr ⟨f, hfC, by simpa⟩
      have hxU : x ∈ domain (⋃ˢ C) := mem_domain_of_kpair_mem hxyU
      have hyU : y ∈ range (⋃ˢ C) := mem_range_of_kpair_mem hxyU
      simpa [mem_prod_iff] using And.intro hxU hyU
    · intro x hx
      rcases mem_domain_iff.mp hx with ⟨y, hxyU⟩
      refine ExistsUnique.intro y hxyU ?_
      intro y' hxy'U
      rcases mem_sUnion_iff.mp hxyU with ⟨f, hfC, hxyf⟩
      rcases mem_sUnion_iff.mp hxy'U with ⟨g, hgC, hxyg⟩
      exact (hcoh f hfC g hgC x y y' hxyf hxyg).symm
  exact IsFunction.of_mem hmem

def CardLE (X Y : V) : Prop := ∃ f ∈ Y ^ X, Injective f

infix:50 " ≤# " => CardLE

lemma cardLE_of_subset {X Y : V} (h : X ⊆ Y) : X ≤# Y :=
  ⟨identity X, mem_function_of_mem_function_of_subset (identity_mem_function X) h, by simp⟩

@[simp] lemma cardLE_empty (X : V) : ∅ ≤# X := cardLE_of_subset (by simp)

@[simp, refl] lemma CardLE.refl (X : V) : X ≤# X := cardLE_of_subset (by simp)

@[trans] lemma CardLE.trans {X Y Z : V} : X ≤# Y → Y ≤# Z → X ≤# Z := by
  rintro ⟨f, hf, f_inj⟩
  rintro ⟨g, hg, g_inj⟩
  refine ⟨compose f g, compose_function hf hg, compose_injective f_inj g_inj⟩

def CardLT (X Y : V) : Prop := X ≤# Y ∧ ¬Y ≤# X

infix:50 " <# " => CardLT

def CardLE.dfn : Semisentence ℒₛₑₜ 2 := f“X Y. ∃ f ∈ !function.dfn Y X, !Injective.dfn f”

instance CardLE.defined : ℒₛₑₜ-relation[V] CardLE via dfn := ⟨fun v ↦ by simp [CardLE, dfn]⟩

instance CardLE.definable : ℒₛₑₜ-relation[V] CardLE := defined.to_definable

def CardLT.dfn : Semisentence ℒₛₑₜ 2 := “X Y. !CardLE.dfn X Y ∧ ¬!CardLE.dfn Y X”

instance CardLT.defined : ℒₛₑₜ-relation[V] CardLT via dfn := ⟨fun v ↦ by simp [CardLT, dfn]⟩

instance CardLT.definable : ℒₛₑₜ-relation[V] CardLT := defined.to_definable

def CardEQ (X Y : V) : Prop := X ≤# Y ∧ Y ≤# X

infix:60 " ≋ " => CardEQ

def CardEQ.dfn : Semisentence ℒₛₑₜ 2 := “X Y. !CardLE.dfn X Y ∧ !CardLE.dfn Y X”

instance CardEQ.defined : ℒₛₑₜ-relation[V] CardEQ via dfn := ⟨fun v ↦ by simp [CardEQ, dfn]⟩

instance CardEQ.definable : ℒₛₑₜ-relation[V] CardEQ := defined.to_definable

lemma CardEQ.le {X Y : V} (h : X ≋ Y) : X ≤# Y := h.1

lemma CardEQ.ge {X Y : V} (h : X ≋ Y) : Y ≤# X := h.2

@[simp, refl] lemma CardEQ.refl (X : V) : X ≋ X := ⟨by rfl, by rfl⟩

@[symm] lemma CardEQ.symm {X Y : V} : X ≋ Y → Y ≋ X := fun e ↦ ⟨e.2, e.1⟩

@[trans] lemma CardEQ.trans {X Y Z : V} : X ≋ Y → Y ≋ Z → X ≋ Z := fun eXY eYZ ↦
  ⟨eXY.le.trans eYZ.le, eYZ.ge.trans eXY.ge⟩

lemma cardLT_power (X : V) : X <# ℘ X := by
  have : X ≤# ℘ X := by
    let F : V := {p ∈ X ×ˢ ℘ X ; ∃ x ∈ X, p = ⟨x, {x}⟩ₖ}
    have : F ∈ ℘ X ^ X := by
      apply mem_function.intro
      · simp [F]
      · intro x hx
        apply ExistsUnique.intro {x} (by simp [F, hx])
        intro y hy
        have : y ⊆ X ∧ y = {x} := by simpa [hx, F] using hy
        simp [this]
    have : Injective F := by
      intro x₁ x₂ s h₁ h₂
      rcases show (x₁ ∈ X ∧ s ⊆ X) ∧ x₁ ∈ X ∧ s = {x₁} by simpa [F] using h₁ with ⟨_, _, rfl⟩
      have : (x₂ ∈ X ∧ x₁ ∈ X) ∧ x₁ ∈ X ∧ x₂ = x₁ := by simpa [F] using h₂
      simp [this.2.2]
    refine ⟨F, by assumption, by assumption⟩
  have : ¬℘ X ≤# X := by
    rintro ⟨F, hF, injF⟩
    have : IsFunction F := IsFunction.of_mem hF
    let D : V := {x ∈ X ; ∃ s ∈ ℘ X, ⟨s, x⟩ₖ ∈ F ∧ x ∉ s}
    have : ∃ d ∈ X, ⟨D, d⟩ₖ ∈ F := exists_of_mem_function hF D (by simp [D])
    rcases this with ⟨d, hd, Hd⟩
    have : d ∈ D ↔ d ∉ D := calc
      d ∈ D ↔ ∃ s ⊆ X, ⟨s, d⟩ₖ ∈ F ∧ d ∉ s := by simp [hd, D]
      _     ↔ d ∉ D := ?_
    · grind
    constructor
    · rintro ⟨S, hS, hSF, hdS⟩
      rcases show D = S from injF _ _ _ Hd hSF
      assumption
    · intro h
      refine ⟨D, by simpa [hd] using mem_of_mem_functions hF Hd, Hd, h⟩
  refine ⟨by assumption, by assumption⟩

lemma two_pow_cardEQ_power (X : V) : 2 ^ X ≋ ℘ X := by
  constructor
  · let F : V := {p ∈ (2 ^ X) ×ˢ ℘ X ; ∃ f s, p = ⟨f, s⟩ₖ ∧ ∀ x, x ∈ s ↔ ⟨x, 1⟩ₖ ∈ f}
    refine ⟨F, ?_, ?_⟩
    · apply mem_function.intro
      · simp [F]
      · intro f hf
        let s : V := {x ∈ X ; ⟨x, 1⟩ₖ ∈ f}
        have ss_s : s ⊆ X := by simp [s]
        have mem_s : ∀ x, x ∈ s ↔ ⟨x, 1⟩ₖ ∈ f := by
          simp only [mem_sep_iff, and_iff_right_iff_imp, s]
          intro x hx
          exact mem_of_mem_functions hf hx |>.1
        apply ExistsUnique.intro s ?_ ?_
        · simp [F, hf, ss_s, mem_s]
        · intro t ht
          ext x
          have ht : (f ∈ ((2 : V) ^ X) ∧ t ⊆ X) ∧ ∀ x, x ∈ t ↔ ⟨x, 1⟩ₖ ∈ f := by simpa [F] using ht
          simp [ht, mem_s]
    · intro f₁ f₂ s h₁ h₂
      have : (f₁ ∈ (2 ^ X : V) ∧ s ⊆ X) ∧ ∀ x, x ∈ s ↔ ⟨x, 1⟩ₖ ∈ f₁ := by simpa [F] using h₁
      rcases this with ⟨⟨f₁func, hs⟩, H₁⟩
      have : (f₂ ∈ (2 ^ X : V) ∧ s ⊆ X) ∧ ∀ x, x ∈ s ↔ ⟨x, 1⟩ₖ ∈ f₂ := by simpa [F] using h₂
      rcases this with ⟨⟨f₂func, _⟩, H₂⟩
      apply function_ext f₁func f₂func
      intro x hx i hi
      rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
      · contrapose
        suffices ⟨x, 1⟩ₖ ∈ f₂ → ⟨x, 1⟩ₖ ∈ f₁ by grind
        grind
      · grind
  · let F : V := {p ∈ ℘ X ×ˢ (2 ^ X) ; ∃ f s, p = ⟨s, f⟩ₖ ∧ ∀ x, ⟨x, 1⟩ₖ ∈ f ↔ x ∈ s}
    refine ⟨F, ?_, ?_⟩
    · apply mem_function.intro
      · simp [F]
      · intro s hs
        have hs : s ⊆ X := by simpa using hs
        let f : V := {p ∈ X ×ˢ 2 ; ∃ x, (x ∈ s → p = ⟨x, 1⟩ₖ) ∧ (x ∉ s → p = ⟨x, 0⟩ₖ)}
        have kp1_mem_f : ∀ x, ⟨x, 1⟩ₖ ∈ f ↔ x ∈ s := by
          intro x
          have : x ∈ s → x ∈ X := fun hx ↦ hs _ hx
          simp only [mem_sep_iff, kpair_mem_iff, mem_two_iff, one_ne_zero, or_true, and_true,
            kpair_iff, and_false, imp_false, not_not, f]; grind
        have f_func : f ∈ (2 ^ X : V) := by
          apply mem_function.intro (by simp [f])
          intro x hx
          by_cases hxS : x ∈ s
          · apply ExistsUnique.intro 1
            · simp only [mem_sep_iff, kpair_mem_iff, hx, mem_two_iff, one_ne_zero, or_true, and_self,
              kpair_iff, and_true, and_false, imp_false, not_not, true_and, f]; grind
            · intro i hi
              simp [f, hx] at hi
              grind only
          · apply ExistsUnique.intro 0
            · simp only [mem_sep_iff, kpair_mem_iff, hx, mem_two_iff, zero_ne_one, or_false,
              and_self, kpair_iff, and_false, imp_false, and_true, true_and, f]; grind
            · intro i hi
              simp [f, hx] at hi
              grind only
        apply ExistsUnique.intro f ?_ ?_
        · simp [F, hs, kp1_mem_f, f_func]
        · intro g hg
          have : (s ⊆ X ∧ g ∈ (2 ^ X : V)) ∧ ∀ x, ⟨x, 1⟩ₖ ∈ g ↔ x ∈ s := by simpa [F] using hg
          rcases this with ⟨⟨_, g_func⟩, Hg⟩
          apply function_ext g_func f_func
          intro x hx i hi
          rcases show i = 0 ∨ i = 1 by simpa using hi with (rfl | rfl)
          · suffices ⟨x, 1⟩ₖ ∈ f → ⟨x, 1⟩ₖ ∈ g by grind
            grind
          · grind
    · intro s₁ s₂ f h₁ h₂
      have : (s₁ ⊆ X ∧ f ∈ (2 ^ X : V)) ∧ ∀ x, ⟨x, 1⟩ₖ ∈ f ↔ x ∈ s₁ := by simpa [F] using h₁
      have : (s₂ ⊆ X ∧ f ∈ (2 ^ X : V)) ∧ ∀ x, ⟨x, 1⟩ₖ ∈ f ↔ x ∈ s₂ := by simpa [F] using h₂
      ext z; grind

end LO.FirstOrder.SetTheory
