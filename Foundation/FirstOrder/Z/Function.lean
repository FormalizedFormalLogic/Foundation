import Foundation.FirstOrder.Z.Basic

/-!
# Relations and functions in Zermelo set theory
-/

namespace LO.Zermelo

open FirstOrder SetTheory

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

@[simp, grind =] lemma domain_insert {x y R : V} : domain (Insert.insert (⟨x, y⟩ₖ) R) = Insert.insert x (domain R) := by
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

@[simp, grind =] lemma range_insert {x y R : V} : range (Insert.insert (⟨x, y⟩ₖ) R) = Insert.insert y (range R) := by
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

lemma function_subset_power_prod (X Y : V) : Y ^ X ⊆ ℘ (X ×ˢ Y) := fun f hf ↦ by simpa using subset_prod_of_mem_function hf

lemma exists_unique_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃! y, ⟨x, y⟩ₖ ∈ f := mem_function_iff.mp h |>.2

lemma exists_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : ∀ x ∈ X, ∃ y ∈ Y, ⟨x, y⟩ₖ ∈ f := by
  intro x hx
  rcases (exists_unique_of_mem_function h x hx).exists with ⟨y, hy⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using subset_prod_of_mem_function h _ hy
  exact ⟨y, this.2, hy⟩

lemma domain_eq_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : domain f = X := by
  ext x
  suffices (∃ y, ⟨x, y⟩ₖ ∈ f) ↔ x ∈ X by simpa [mem_domain_iff]
  constructor
  · rintro ⟨y, hxy⟩
    have : x ∈ X ∧ y ∈ Y := by simpa using subset_prod_of_mem_function h _ hxy
    exact this.1
  · intro hx
    rcases exists_of_mem_function h x hx with ⟨y, hy⟩
    exact ⟨y, hy.2⟩

lemma range_subset_of_mem_function {f X Y : V} (h : f ∈ Y ^ X) : range f ⊆ Y := by
  intro y hy
  have : ∃ x, ⟨x, y⟩ₖ ∈ f := by simpa [mem_range_iff] using hy
  rcases this with ⟨x, hxy⟩
  have : x ∈ X ∧ y ∈ Y := by simpa using subset_prod_of_mem_function h _ hxy
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

def insert (f x y : V) (hx : x ∉ domain f) [hf : IsFunction f] : IsFunction (Insert.insert (⟨x, y⟩ₖ) f) := by
  refine ⟨Insert.insert x (domain f), Insert.insert y (range f), ?_⟩
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

@[simp] instance (x y : V) : IsFunction ({⟨x, y⟩ₖ} : V) := by simpa using insert ∅ x y (by simp)

end IsFunction

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

/-! ### Cardinality comparison -/

def CardLE (X Y : V) : Prop := ∃ f ∈ Y ^ X, Injective f

scoped instance : LE V := ⟨CardLE⟩

lemma cardLE_of_subset {X Y : V} (h : X ⊆ Y) : X ≤ Y :=
  ⟨identity X, mem_function_of_mem_function_of_subset (identity_mem_function X) h, by simp⟩

@[simp] lemma cardLE_empty (X : V) : ∅ ≤ X := cardLE_of_subset (by simp)

@[simp, refl] lemma CardLE.refl (X : V) : X ≤ X := cardLE_of_subset (by simp)

@[trans] lemma CardLE.trans {X Y Z : V} : X ≤ Y → Y ≤ Z → X ≤ Z := by
  rintro ⟨f, hf, f_inj⟩
  rintro ⟨g, hg, g_inj⟩
  refine ⟨compose f g, compose_function hf hg, compose_injective f_inj g_inj⟩

instance : Preorder V where
  le_refl := CardLE.refl
  le_trans _ _ _ := CardLE.trans

lemma cardLE_def {X Y : V} : X ≤ Y ↔ ∃ f ∈ Y ^ X, Injective f := by rfl

lemma cardLT_def {X Y : V} : X < Y ↔ X ≤ Y ∧ ¬Y ≤ X := by rfl

def CardLE.dfn : Semisentence ℒₛₑₜ 2 := f“X Y. ∃ f ∈ !function.dfn Y X, !Injective.dfn f”

instance CardLE.defined : ℒₛₑₜ-relation[V] (· ≤ ·) via dfn := ⟨fun v ↦ by simp [cardLE_def, dfn]⟩

instance CardLE.definable : ℒₛₑₜ-relation[V] (· ≤ ·) := defined.to_definable

def CardLT.dfn : Semisentence ℒₛₑₜ 2 := “X Y. !CardLE.dfn X Y ∧ ¬!CardLE.dfn Y X”

instance CardLT.defined : ℒₛₑₜ-relation[V] (· < ·) via dfn := ⟨fun v ↦ by simp [cardLT_def, dfn]⟩

instance CardLT.definable : ℒₛₑₜ-relation[V] (· < ·) := defined.to_definable

def CardEQ (X Y : V) : Prop := X ≤ Y ∧ Y ≤ X

infix:60 " ≋ " => CardEQ

def CardEQ.dfn : Semisentence ℒₛₑₜ 2 := “X Y. !CardLE.dfn X Y ∧ !CardLE.dfn Y X”

instance CardEQ.defined : ℒₛₑₜ-relation[V] (· ≋ ·) via dfn := ⟨fun v ↦ by simp [CardEQ, dfn]⟩

instance CardEQ.definable : ℒₛₑₜ-relation[V] (· ≋ ·) := defined.to_definable

@[simp, refl] lemma CardEQ.refl (X : V) : X ≋ X := ⟨by rfl, by rfl⟩

@[simp, symm] lemma CardEQ.symm {X Y : V} : X ≋ Y → Y ≋ X := fun e ↦ ⟨e.2, e.1⟩

end LO.Zermelo
