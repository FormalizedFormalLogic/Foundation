module

public import Foundation.FirstOrder.Arithmetic.Exponential

@[expose] public section
/-!

# Hereditary Finite Set Theory in $\mathsf{I}\Sigma_1$

-/

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

@[simp] lemma susbset_insert (x a : V) : a ⊆ insert x a := by intro z hz; simp [hz]

@[simp] lemma bitRemove_susbset (x a : V) : bitRemove x a ⊆ a := by intro z; simp

lemma lt_of_mem_dom {x y m : V} (h : ⟪x, y⟫ ∈ m) : x < m := lt_of_le_of_lt (by simp) (lt_of_mem h)

lemma lt_of_mem_rng {x y m : V} (h : ⟪x, y⟫ ∈ m) : y < m := lt_of_le_of_lt (by simp) (lt_of_mem h)

lemma insert_subset_insert_of_subset {a b : V} (x : V) (h : a ⊆ b) : insert x a ⊆ insert x b := by
  intro z hz
  rcases mem_bitInsert_iff.mp hz with (rfl | hz)
  · simp
  · simp [h hz]

section under

@[simp] lemma under_subset_under_of_le {i j : V} : under i ⊆ under j ↔ i ≤ j :=
  ⟨by intro h; by_contra hij
      have : j < i := by simpa using hij
      simpa using h (mem_under_iff.mpr this),
   by intro hij x
      simp only [mem_under_iff]
      intro hx
      exact lt_of_lt_of_le hx hij⟩

end under

section sUnion

lemma sUnion_exists_unique (s : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) := by
  have : 𝚺₁-Predicate fun x ↦ ∃ t ∈ s, x ∈ t := by definability
  exact finite_comprehension₁! this
    ⟨s, fun i ↦ by
      rintro ⟨t, ht, hi⟩; exact lt_trans (lt_of_mem hi) (lt_of_mem ht)⟩

noncomputable def sUnion (s : V) : V := Classical.choose! (sUnion_exists_unique s)

prefix:80 "⋃ʰᶠ " => sUnion

@[simp] lemma mem_sUnion_iff {a b : V} : a ∈ ⋃ʰᶠ b ↔ ∃ c ∈ b, a ∈ c := Classical.choose!_spec (sUnion_exists_unique b) a

@[simp] lemma sUnion_empty : (⋃ʰᶠ ∅ : V) = ∅ := mem_ext (by simp)

lemma sUnion_lt_of_pos {a : V} (ha : 0 < a) : ⋃ʰᶠ a < a :=
  lt_of_lt_log ha <| by
    suffices ∀ i x, x ∈ a → i ∈ x → i < log a by simpa
    intro i x hx hi
    exact lt_of_lt_of_le (lt_of_mem hi) (le_log_of_mem hx)

@[simp] lemma sUnion_le (a : V) : ⋃ʰᶠ a ≤ a := by
  rcases Arithmetic.zero_le a with (rfl | pos)
  · simp [←emptyset_def]
  · exact le_of_lt (sUnion_lt_of_pos pos)

lemma sUnion_graph {u s : V} : u = ⋃ʰᶠ s ↔ ∀ x < u + s, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) :=
  ⟨by rintro rfl; simp, by
    intro h; apply mem_ext
    intro x
    suffices x ∈ u ↔ ∃ c ∈ s, x ∈ c by simpa
    constructor
    · intro hx
      exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · rintro ⟨c, hc, hx⟩
      exact h x (lt_of_lt_of_le (lt_trans (lt_of_mem hx) (lt_of_mem hc)) (by simp)) |>.mpr ⟨c, hc, hx⟩⟩

def _root_.LO.FirstOrder.Arithmetic.sUnionDef : 𝚺₀.Semisentence 2 := .mkSigma
  “u s. ∀ x < u + s, (x ∈ u ↔ ∃ t ∈' s, x ∈ t)”

instance sUnion_defined : 𝚺₀-Function₁[V] sUnion via sUnionDef := .mk fun v ↦ by simp [sUnionDef, sUnion_graph]

instance sUnion_definable : 𝚺₀-Function₁[V] sUnion := sUnion_defined.to_definable

instance sUnion_definable' (ℌ : HierarchySymbol) : ℌ-Function₁[V] sUnion := sUnion_definable.of_zero

end sUnion

section union

noncomputable def union (a b : V) : V := ⋃ʰᶠ {a, b}

noncomputable scoped instance : Union V := ⟨union⟩

@[simp] lemma mem_cup_iff {a b c : V} : a ∈ b ∪ c ↔ a ∈ b ∨ a ∈ c := by simp [Union.union, union]

private lemma union_graph {u s t : V} : u = s ∪ t ↔ ∀ x < u + s + t, (x ∈ u ↔ x ∈ s ∨ x ∈ t) :=
  ⟨by rintro rfl; simp, by
    intro h; apply mem_ext
    intro x
    suffices x ∈ u ↔ x ∈ s ∨ x ∈ t by simpa
    constructor
    · intro hx; exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp [add_assoc])) |>.mp hx
    · rintro (hx | hx)
      · exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp )) |>.mpr (Or.inl hx)
      · exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp )) |>.mpr (Or.inr hx)⟩

def _root_.LO.FirstOrder.Arithmetic.unionDef : 𝚺₀.Semisentence 3 := .mkSigma
  “∀⁰[#0 < #1 + #2 + #3](#0 ∈ #1 ↔ #0 ∈ #2 ∨ #0 ∈ #3)”

instance union_defined : 𝚺₀-Function₂ ((· ∪ ·) : V → V → V) via unionDef := .mk fun v ↦ by
  simp [unionDef, union_graph]

instance union_definable : 𝚺₀-Function₂ ((· ∪ ·) : V → V → V) := union_defined.to_definable

instance union_definable' (ℌ : HierarchySymbol) : ℌ-Function₂ ((· ∪ ·) : V → V → V) := union_definable.of_zero

lemma insert_eq_union_singleton (a s : V) : insert a s = {a} ∪ s := mem_ext (fun x ↦ by simp)

@[simp] lemma union_polybound (a b : V) : a ∪ b ≤ 2 * (a + b) := by
  suffices ∀ i, i ∈ a ∨ i ∈ b → i < log (2 * (a + b) + 1) from le_iff_lt_succ.mpr <| lt_of_lt_log (by simp) <| by simpa
  rintro i (hi | hi)
  · calc
      i ≤ log (a + b) := le_trans (le_log_of_mem hi) (log_monotone (by simp))
      _ < log (2 * (a + b)) := by simp [log_two_mul_of_pos (show 0 < a + b from by simp [pos_of_nonempty hi])]
      _ ≤ log (2 * (a + b) + 1) := log_monotone (by simp)
  · calc
      i ≤ log (a + b) := le_trans (le_log_of_mem hi) (log_monotone (by simp))
      _ < log (2 * (a + b)) := by simp [log_two_mul_of_pos (show 0 < a + b from by simp [pos_of_nonempty hi])]
      _ ≤ log (2 * (a + b) + 1) := log_monotone (by simp)

instance : Bounded₂ ((· ∪ ·) : V → V → V) := ⟨‘x y. 2 * (x + y)’, fun _ ↦ by simp⟩

lemma union_comm (a b : V) : a ∪ b = b ∪ a := mem_ext (by simp [or_comm])

@[simp] lemma union_succ_union_left (a b : V) : a ⊆ a ∪ b := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_right (a b : V) : b ⊆ a ∪ b := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_union_left (a b c : V) : a ⊆ a ∪ b ∪ c := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_union_right (a b c : V) : b ⊆ a ∪ b ∪ c := by intro x hx; simp [hx]

@[simp] lemma union_empty_eq_right (a : V) : a ∪ ∅ = a := mem_ext <| by simp

@[simp] lemma union_empty_eq_left (a : V) : ∅ ∪ a = a := mem_ext <| by simp

end union

section sInter

lemma sInter_exists_unique (s : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t) := by
  have : 𝚺₁-Predicate fun x ↦ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t := by definability
  exact finite_comprehension₁! this
    ⟨s, fun i ↦ by
      rintro ⟨hs, h⟩
      have : log s ∈ s := log_mem_of_pos <| pos_iff_ne_zero.mpr hs
      exact _root_.trans (lt_of_mem <| h (log s) this) (lt_of_mem this)⟩

noncomputable def sInter (s : V) : V := Classical.choose! (sInter_exists_unique s)

prefix:80 "⋂ʰᶠ " => sInter

lemma mem_sInter_iff {x s : V} : x ∈ ⋂ʰᶠ s ↔ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t := Classical.choose!_spec (sInter_exists_unique s) x

@[simp] lemma mem_sInter_iff_empty : ⋂ʰᶠ (∅ : V) = ∅ := mem_ext (by simp [mem_sInter_iff])

lemma mem_sInter_iff_of_pos {x s : V} (h : s ≠ ∅) : x ∈ ⋂ʰᶠ s ↔ ∀ t ∈ s, x ∈ t := by simp [mem_sInter_iff, h]

end sInter

section inter

noncomputable def inter (a b : V) : V := ⋂ʰᶠ {a, b}

noncomputable scoped instance : Inter V := ⟨inter⟩

@[simp] lemma mem_inter_iff {a b c : V} : a ∈ b ∩ c ↔ a ∈ b ∧ a ∈ c := by
  simp [Inter.inter, inter, mem_sInter_iff_of_pos (s := {b, c}) (nonempty_iff.mpr ⟨b, by simp⟩)]

lemma inter_comm (a b : V) : a ∩ b = b ∩ a := mem_ext (by simp [and_comm])

lemma inter_eq_self_of_subset {a b : V} (h : a ⊆ b) :
  a ∩ b = a := mem_ext (by simpa using fun i hi↦ h hi)

end inter

section product

lemma product_exists_unique (a b : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫) := by
  have : 𝚺₁-Predicate fun x ↦ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫ := by definability
  exact finite_comprehension₁! this
    ⟨⟪log a, log b⟫ + 1, fun i ↦ by
      rintro ⟨y, hy, z, hz, rfl⟩
      simpa [lt_succ_iff_le]
      using pair_le_pair (le_log_of_mem hy) (le_log_of_mem hz)⟩

noncomputable def product (a b : V) : V := Classical.choose! (product_exists_unique a b)

infixl:60 " ×ʰᶠ " => product

lemma mem_product_iff {x a b : V} : x ∈ a ×ʰᶠ b ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫ := Classical.choose!_spec (product_exists_unique a b) x

lemma mem_product_iff' {x a b : V} : x ∈ a ×ʰᶠ b ↔ π₁ x ∈ a ∧ π₂ x ∈ b := by
  suffices (∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫) ↔ π₁ x ∈ a ∧ π₂ x ∈ b by simpa [mem_product_iff]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩; simp [*]
  · rintro ⟨h₁, h₂⟩; exact ⟨π₁ x, h₁, π₂ x, h₂, by simp⟩

@[simp] lemma pair_mem_product_iff {x y a b : V} : ⟪x, y⟫ ∈ a ×ʰᶠ b ↔ x ∈ a ∧ y ∈ b := by simp [mem_product_iff']

lemma pair_mem_product {x y a b : V} (hx : x ∈ a) (hy : y ∈ b) : ⟪x, y⟫ ∈ a ×ʰᶠ b := by
  simpa [mem_product_iff] using ⟨hx, hy⟩

private lemma product_graph {u a b : V} : u = a ×ʰᶠ b ↔ ∀ x < u + (a + b + 1) ^ 2, (x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫) :=
  ⟨by rintro rfl x _; simp [mem_product_iff], by
    intro h
    apply mem_ext; intro x
    suffices x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫ by simpa [mem_product_iff]
    constructor
    · intro hx; exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact h ⟪y, z⟫ (lt_of_lt_of_le (pair_lt_pair (lt_of_mem hy) (lt_of_mem hz))
        (le_trans (pair_polybound a b) <| by simp)) |>.mpr ⟨y, hy, z, hz, rfl⟩⟩

def _root_.LO.FirstOrder.Arithmetic.productDef : 𝚺₀.Semisentence 3 := .mkSigma
  “u a b. ∀ x < u + (a + b + 1)², (x ∈ u ↔ ∃ y ∈' a, ∃ z ∈' b, !pairDef x y z)”

instance product_defined : 𝚺₀-Function₂ ((· ×ʰᶠ ·) : V → V → V) via productDef := .mk fun v ↦ by
  simp [productDef, product_graph]

instance product_definable : 𝚺₀-Function₂ ((· ×ʰᶠ ·) : V → V → V) := product_defined.to_definable

instance product_definable' (ℌ : HierarchySymbol) : ℌ-Function₂ ((· ×ʰᶠ ·) : V → V → V) := product_definable.of_zero

end product

section domain

lemma domain_exists_unique (s : V) :
    ∃! d : V, ∀ x, x ∈ d ↔ ∃ y, ⟪x, y⟫ ∈ s := by
  have : 𝚺₁-Predicate fun x ↦ ∃ y, ⟪x, y⟫ ∈ s :=
    HierarchySymbol.DefinablePred.of_iff (Q := fun x ↦ ∃ y < s, ⟪x, y⟫ ∈ s)
      (by definability)
      (fun x ↦ ⟨by rintro ⟨y, hy⟩; exact ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), hy⟩,
                by rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩)
  exact finite_comprehension₁!
    this
    (⟨s, fun x ↦ by rintro ⟨y, hy⟩; exact lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy)⟩)

noncomputable def domain (s : V) : V := Classical.choose! (domain_exists_unique s)

lemma mem_domain_iff {x s : V} : x ∈ domain s ↔ ∃ y, ⟪x, y⟫ ∈ s := Classical.choose!_spec (domain_exists_unique s) x

private lemma domain_graph {u s : V} : u = domain s ↔ ∀ x < u + s, (x ∈ u ↔ ∃ y < s, ∃ z ∈ s, z = ⟪x, y⟫) := by
  constructor
  · rintro rfl x _
    suffices (∃ y, ⟪x, y⟫ ∈ s) ↔ ∃ y < s, ⟪x, y⟫ ∈ s by simpa [mem_domain_iff]
    exact ⟨by rintro ⟨y, hy⟩; exact ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), hy⟩, by
      rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩
  · intro h; apply mem_ext; intro x
    suffices x ∈ u ↔ ∃ y, ⟪x, y⟫ ∈ s by simpa [mem_domain_iff]
    constructor
    · intro hx
      rcases h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx with ⟨y, _, _, hy, rfl⟩; exact ⟨y, hy⟩
    · rintro ⟨y, hy⟩
      exact h x (lt_of_lt_of_le (lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy)) (by simp))
        |>.mpr ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), _, hy, rfl⟩

def _root_.LO.FirstOrder.Arithmetic.domainDef : 𝚺₀.Semisentence 2 := .mkSigma
  “u s. ∀ x < u + s, (x ∈ u ↔ ∃ y < s, ∃ z ∈' s, !pairDef z x y)”

instance domain_defined : 𝚺₀-Function₁ (domain : V → V) via domainDef := .mk fun v ↦ by simp [domainDef, domain_graph]

instance domain_definable : 𝚺₀-Function₁ (domain : V → V) := domain_defined.to_definable

instance domain_definable' (ℌ : HierarchySymbol) : ℌ-Function₁ (domain : V → V) := domain_definable.of_zero

@[simp] lemma domain_empty : domain (∅ : V) = ∅ := mem_ext (by simp [mem_domain_iff])

@[simp] lemma domain_union (a b : V) : domain (a ∪ b) = domain a ∪ domain b := mem_ext (by
  suffices ∀ i, (∃ y, ⟪i, y⟫ ∈ a ∨ ⟪i, y⟫ ∈ b) ↔ (∃ y, ⟪i, y⟫ ∈ a) ∨ ∃ y, ⟪i, y⟫ ∈ b by simpa [mem_domain_iff]
  intro x; constructor
  · rintro ⟨y, (hy | hy)⟩
    · left; exact ⟨y, hy⟩
    · right; exact ⟨y, hy⟩
  · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
    · exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩)

@[simp] lemma domain_singleton (x y : V) : (domain {⟪x, y⟫} : V) = {x} := mem_ext (by simp [mem_domain_iff])

@[simp] lemma domain_insert (x y s : V) : domain (insert ⟪x, y⟫ s) = insert x (domain s) := by simp [insert_eq_union_singleton]

@[simp] lemma domain_bound (s : V) : domain s ≤ 2 * s := le_iff_lt_succ.mpr
  <| lt_of_lt_log (by simp) (by
    simp only [mem_domain_iff, forall_exists_index]
    intro i x hix
    exact lt_of_le_of_lt (le_trans (le_pair_left i x) (le_log_of_mem hix))
      (by simp [log_two_mul_add_one_of_pos (pos_of_nonempty hix)]))

instance : Bounded₁ (domain : V → V) := ⟨‘x. 2 * x’, fun _ ↦ by simp⟩

lemma mem_domain_of_pair_mem {x y s : V} (h : ⟪x, y⟫ ∈ s) : x ∈ domain s := mem_domain_iff.mpr ⟨y, h⟩

lemma domain_subset_domain_of_subset {s t : V} (h : s ⊆ t) : domain s ⊆ domain t := by
  intro x hx
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  exact mem_domain_iff.mpr ⟨y, h hy⟩

@[simp] lemma domain_eq_empty_iff_eq_empty {s : V} : domain s = ∅ ↔ s = ∅ :=
  ⟨by simp only [isempty_iff, mem_domain_iff, not_exists]
      intro h x hx
      exact h (π₁ x) (π₂ x) (by simpa using hx), by rintro rfl; simp⟩

/-
@[simp] lemma domain_le_self {P : V → Prop}
    (hempty : P ∅) (hinsert : ∀ s x, x ∉ s → P s → P (insert x s)) : ∀ x, P x := by {  }

@[simp] lemma domain_le_self (P : V → Prop) (s : V) : domain s ≤ s := le_iff_lt_succ.mpr
-/

end domain

/-! ### Range -/

section range

lemma range_exists_unique (s : V) :
    ∃! r : V, ∀ y, y ∈ r ↔ ∃ x, ⟪x, y⟫ ∈ s := by
  have : 𝚺₁-Predicate fun y ↦ ∃ x, ⟪x, y⟫ ∈ s :=
    HierarchySymbol.DefinablePred.of_iff (Q := fun y ↦ ∃ x < s, ⟪x, y⟫ ∈ s)
      (by definability)
      (fun y ↦ ⟨by rintro ⟨x, hy⟩; exact ⟨x, lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy), hy⟩,
                by rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩)
  exact finite_comprehension₁!
    this
    (⟨s, fun y ↦ by rintro ⟨x, hx⟩; exact lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hx)⟩)


noncomputable def range (s : V) : V := Classical.choose! (range_exists_unique s)

lemma mem_range_iff {y s : V} : y ∈ range s ↔ ∃ x, ⟪x, y⟫ ∈ s := Classical.choose!_spec (range_exists_unique s) y

private lemma range_graph {s' s : V} : s' = range s ↔ ∀ y < s' + s, (y ∈ s' ↔ ∃ x < s, ∃ z ∈ s, z = ⟪x, y⟫) :=
  ⟨by rintro rfl y _
      suffices (∃ x, ⟪x, y⟫ ∈ s) ↔ ∃ x < s, ⟪x, y⟫ ∈ s by simpa [mem_range_iff]
      exact ⟨by rintro ⟨x, hx⟩; exact ⟨x, lt_of_mem_dom hx, hx⟩, by rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩,
   by intro h
      apply mem_ext
      intro y
      suffices y ∈ s' ↔ ∃ x, ⟪x, y⟫ ∈ s by simpa [mem_range_iff]
      constructor
      · intro hy
        rcases h y (lt_of_lt_of_le (lt_of_mem hy) (by simp)) |>.mp hy with ⟨y, _, _, hy, rfl⟩; exact ⟨y, hy⟩
      · rintro ⟨x, hx⟩
        exact h y (lt_of_lt_of_le (lt_of_mem_rng hx) (by simp))
          |>.mpr ⟨x, lt_of_mem_dom hx, _, hx, rfl⟩⟩

def _root_.LO.FirstOrder.Arithmetic.rangeDef : 𝚺₀.Semisentence 2 := .mkSigma
  “s' s. ∀ y < s' + s, (y ∈ s' ↔ ∃ x < s, ∃ z ∈' s, !pairDef z x y)”

instance range_defined : 𝚺₀-Function₁ (range : V → V) via rangeDef := .mk fun v ↦ by simp [rangeDef, range_graph]

instance range_definable : 𝚺₀-Function₁ (range : V → V) := range_defined.to_definable

instance range_definable' (ℌ : HierarchySymbol) : ℌ-Function₁ (range : V → V) := range_definable.of_zero

@[simp] lemma range_empty : range (∅ : V) = ∅ := mem_ext (by simp [mem_range_iff])

end range

/-! ### Disjoint -/

section disjoint

def Disjoint (s t : V) : Prop := s ∩ t = ∅

lemma Disjoint.iff {s t : V} : Disjoint s t ↔ ∀ x, x ∉ s ∨ x ∉ t := by simp [Disjoint, isempty_iff, imp_iff_not_or]

lemma Disjoint.not_of_mem {s t x : V} (hs : x ∈ s) (ht : x ∈ t) : ¬Disjoint s t := by
  simpa [Disjoint.iff, not_or] using ⟨x, hs, ht⟩

lemma Disjoint.symm {s t : V} (h : Disjoint s t) : Disjoint t s := by simpa [Disjoint, inter_comm t s] using h

@[simp] lemma Disjoint.singleton_iff {a : V} : Disjoint ({a} : V) s ↔ a ∉ s := by simp [Disjoint, isempty_iff]

end disjoint

/-! ### Mapping -/

section mapping

def IsMapping (m : V) : Prop := ∀ x ∈ domain m, ∃! y, ⟪x, y⟫ ∈ m

section

private lemma isMapping_iff {m : V} :
    IsMapping m ↔ ∃ d ≤ 2 * m, d = domain m ∧ ∀ x ∈ d, ∃ y < m, ⟪x, y⟫ ∈ m ∧ ∀ y' < m, ⟪x, y'⟫ ∈ m → y' = y :=
  ⟨by intro hm
      exact ⟨domain m, by simp, rfl, fun x hx ↦ by
        rcases hm x hx with ⟨y, hy, uniq⟩
        exact ⟨y, lt_of_mem_rng hy, hy, fun y' _ h' ↦ uniq y' h'⟩⟩,
   by rintro ⟨_, _, rfl, h⟩ x hx
      rcases h x hx with ⟨y, _, hxy, h⟩
      exact ExistsUnique.intro y hxy (fun y' hxy' ↦ h y' (lt_of_mem_rng hxy') hxy')⟩

def _root_.LO.FirstOrder.Arithmetic.isMappingDef : 𝚺₀.Semisentence 1 := .mkSigma
  “m. ∃ d <⁺ 2 * m, !domainDef d m ∧ ∀ x ∈' d, ∃ y < m, x ∼[m] y ∧ ∀ y' < m, x ∼[m] y' → y' = y”

instance isMapping_defined : 𝚺₀-Predicate (IsMapping : V → Prop) via isMappingDef := .mk <| by
  intro v; simp [isMappingDef, isMapping_iff]

instance isMapping_definable : 𝚺₀-Predicate (IsMapping : V → Prop) := isMapping_defined.to_definable

instance isMapping_definable' (ℌ) : ℌ-Predicate (IsMapping : V → Prop) := isMapping_definable.of_zero

end

lemma IsMapping.get_exists_uniq {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) : ∃! y, ⟪x, y⟫ ∈ m := h x hx

noncomputable def IsMapping.get {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) : V := Classical.choose! (IsMapping.get_exists_uniq h hx)

@[simp] lemma IsMapping.get_mem {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) :
    ⟪x, h.get hx⟫ ∈ m := Classical.choose!_spec (IsMapping.get_exists_uniq h hx)

lemma IsMapping.get_uniq {m : V} (h : IsMapping m) {x : V} (hx : x ∈ domain m) (hy : ⟪x, y⟫ ∈ m) : y = h.get hx :=
    (h x hx).unique hy (by simp)

@[simp] lemma IsMapping.empty : IsMapping (∅ : V) := by intro x; simp

lemma IsMapping.union_of_disjoint_domain {m₁ m₂ : V}
    (h₁ : IsMapping m₁) (h₂ : IsMapping m₂) (disjoint : Disjoint (domain m₁) (domain m₂)) : IsMapping (m₁ ∪ m₂) := by
  intro x
  suffices x ∈ domain m₁ ∨ x ∈ domain m₂ → ∃! y, ⟪x, y⟫ ∈ m₁ ∨ ⟪x, y⟫ ∈ m₂ by simpa
  rintro (hx | hx)
  · exact ExistsUnique.intro (h₁.get hx) (by simp) (by
      intro y
      rintro (hy | hy)
      · exact h₁.get_uniq hx hy
      · by_contra; exact Disjoint.not_of_mem hx (mem_domain_of_pair_mem hy) disjoint)
  · exact ExistsUnique.intro (h₂.get hx) (by simp) (by
      intro y
      rintro (hy | hy)
      · by_contra; exact Disjoint.not_of_mem hx (mem_domain_of_pair_mem hy) disjoint.symm
      · exact h₂.get_uniq hx hy)

@[simp] lemma IsMapping.singleton (x y : V) : IsMapping ({⟪x, y⟫} : V) := by
  intro x; simp only [domain_singleton, mem_singleton_iff, pair_ext_iff]
  rintro rfl; exact ExistsUnique.intro y (by simp) (by rintro _ ⟨_, rfl⟩; simp)

lemma IsMapping.insert {x y m : V}
    (h : IsMapping m) (disjoint : x ∉ domain m) : IsMapping (insert ⟪x, y⟫ m) := by
  simpa [insert_eq_union_singleton]
  using IsMapping.union_of_disjoint_domain (by simp) h (by simpa)

lemma IsMapping.of_subset {m m' : V} (h : IsMapping m) (ss : m' ⊆ m) : IsMapping m' := fun x hx ↦ by
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  have : ∃! y, ⟪x, y⟫ ∈ m := h x (domain_subset_domain_of_subset ss hx)
  exact ExistsUnique.intro y hy (fun y' hy' ↦ this.unique (ss hy') (ss hy))

lemma IsMapping.uniq {m x y₁ y₂ : V} (h : IsMapping m) : ⟪x, y₁⟫ ∈ m → ⟪x, y₂⟫ ∈ m → y₁ = y₂ := fun h₁ h₂ ↦
  h x (mem_domain_iff.mpr ⟨y₁, h₁⟩) |>.unique h₁ h₂

end mapping

/-! ### Restriction of mapping -/

section restriction

lemma restr_exists_unique (f s : V) :
    ∃! g : V, ∀ x, (x ∈ g ↔ x ∈ f ∧ π₁ x ∈ s) := by
  have : 𝚺₁-Predicate fun x ↦ x ∈ f ∧ π₁ x ∈ s := by definability
  exact finite_comprehension₁! this
    ⟨f, fun i ↦ by rintro ⟨hi, _⟩; exact lt_of_mem hi⟩

noncomputable def restr (f s : V) : V := Classical.choose! (restr_exists_unique f s)

scoped infix:80 " ↾ " => restr

lemma mem_restr_iff {x f s : V} : x ∈ f ↾ s ↔ x ∈ f ∧ π₁ x ∈ s := Classical.choose!_spec (restr_exists_unique f s) x

@[simp] lemma pair_mem_restr_iff {x y f s : V} : ⟪x, y⟫ ∈ f ↾ s ↔ ⟪x, y⟫ ∈ f ∧ x ∈ s := by simp [mem_restr_iff]

@[simp] lemma restr_empty (f : V) : f ↾ ∅ = ∅ := mem_ext (by simp [mem_restr_iff])

@[simp] lemma restr_subset_self (f s : V) : f ↾ s ⊆ f := fun _ hx ↦ (mem_restr_iff.mp hx).1

@[simp] lemma restr_le_self (f s : V) : f ↾ s ≤ f := le_of_subset (by simp)

lemma IsMapping.restr {m : V} (h : IsMapping m) (s : V) : IsMapping (m ↾ s) := h.of_subset (by simp)

lemma domain_restr (f s : V) : domain (f ↾ s) = domain f ∩ s :=
  mem_ext (by simp [mem_domain_iff, pair_mem_restr_iff, exists_and_right, mem_inter_iff])

lemma domain_restr_of_subset_domain {f s : V} (h : s ⊆ domain f) : domain (f ↾ s) = s := by
  simp [domain_restr, inter_comm, inter_eq_self_of_subset h]

end restriction

theorem insert_induction {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hempty : P ∅) (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  InductionOnHierarchy.order_induction_sigma Γ 1 hP <| by
    intro s IH
    rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · exact hempty
    · simpa [insert_remove hx] using
        hinsert x (bitRemove x s) (by simp) (IH _ (bitRemove_lt_of_mem hx))

@[elab_as_elim]
lemma insert_induction_sigmaOne {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (hempty : P ∅) (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  insert_induction hP hempty hinsert

@[elab_as_elim]
lemma insert_induction_piOne {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (hempty : P ∅) (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  insert_induction hP hempty hinsert

theorem sigmaOne_skolem {R : V → V → Prop} (hP : 𝚺₁-Relation R) {s : V}
    (H : ∀ x ∈ s, ∃ y, R x y) : ∃ f, IsMapping f ∧ domain f = s ∧ ∀ x y, ⟪x, y⟫ ∈ f → R x y := by
  have : ∀ u, u ⊆ s → ∃ f, IsMapping f ∧ domain f = u ∧ ∀ x y, ⟪x, y⟫ ∈ f → R x y := by
    intro u hu
    induction u using insert_induction_sigmaOne
    · have : 𝚺₁-Predicate fun u ↦ u ⊆ s → ∃ f, IsMapping f ∧ domain f = u ∧ ∀ x < f, ∀ y < f, ⟪x, y⟫ ∈ f → R x y := by definability
      exact this.of_iff <| by
        intro x; apply imp_congr_right <| fun _ ↦ exists_congr <| fun f ↦ and_congr_right
          <| fun _ ↦ and_congr_right <| fun _ ↦
            ⟨fun h x _ y _ hxy ↦ h x y hxy, fun h x y hxy ↦ h x (lt_of_mem_dom hxy) y (lt_of_mem_rng hxy) hxy⟩
    case hempty =>
      exact ⟨∅, by simp⟩
    case hinsert a u ha ih =>
      have : ∃ f, IsMapping f ∧ domain f = u ∧ ∀ x y, ⟪x, y⟫ ∈ f → R x y := ih (subset_trans (susbset_insert a u) hu)
      rcases this with ⟨f, mf, rfl, hf⟩
      have : ∃ b, R a b := H a <| And.left <| by simpa [subset_iff] using hu
      rcases this with ⟨b, hb⟩
      let f' := insert ⟪a, b⟫ f
      exact ⟨f', mf.insert (by simpa using ha), by simp [f'], by
        intro x y hxy
        rcases (show x = a ∧ y = b ∨ ⟪x, y⟫ ∈ f by simpa [f'] using hxy) with (⟨rfl, rfl⟩ | h)
        · exact hb
        · exact hf x y h⟩
  exact this s (by rfl)

theorem sigma₁_replacement {f : V → V} (hf : 𝚺₁-Function₁ f) (s : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = f x := by
  have : ∀ x ∈ s, ∃ y, y = f x := by intro x _; exact ⟨f x, rfl⟩
  have : ∃ F, IsMapping F ∧ domain F = s ∧ ∀ (x y : V), ⟪x, y⟫ ∈ F → y = f x :=
    sigmaOne_skolem (by definability) this
  rcases this with ⟨F, _, rfl, hF⟩
  refine ExistsUnique.intro (range F) ?_ ?_
  · intro y
    simp only [mem_range_iff]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, by simpa [mem_domain_iff] using ⟨y, hx⟩, hF _ _ hx⟩
    · simp only [mem_domain_iff, forall_exists_index, and_imp]
      rintro x y hxy rfl; exact ⟨x, by rcases hF _ _ hxy; exact hxy⟩
  · intro s' hs'
    apply mem_ext; intro y
    suffices (∃ x, (∃ y, ⟪x, y⟫ ∈ F) ∧ y = f x) ↔ ∃ x, ⟪x, y⟫ ∈ F by simpa [hs', mem_domain_iff, mem_range_iff]
    constructor
    · rintro ⟨x, ⟨y, hxy⟩, rfl⟩; exact ⟨x, by rcases hF _ _ hxy; exact hxy⟩
    · rintro ⟨x, hxy⟩; exact ⟨x, ⟨y, hxy⟩, hF _ _ hxy⟩

theorem sigma₁_replacement₂ {f : V → V → V} (hf : 𝚺₁-Function₂ f) (s₁ s₂ : V) :
    ∃! t : V, ∀ y, y ∈ t ↔ ∃ x₁ ∈ s₁, ∃ x₂ ∈ s₂, y = f x₁ x₂ := by
  have : 𝚺₁-Function₁ (fun x ↦ f (π₁ x) (π₂ x)) := by definability
  exact (existsUnique_congr (by
      intro t; apply forall_congr'; intro y; apply iff_congr (by rfl)
      simp only [mem_product_iff']
      constructor
      · rintro ⟨x, ⟨h₁, h₂⟩, rfl⟩; exact ⟨π₁ x, h₁, π₂ x, h₂, by rfl⟩
      · rintro ⟨x₁, h₁, x₂, h₂, rfl⟩; exact ⟨⟪x₁, x₂⟫, by simp [h₁, h₂]⟩)).mp
    (sigma₁_replacement this (s₁ ×ʰᶠ s₂))

section fstIdx

noncomputable def fstIdx (p : V) : V := π₁ (p - 1)

@[simp] lemma fstIdx_le_self (p : V) : fstIdx p ≤ p := le_trans (by simp [fstIdx]) (show p - 1 ≤ p by simp)

def _root_.LO.FirstOrder.Arithmetic.fstIdxDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “n p. ∃ p' <⁺ p, !subDef p' p 1 ∧ !pi₁Def n p'”

instance fstIdx_defined : 𝚺₀-Function₁ (fstIdx : V → V) via fstIdxDef := .mk <| by
  intro v; simp [fstIdxDef, fstIdx]

instance fstIdx_definable : 𝚺₀-Function₁ (fstIdx : V → V) := fstIdx_defined.to_definable

instance fstIdx_definable' (Γ) : Γ-Function₁ (fstIdx : V → V) := fstIdx_definable.of_zero

end fstIdx

section sndIdx

noncomputable def sndIdx (p : V) : V := π₂ (p - 1)

@[simp] lemma sndIdx_le_self (p : V) : sndIdx p ≤ p := le_trans (by simp [sndIdx]) (show p - 1 ≤ p by simp)

def _root_.LO.FirstOrder.Arithmetic.sndIdxDef : 𝚺₀.Semisentence 2 :=
  .mkSigma “n p. ∃ p' <⁺ p, !subDef p' p 1 ∧ !pi₂Def n p'”

instance sndIdx_defined : 𝚺₀-Function₁ (sndIdx : V → V) via sndIdxDef := .mk fun v ↦ by simp [sndIdxDef, sndIdx]

instance sndIdx_definable : 𝚺₀-Function₁ (sndIdx : V → V) := sndIdx_defined.to_definable

instance sndIdx_definable' (Γ) : Γ-Function₁ (sndIdx : V → V) := sndIdx_definable.of_zero

end sndIdx

end LO.FirstOrder.Arithmetic
