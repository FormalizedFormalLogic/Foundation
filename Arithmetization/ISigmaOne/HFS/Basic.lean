import Arithmetization.ISigmaOne.Bit
import Arithmetization.Vorspiel.ExistsUnique

/-!

# Hereditary Finite Set Theory in $\mathsf{I} \Sigma_1$

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

@[simp] lemma susbset_insert (x a : M) : a ⊆ insert x a := by intro z hz; simp [hz]

@[simp] lemma bitRemove_susbset (x a : M) : bitRemove x a ⊆ a := by intro z; simp

lemma lt_of_mem_dom {x y m : M} (h : ⟪x, y⟫ ∈ m) : x < m := lt_of_le_of_lt (by simp) (lt_of_mem h)

lemma lt_of_mem_rng {x y m : M} (h : ⟪x, y⟫ ∈ m) : y < m := lt_of_le_of_lt (by simp) (lt_of_mem h)

section under

@[simp] lemma under_subset_under_of_le {i j : M} : under i ⊆ under j ↔ i ≤ j :=
  ⟨by intro h; by_contra hij
      have : j < i := by simpa using hij
      simpa using h (mem_under_iff.mpr this),
   by intro hij x
      simp only [mem_under_iff]
      intro hx
      exact lt_of_lt_of_le hx hij⟩

end under

section sUnion

lemma sUnion_exists_unique (s : M) :
    ∃! u : M, ∀ x, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) := by
  have : 𝚺₁-Predicate fun x ↦ ∃ t ∈ s, x ∈ t := by definability
  exact finite_comprehension₁! this
    ⟨s, fun i ↦ by
      rintro ⟨t, ht, hi⟩; exact lt_trans (lt_of_mem hi) (lt_of_mem ht)⟩

def sUnion (s : M) : M := Classical.choose! (sUnion_exists_unique s)

prefix:80 "⋃ʰᶠ " => sUnion

@[simp] lemma mem_sUnion_iff {a b : M} : a ∈ ⋃ʰᶠ b ↔ ∃ c ∈ b, a ∈ c := Classical.choose!_spec (sUnion_exists_unique b) a

@[simp] lemma sUnion_empty : (⋃ʰᶠ ∅ : M) = ∅ := mem_ext (by simp)

lemma sUnion_lt_of_pos {a : M} (ha : 0 < a) : ⋃ʰᶠ a < a :=
  lt_of_lt_log ha (by simp; intro i x hx hi; exact lt_of_lt_of_le (lt_of_mem hi) (le_log_of_mem hx))

@[simp] lemma sUnion_le (a : M) : ⋃ʰᶠ a ≤ a := by
  rcases zero_le a with (rfl | pos)
  · simp [←emptyset_def]
  · exact le_of_lt (sUnion_lt_of_pos pos)

lemma sUnion_graph {u s : M} : u = ⋃ʰᶠ s ↔ ∀ x < u + s, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) :=
  ⟨by rintro rfl; simp, by
    intro h; apply mem_ext
    intro x; simp
    constructor
    · intro hx
      exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · rintro ⟨c, hc, hx⟩
      exact h x (lt_of_lt_of_le (lt_trans (lt_of_mem hx) (lt_of_mem hc)) (by simp)) |>.mpr ⟨c, hc, hx⟩⟩

def _root_.LO.FirstOrder.Arith.sUnionDef : 𝚺₀-Semisentence 2 := .mkSigma
  “u s | ∀ x < u + s, (x ∈ u ↔ ∃ t ∈' s, x ∈ t)” (by simp)

lemma sUnion_defined : 𝚺₀-Function₁ ((⋃ʰᶠ ·) : M → M) via sUnionDef := by
  intro v; simp [sUnionDef, sUnion_graph]

@[simp] lemma sUnion_defined_iff (v) :
    Semiformula.Evalbm M v sUnionDef.val ↔ v 0 = ⋃ʰᶠ v 1 := sUnion_defined.df.iff v

instance sUnion_definable : DefinableFunction₁ ℒₒᵣ 𝚺₀ ((⋃ʰᶠ ·) : M → M) := Defined.to_definable _ sUnion_defined

instance sUnion_definable' (Γ) : DefinableFunction₁ ℒₒᵣ Γ ((⋃ʰᶠ ·) : M → M) := .of_zero sUnion_definable _

end sUnion

section union

def union (a b : M) : M := ⋃ʰᶠ {a, b}

scoped instance : Union M := ⟨union⟩

@[simp] lemma mem_cup_iff {a b c : M} : a ∈ b ∪ c ↔ a ∈ b ∨ a ∈ c := by simp [Union.union, union]

private lemma union_graph {u s t : M} : u = s ∪ t ↔ ∀ x < u + s + t, (x ∈ u ↔ x ∈ s ∨ x ∈ t) :=
  ⟨by rintro rfl; simp, by
    intro h; apply mem_ext
    intro x; simp
    constructor
    · intro hx; exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp [add_assoc])) |>.mp hx
    · rintro (hx | hx)
      · exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp )) |>.mpr (Or.inl hx)
      · exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp )) |>.mpr (Or.inr hx)⟩

def _root_.LO.FirstOrder.Arith.unionDef : 𝚺₀-Semisentence 3 := .mkSigma
  “∀[#0 < #1 + #2 + #3](#0 ∈ #1 ↔ #0 ∈ #2 ∨ #0 ∈ #3)” (by simp)

lemma union_defined : 𝚺₀-Function₂ ((· ∪ ·) : M → M → M) via unionDef := by
  intro v; simp [unionDef, union_graph]

@[simp] lemma union_defined_iff (v) :
    Semiformula.Evalbm M v unionDef.val ↔ v 0 = v 1 ∪ v 2 := union_defined.df.iff v

instance union_definable : DefinableFunction₂ ℒₒᵣ 𝚺₀ ((· ∪ ·) : M → M → M) := Defined.to_definable _ union_defined

instance union_definable' (Γ) : DefinableFunction₂ ℒₒᵣ Γ ((· ∪ ·) : M → M → M) := .of_zero union_definable _

lemma insert_eq_union_singleton (a s : M) : insert a s = {a} ∪ s := mem_ext (fun x ↦ by simp)

@[simp] lemma union_polybound (a b : M) : a ∪ b ≤ 2 * (a + b) := le_iff_lt_succ.mpr
  <| lt_of_lt_log (by simp) (by
    simp; rintro i (hi | hi)
    · calc
        i ≤ log (a + b) := le_trans (le_log_of_mem hi) (log_monotone (by simp))
        _ < log (2 * (a + b)) := by simp [log_two_mul_of_pos (show 0 < a + b from by simp [pos_of_nonempty hi])]
        _ ≤ log (2 * (a + b) + 1) := log_monotone (by simp)
    · calc
        i ≤ log (a + b) := le_trans (le_log_of_mem hi) (log_monotone (by simp))
        _ < log (2 * (a + b)) := by simp [log_two_mul_of_pos (show 0 < a + b from by simp [pos_of_nonempty hi])]
        _ ≤ log (2 * (a + b) + 1) := log_monotone (by simp))

instance : Bounded₂ ℒₒᵣ ((· ∪ ·) : M → M → M) := ⟨‘x y | 2 * (x + y)’, fun _ ↦ by simp⟩

lemma union_comm (a b : M) : a ∪ b = b ∪ a := mem_ext (by simp [or_comm])

@[simp] lemma union_succ_union_left (a b : M) : a ⊆ a ∪ b := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_right (a b : M) : b ⊆ a ∪ b := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_union_left (a b c : M) : a ⊆ a ∪ b ∪ c := by intro x hx; simp [hx]

@[simp] lemma union_succ_union_union_right (a b c : M) : b ⊆ a ∪ b ∪ c := by intro x hx; simp [hx]

end union

section sInter

lemma sInter_exists_unique (s : M) :
    ∃! u : M, ∀ x, (x ∈ u ↔ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t) := by
  have : 𝚺₁-Predicate fun x ↦ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t := by definability
  exact finite_comprehension₁! this
    ⟨s, fun i ↦ by
      rintro ⟨hs, h⟩
      have : log s ∈ s := log_mem_of_pos <| pos_iff_ne_zero.mpr hs
      exact _root_.trans (lt_of_mem <| h (log s) this) (lt_of_mem this)⟩

def sInter (s : M) : M := Classical.choose! (sInter_exists_unique s)

prefix:80 "⋂ʰᶠ " => sInter

lemma mem_sInter_iff {x s : M} : x ∈ ⋂ʰᶠ s ↔ s ≠ ∅ ∧ ∀ t ∈ s, x ∈ t := Classical.choose!_spec (sInter_exists_unique s) x

@[simp] lemma mem_sInter_iff_empty : ⋂ʰᶠ (∅ : M) = ∅ := mem_ext (by simp [mem_sInter_iff])

lemma mem_sInter_iff_of_pos {x s : M} (h : s ≠ ∅) : x ∈ ⋂ʰᶠ s ↔ ∀ t ∈ s, x ∈ t := by simp [mem_sInter_iff, h]

end sInter

section inter

def inter (a b : M) : M := ⋂ʰᶠ {a, b}

scoped instance : Inter M := ⟨inter⟩

@[simp] lemma mem_inter_iff {a b c : M} : a ∈ b ∩ c ↔ a ∈ b ∧ a ∈ c := by
  simp [Inter.inter, inter, mem_sInter_iff_of_pos (s := {b, c}) (nonempty_iff.mpr ⟨b, by simp⟩)]

lemma inter_comm (a b : M) : a ∩ b = b ∩ a := mem_ext (by simp [and_comm])

lemma inter_eq_self_of_subset {a b : M} (h : a ⊆ b) :
  a ∩ b = a := mem_ext (by simp; intro i hi; exact h hi)

end inter

section product

lemma product_exists_unique (a b : M) :
    ∃! u : M, ∀ x, (x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫) := by
  have : 𝚺₁-Predicate fun x ↦ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫ := by definability
  exact finite_comprehension₁! this
    ⟨⟪log a, log b⟫ + 1, fun i ↦ by
      rintro ⟨y, hy, z, hz, rfl⟩
      simp [lt_succ_iff_le]
      exact pair_le_pair (le_log_of_mem hy) (le_log_of_mem hz)⟩

def product (a b : M) : M := Classical.choose! (product_exists_unique a b)

infixl:60 " ×ʰᶠ " => product

lemma mem_product_iff {x a b : M} : x ∈ a ×ʰᶠ b ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫ := Classical.choose!_spec (product_exists_unique a b) x

lemma mem_product_iff' {x a b : M} : x ∈ a ×ʰᶠ b ↔ π₁ x ∈ a ∧ π₂ x ∈ b := by
  simp [mem_product_iff]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩; simp [*]
  · rintro ⟨h₁, h₂⟩; exact ⟨π₁ x, h₁, π₂ x, h₂, by simp⟩

@[simp] lemma pair_mem_product_iff {x y a b : M} : ⟪x, y⟫ ∈ a ×ʰᶠ b ↔ x ∈ a ∧ y ∈ b := by simp [mem_product_iff']

lemma pair_mem_product {x y a b : M} (hx : x ∈ a) (hy : y ∈ b) : ⟪x, y⟫ ∈ a ×ʰᶠ b := by
  simp [mem_product_iff]; exact ⟨hx, hy⟩

private lemma product_graph {u a b : M} : u = a ×ʰᶠ b ↔ ∀ x < u + (a + b + 1) ^ 2, (x ∈ u ↔ ∃ y ∈ a, ∃ z ∈ b, x = ⟪y, z⟫) :=
  ⟨by rintro rfl x _; simp [mem_product_iff], by
    intro h
    apply mem_ext; intro x; simp [mem_product_iff]
    constructor
    · intro hx; exact h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · rintro ⟨y, hy, z, hz, rfl⟩
      exact h ⟪y, z⟫ (lt_of_lt_of_le (pair_lt_pair (lt_of_mem hy) (lt_of_mem hz))
        (le_trans (pair_polybound a b) <| by simp)) |>.mpr ⟨y, hy, z, hz, rfl⟩⟩

def _root_.LO.FirstOrder.Arith.productDef : 𝚺₀-Semisentence 3 := .mkSigma
  “u a b | ∀ x < u + (a + b + 1)², (x ∈ u ↔ ∃ y ∈' a, ∃ z ∈' b, !pairDef x y z)” (by simp)

lemma product_defined : 𝚺₀-Function₂ ((· ×ʰᶠ ·) : M → M → M) via productDef := by
  intro v; simp [productDef, product_graph]

@[simp] lemma product_defined_iff (v) :
    Semiformula.Evalbm M v productDef.val ↔ v 0 = v 1 ×ʰᶠ v 2 := product_defined.df.iff v

instance product_definable : DefinableFunction₂ ℒₒᵣ 𝚺₀ ((· ×ʰᶠ ·) : M → M → M) := Defined.to_definable _ product_defined

instance product_definable' (Γ) : DefinableFunction₂ ℒₒᵣ Γ ((· ×ʰᶠ ·) : M → M → M) := .of_zero product_definable _

end product

section domain

lemma domain_exists_unique (s : M) :
    ∃! d : M, ∀ x, x ∈ d ↔ ∃ y, ⟪x, y⟫ ∈ s := by
  have : 𝚺₁-Predicate fun x ↦ ∃ y, ⟪x, y⟫ ∈ s :=
    DefinablePred.of_iff (fun x ↦ ∃ y < s, ⟪x, y⟫ ∈ s)
      (fun x ↦ ⟨by rintro ⟨y, hy⟩; exact ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), hy⟩,
                by rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩)
      (by definability)
  exact finite_comprehension₁!
    this
    (⟨s, fun x ↦ by rintro ⟨y, hy⟩; exact lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy)⟩)

def domain (s : M) : M := Classical.choose! (domain_exists_unique s)

lemma mem_domain_iff {x s : M} : x ∈ domain s ↔ ∃ y, ⟪x, y⟫ ∈ s := Classical.choose!_spec (domain_exists_unique s) x

private lemma domain_graph {u s : M} : u = domain s ↔ ∀ x < u + s, (x ∈ u ↔ ∃ y < s, ∃ z ∈ s, z = ⟪x, y⟫) :=
  ⟨by rintro rfl x _; simp [mem_domain_iff]
      exact ⟨by rintro ⟨y, hy⟩; exact ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), hy⟩, by
        rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩,
   by intro h; apply mem_ext; intro x; simp [mem_domain_iff]
      constructor
      · intro hx
        rcases h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx with ⟨y, _, _, hy, rfl⟩; exact ⟨y, hy⟩
      · rintro ⟨y, hy⟩
        exact h x (lt_of_lt_of_le (lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy)) (by simp))
          |>.mpr ⟨y, lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hy), _, hy, rfl⟩⟩

def _root_.LO.FirstOrder.Arith.domainDef : 𝚺₀-Semisentence 2 := .mkSigma
  “u s | ∀ x < u + s, (x ∈ u ↔ ∃ y < s, ∃ z ∈' s, !pairDef z x y)” (by simp)

lemma domain_defined : 𝚺₀-Function₁ (domain : M → M) via domainDef := by
  intro v; simp [domainDef, domain_graph]

@[simp] lemma domain_defined_iff (v) :
    Semiformula.Evalbm M v domainDef.val ↔ v 0 = domain (v 1) := domain_defined.df.iff v

instance domain_definable : DefinableFunction₁ ℒₒᵣ 𝚺₀ (domain : M → M) := Defined.to_definable _ domain_defined

instance domain_definable' (Γ) : DefinableFunction₁ ℒₒᵣ Γ (domain : M → M) := .of_zero domain_definable _

@[simp] lemma domain_empty : domain (∅ : M) = ∅ := mem_ext (by simp [mem_domain_iff])

@[simp] lemma domain_union (a b : M) : domain (a ∪ b) = domain a ∪ domain b := mem_ext (by
  simp [mem_domain_iff]
  intro x; constructor
  · rintro ⟨y, (hy | hy)⟩
    · left; exact ⟨y, hy⟩
    · right; exact ⟨y, hy⟩
  · rintro (⟨y, hy⟩ | ⟨y, hy⟩)
    · exact ⟨y, Or.inl hy⟩
    · exact ⟨y, Or.inr hy⟩)

@[simp] lemma domain_singleton (x y : M) : (domain {⟪x, y⟫} : M) = {x} := mem_ext (by simp [mem_domain_iff])

@[simp] lemma domain_insert (x y s : M) : domain (insert ⟪x, y⟫ s) = insert x (domain s) := by simp [insert_eq_union_singleton]

@[simp] lemma domain_bound (s : M) : domain s ≤ 2 * s := le_iff_lt_succ.mpr
  <| lt_of_lt_log (by simp) (by
    simp [mem_domain_iff]; intro i x hix
    exact lt_of_le_of_lt (le_trans (le_pair_left i x) (le_log_of_mem hix))
      (by simp [log_two_mul_add_one_of_pos (pos_of_nonempty hix)]))

instance : Bounded₁ ℒₒᵣ (domain : M → M) := ⟨‘x | 2 * x’, fun _ ↦ by simp⟩

lemma mem_domain_of_pair_mem {x y s : M} (h : ⟪x, y⟫ ∈ s) : x ∈ domain s := mem_domain_iff.mpr ⟨y, h⟩

lemma domain_subset_domain_of_subset {s t : M} (h : s ⊆ t) : domain s ⊆ domain t := by
  intro x hx
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  exact mem_domain_iff.mpr ⟨y, h hy⟩

@[simp] lemma domain_eq_empty_iff_eq_empty {s : M} : domain s = ∅ ↔ s = ∅ :=
  ⟨by simp [isempty_iff, mem_domain_iff]
      intro h x hx
      exact h (π₁ x) (π₂ x) (by simpa using hx), by rintro rfl; simp⟩

/-
@[simp] lemma domain_le_self {P : M → Prop}
    (hempty : P ∅) (hinsert : ∀ s x, x ∉ s → P s → P (insert x s)) : ∀ x, P x := by {  }

@[simp] lemma domain_le_self (P : M → Prop) (s : M) : domain s ≤ s := le_iff_lt_succ.mpr
-/

end domain

section range

/-
lemma range_exists_unique (s : M) :
    ∃! r : M, ∀ y, y ∈ r ↔ ∃ x, ⟪x, y⟫ ∈ s := by
  have : 𝚺₁-Predicate fun y ↦ ∃ x, ⟪x, y⟫ ∈ s :=
    DefinablePred.of_iff (fun y ↦ ∃ x < s, ⟪x, y⟫ ∈ s)
      (fun y ↦ ⟨by rintro ⟨x, hy⟩; exact ⟨x, lt_of_le_of_lt (le_pair_left x y) (lt_of_mem hy), hy⟩,
                by rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩⟩)
      (by definability)
  exact finite_comprehension₁!
    this
    (⟨s, fun y ↦ by rintro ⟨x, hx⟩; exact lt_of_le_of_lt (le_pair_right x y) (lt_of_mem hx)⟩)
-/

end range

section disjoint

def Disjoint (s t : M) : Prop := s ∩ t = ∅

lemma Disjoint.iff {s t : M} : Disjoint s t ↔ ∀ x, x ∉ s ∨ x ∉ t := by simp [Disjoint, isempty_iff, imp_iff_not_or]

lemma Disjoint.not_of_mem {s t x : M} (hs : x ∈ s) (ht : x ∈ t) : ¬Disjoint s t := by
  simp [Disjoint.iff, not_or]; exact ⟨x, hs, ht⟩

lemma Disjoint.symm {s t : M} (h : Disjoint s t) : Disjoint t s := by simpa [Disjoint, inter_comm t s] using h

@[simp] lemma Disjoint.singleton_iff {a : M} : Disjoint ({a} : M) s ↔ a ∉ s := by simp [Disjoint, isempty_iff]

end disjoint

section mapping

def IsMapping (m : M) : Prop := ∀ x ∈ domain m, ∃! y, ⟪x, y⟫ ∈ m

section

private lemma isMapping_iff {m : M} :
    IsMapping m ↔ ∃ d ≤ 2 * m, d = domain m ∧ ∀ x ∈ d, ∃ y < m, ⟪x, y⟫ ∈ m ∧ ∀ y' < m, ⟪x, y'⟫ ∈ m → y' = y :=
  ⟨by intro hm
      exact ⟨domain m, by simp, rfl, fun x hx ↦ by
        rcases hm x hx with ⟨y, hy, uniq⟩
        exact ⟨y, lt_of_mem_rng hy, hy, fun y' _ h' ↦ uniq y' h'⟩⟩,
   by rintro ⟨_, _, rfl, h⟩ x hx
      rcases h x hx with ⟨y, _, hxy, h⟩
      exact ExistsUnique.intro y hxy (fun y' hxy' ↦ h y' (lt_of_mem_rng hxy') hxy')⟩

def _root_.LO.FirstOrder.Arith.isMappingDef : 𝚺₀-Semisentence 1 := .mkSigma
  “m | ∃ d <⁺ 2 * m, !domainDef d m ∧ ∀ x ∈' d, ∃ y < m, x ~[m] y ∧ ∀ y' < m, x ~[m] y' → y' = y” (by simp)

lemma isMapping_defined : 𝚺₀-Predicate (IsMapping : M → Prop) via isMappingDef := by
  intro v; simp [isMappingDef, isMapping_iff, lt_succ_iff_le]

@[simp] lemma isMapping_defined_iff (v) :
    Semiformula.Evalbm M v isMappingDef.val ↔ IsMapping (v 0) := isMapping_defined.df.iff v

instance isMapping_definable : 𝚺₀-Predicate (IsMapping : M → Prop) := Defined.to_definable _ isMapping_defined

instance isMapping_definable' (Γ) : Γ-Predicate (IsMapping : M → Prop) := .of_zero isMapping_definable _

end

lemma IsMapping.get_exists_uniq {m : M} (h : IsMapping m) {x : M} (hx : x ∈ domain m) : ∃! y, ⟪x, y⟫ ∈ m := h x hx

def IsMapping.get {m : M} (h : IsMapping m) {x : M} (hx : x ∈ domain m) : M := Classical.choose! (IsMapping.get_exists_uniq h hx)

@[simp] lemma IsMapping.get_mem {m : M} (h : IsMapping m) {x : M} (hx : x ∈ domain m) :
    ⟪x, h.get hx⟫ ∈ m := Classical.choose!_spec (IsMapping.get_exists_uniq h hx)

lemma IsMapping.get_uniq {m : M} (h : IsMapping m) {x : M} (hx : x ∈ domain m) (hy : ⟪x, y⟫ ∈ m) : y = h.get hx :=
    (h x hx).unique hy (by simp)

@[simp] lemma IsMapping.empty : IsMapping (∅ : M) := by intro x; simp

lemma IsMapping.union_of_disjoint_domain {m₁ m₂ : M}
    (h₁ : IsMapping m₁) (h₂ : IsMapping m₂) (disjoint : Disjoint (domain m₁) (domain m₂)) : IsMapping (m₁ ∪ m₂) := by
  intro x
  simp; rintro (hx | hx)
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

@[simp] lemma IsMapping.singleton (x y : M) : IsMapping ({⟪x, y⟫} : M) := by
  intro x; simp; rintro rfl; exact ExistsUnique.intro y (by simp) (by rintro _ ⟨_, rfl⟩; simp)

lemma IsMapping.insert {x y m : M}
    (h : IsMapping m) (disjoint : x ∉ domain m) : IsMapping (insert ⟪x, y⟫ m) := by
  simp [insert_eq_union_singleton]
  exact IsMapping.union_of_disjoint_domain (by simp) h (by simpa)

lemma IsMapping.of_subset {m m' : M} (h : IsMapping m) (ss : m' ⊆ m) : IsMapping m' := fun x hx ↦ by
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  have : ∃! y, ⟪x, y⟫ ∈ m := h x (domain_subset_domain_of_subset ss hx)
  exact ExistsUnique.intro y hy (fun y' hy' ↦ this.unique (ss hy') (ss hy))

lemma IsMapping.uniq {m x y₁ y₂ : M} (h : IsMapping m) : ⟪x, y₁⟫ ∈ m → ⟪x, y₂⟫ ∈ m → y₁ = y₂ := fun h₁ h₂ ↦
  h x (mem_domain_iff.mpr ⟨y₁, h₁⟩) |>.unique h₁ h₂


end mapping

/-! ### Restriction of mapping -/

section restriction

lemma restr_exists_unique (f s : M) :
    ∃! g : M, ∀ x, (x ∈ g ↔ x ∈ f ∧ π₁ x ∈ s) := by
  have : 𝚺₁-Predicate fun x ↦ x ∈ f ∧ π₁ x ∈ s := by definability
  exact finite_comprehension₁! this
    ⟨f, fun i ↦ by rintro ⟨hi, _⟩; exact lt_of_mem hi⟩

def restr (f s : M) : M := Classical.choose! (restr_exists_unique f s)

scoped infix:80 " ↾ " => restr

lemma mem_restr_iff {x f s : M} : x ∈ f ↾ s ↔ x ∈ f ∧ π₁ x ∈ s := Classical.choose!_spec (restr_exists_unique f s) x

@[simp] lemma pair_mem_restr_iff {x y f s : M} : ⟪x, y⟫ ∈ f ↾ s ↔ ⟪x, y⟫ ∈ f ∧ x ∈ s := by simp [mem_restr_iff]

@[simp] lemma restr_empty (f : M) : f ↾ ∅ = ∅ := mem_ext (by simp [mem_restr_iff])

@[simp] lemma restr_subset_self (f s : M) : f ↾ s ⊆ f := fun _ hx ↦ (mem_restr_iff.mp hx).1

@[simp] lemma restr_le_self (f s : M) : f ↾ s ≤ f := le_of_subset (by simp)

lemma IsMapping.restr {m : M} (h : IsMapping m) (s : M) : IsMapping (m ↾ s) := h.of_subset (by simp)

lemma domain_restr (f s : M) : domain (f ↾ s) = domain f ∩ s :=
  mem_ext (by simp [mem_domain_iff, pair_mem_restr_iff, exists_and_right, mem_inter_iff])

lemma domain_restr_of_subset_domain {f s : M} (h : s ⊆ domain f) : domain (f ↾ s) = s := by
  simp [domain_restr, inter_comm, inter_eq_self_of_subset h]

end restriction

theorem insert_induction {P : M → Prop} (hP : (Γ, 1)-Predicate P)
    (hempty : P ∅) (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  order_induction_hh ℒₒᵣ Γ 1 hP <| by
    intro s IH
    rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · exact hempty
    · simpa [insert_remove hx] using
        hinsert x (bitRemove x s) (by simp) (IH _ (bitRemove_lt_of_mem hx))

@[elab_as_elim]
lemma insert_induction_sigmaOne {P : M → Prop} (hP : 𝚺₁-Predicate P)
    (hempty : P ∅) (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  insert_induction hP hempty hinsert

@[elab_as_elim]
lemma insert_induction_piOne {P : M → Prop} (hP : 𝚷₁-Predicate P)
    (hempty : P ∅) (hinsert : ∀ a s, a ∉ s → P s → P (insert a s)) : ∀ s, P s :=
  insert_induction hP hempty hinsert

theorem sigmaOne_skolem {R : M → M → Prop} (hP : 𝚺₁-Relation R) {s : M}
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
      have : ∃ b, R a b := H a (by simp [subset_iff] at hu; exact hu.1)
      rcases this with ⟨b, hb⟩
      let f' := insert ⟪a, b⟫ f
      exact ⟨f', mf.insert (by simpa using ha), by simp [f'], by
        intro x y hxy
        rcases (show x = a ∧ y = b ∨ ⟪x, y⟫ ∈ f by simpa [f'] using hxy) with (⟨rfl, rfl⟩ | h)
        · exact hb
        · exact hf x y h⟩
  exact this s (by rfl)

end LO.Arith

end
