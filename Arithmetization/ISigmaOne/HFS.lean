import Arithmetization.ISigmaOne.Bit
import Arithmetization.Vorspiel.ExistsUnique

/-!

# Hereditary Finite Set Theory in $\mathsf{I} \Sigma_1$

-/

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

@[simp] lemma susbset_insert (x a : M) : a ⊆ insert x a := by intro z hz; simp [hz]

@[simp] lemma bitRemove_susbset (x a : M) : bitRemove x a ⊆ a := by intro z; simp

lemma lt_of_mem_dom {x y m : M} (h : ⟪x, y⟫ ∈ m) : x < m := lt_of_le_of_lt (by simp) (lt_of_mem h)

lemma lt_of_mem_rng {x y m : M} (h : ⟪x, y⟫ ∈ m) : y < m := lt_of_le_of_lt (by simp) (lt_of_mem h)

section sUnion

lemma sUnion_exists_unique (s : M) :
    ∃! u : M, ∀ x, (x ∈ u ↔ ∃ t ∈ s, x ∈ t) := by
  have : 𝚺₁-Predicate fun x ↦ ∃ t ∈ s, x ∈ t := by definability
  exact finite_comprehension₁! this
    ⟨s, fun i ↦ by
      rintro ⟨t, ht, hi⟩; exact lt_trans _ _ _ (lt_of_mem hi) (lt_of_mem ht)⟩

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
      exact h x (lt_of_lt_of_le (lt_trans _ _ _ (lt_of_mem hx) (lt_of_mem hc)) (by simp)) |>.mpr ⟨c, hc, hx⟩⟩

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

private lemma isMapping_iff {m : M} : IsMapping m ↔ ∃ d ≤ 2 * m, d = domain m ∧ ∀ x ∈ d, ∃ y < m, ⟪x, y⟫ ∈ m ∧ ∀ y' < m, ⟪x, y'⟫ ∈ m → y' = y :=
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

end mapping

section seq

def Seq (s : M) : Prop := IsMapping s ∧ ∃ l, domain s = under l

def Seq.isMapping {s : M} (h : Seq s) : IsMapping s := h.1

private lemma seq_iff (s : M) : Seq s ↔ IsMapping s ∧ ∃ l ≤ 2 * s, ∃ d ≤ 2 * s, d = domain s ∧ d = under l :=
  ⟨by rintro ⟨hs, l, h⟩
      exact ⟨hs, l, (by
      calc
        l ≤ domain s := by simp [h]
        _ ≤ 2 * s    := by simp), ⟨domain s , by simp,  rfl, h⟩⟩,
   by rintro ⟨hs, l, _, _, _, rfl, h⟩; exact ⟨hs, l, h⟩⟩

def _root_.LO.FirstOrder.Arith.seqDef : 𝚺₀-Semisentence 1 := .mkSigma
  “s | !isMappingDef s ∧ ∃ l <⁺ 2 * s, ∃ d <⁺ 2 * s, !domainDef d s ∧ !underDef d l” (by simp)

lemma seq_defined : 𝚺₀-Predicate (Seq : M → Prop) via seqDef := by
  intro v; simp [seqDef, seq_iff]

@[simp] lemma seq_defined_iff (v) :
    Semiformula.Evalbm M v seqDef.val ↔ Seq (v 0) := seq_defined.df.iff v

instance seq_definable : 𝚺₀-Predicate (Seq : M → Prop) := Defined.to_definable _ seq_defined

@[simp, definability] instance seq_definable' (Γ) : Γ-Predicate (Seq : M → Prop) := .of_zero seq_definable _

section

open Lean PrettyPrinter Delaborator

syntax ":Seq " first_order_term : first_order_formula

scoped macro_rules
  | `(“ $binders* | :Seq $t:first_order_term ”) =>
    `(“ $binders* | !seqDef.val $t ”)

end

lemma lh_exists_uniq (s : M) : ∃! l, (Seq s → domain s = under l) ∧ (¬Seq s → l = 0) := by
  by_cases h : Seq s
  · rcases h with ⟨h, l, hl⟩
    exact ExistsUnique.intro l
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
  · simp [h]

def lh (s : M) : M := Classical.choose! (lh_exists_uniq s)

lemma lh_prop (s : M) : (Seq s → domain s = under (lh s)) ∧ (¬Seq s → lh s = 0) := Classical.choose!_spec (lh_exists_uniq s)

lemma lh_prop_of_not_seq {s : M} (h : ¬Seq s) : lh s = 0 := (lh_prop s).2 h

lemma Seq.domain_eq {s : M} (h : Seq s) : domain s = under (lh s) := (Model.lh_prop s).1 h

@[simp] lemma lh_bound (s : M) : lh s ≤ 2 * s := by
  by_cases hs : Seq s
  · calc
      lh s ≤ under (lh s) := le_under _
      _    ≤ 2 * s        := by simp [←hs.domain_eq]
  · simp [lh_prop_of_not_seq hs]

private lemma lh_graph (l s : M) : l = lh s ↔ (Seq s → ∃ d ≤ 2 * s, d = domain s ∧ d = under l) ∧ (¬Seq s → l = 0) :=
  ⟨by
    rintro rfl
    by_cases Hs : Seq s <;> simp [Hs, ←Seq.domain_eq, lh_prop_of_not_seq], by
    rintro ⟨h, hn⟩
    by_cases Hs : Seq s
    · rcases h Hs with ⟨_, _, rfl, h⟩; simpa [h] using Hs.domain_eq
    · simp [lh_prop_of_not_seq Hs, hn Hs]⟩

def _root_.LO.FirstOrder.Arith.lhDef : 𝚺₀-Semisentence 2 := .mkSigma
  “l s | (!seqDef s → ∃ d <⁺ 2 * s, !domainDef d s ∧ !underDef d l) ∧ (¬!seqDef s → l = 0)” (by simp)

lemma lh_defined : 𝚺₀-Function₁ (lh : M → M) via lhDef := by
  intro v; simp [lhDef, -exists_eq_right_right, lh_graph]

@[simp] lemma lh_defined_iff (v) :
    Semiformula.Evalbm M v lhDef.val ↔ v 0 = lh (v 1) := lh_defined.df.iff v

instance lh_definable : 𝚺₀-Function₁ (lh : M → M) := Defined.to_definable _ lh_defined

instance lh_definable' (Γ) : Γ-Function₁ (lh : M → M) := .of_zero lh_definable _

instance : Bounded₁ ℒₒᵣ (lh : M → M) := ⟨‘x | 2 * x’, fun _ ↦ by simp⟩

lemma Seq.exists {s : M} (h : Seq s) {x : M} (hx : x < lh s) : ∃ y, ⟪x, y⟫ ∈ s := h.isMapping x (by simpa [h.domain_eq] using hx) |>.exists

lemma Seq.nth_exists_uniq {s : M} (h : Seq s) {x : M} (hx : x < lh s) : ∃! y, ⟪x, y⟫ ∈ s := h.isMapping x (by simpa [h.domain_eq] using hx)

def Seq.nth {s : M} (h : Seq s) {x : M} (hx : x < lh s) : M := Classical.choose! (h.nth_exists_uniq hx)

@[simp] lemma Seq.nth_mem {s : M} (h : Seq s) {x : M} (hx : x < lh s) :
    ⟪x, h.nth hx⟫ ∈ s := Classical.choose!_spec (h.nth_exists_uniq hx)

lemma Seq.nth_uniq {s : M} (h : Seq s) {x y : M} (hx : x < lh s) (hy : ⟪x, y⟫ ∈ s) : y = h.nth hx :=
    (h.nth_exists_uniq hx).unique hy (by simp)

@[simp] lemma Seq.nth_lt {s : M} (h : Seq s) {x} (hx : x < lh s) : h.nth hx < s := lt_of_mem_rng (h.nth_mem hx)

lemma Seq.lt_lh_iff {s : M} (h : Seq s) {i} : i < lh s ↔ i ∈ domain s := by simp [h.domain_eq]

lemma Seq.lt_lh_of_mem {s : M} (h : Seq s) {i x} (hix : ⟪i, x⟫ ∈ s) : i < lh s := by simp [h.lt_lh_iff, mem_domain_iff]; exact ⟨x, hix⟩

def seqCons (s x : M) : M := insert ⟪lh s, x⟫ s

-- infixr:67 " ::ˢ " => seqCons

infixr:67 " ⁀' " => seqCons

@[simp] lemma seq_empty : Seq (∅ : M) := ⟨by simp, 0, by simp⟩

@[simp] lemma lh_empty : lh (∅ : M) = 0 := by
  have : under (lh ∅ : M) = under 0 := by simpa using Eq.symm <| Seq.domain_eq (M := M) (s := ∅) (by simp)
  exact under_inj.mp this

@[simp] lemma Seq.subset_seqCons (s x : M) : s ⊆ s ⁀' x := by simp [seqCons]

lemma Seq.lt_seqCons {s} (hs : Seq s) (x : M) : s < s ⁀' x :=
  lt_iff_le_and_ne.mpr <| ⟨le_of_subset <| by simp, by
    simp [seqCons]; intro A
    have : ⟪lh s, x⟫ ∈ s := by simpa [←A] using mem_insert ⟪lh s, x⟫ s
    simpa using hs.lt_lh_of_mem this⟩

@[simp] lemma Seq.mem_seqCons (s x : M) : ⟪lh s, x⟫ ∈ s ⁀' x := by simp [seqCons]

protected lemma Seq.seqCons {s : M} (h : Seq s) (x : M) : Seq (s ⁀' x) :=
  ⟨h.isMapping.insert (by simp [h.domain_eq]), lh s + 1, by simp [seqCons, h.domain_eq]⟩

@[simp] lemma Seq.lh_seqCons (x : M) {s} (h : Seq s) : lh (s ⁀' x) = lh s + 1 := by
  have : under (lh s + 1) = under (lh (s ⁀' x)) := by
    simpa [seqCons, h.domain_eq] using (h.seqCons x).domain_eq
  exact Eq.symm <| under_inj.mp this

lemma mem_seqCons_iff {i x z s : M} : ⟪i, x⟫ ∈ s ⁀' z ↔ (i = lh s ∧ x = z) ∨ ⟪i, x⟫ ∈ s := by simp [seqCons]

@[simp] lemma lh_mem_seqCons (s z : M) : ⟪lh s, z⟫ ∈ s ⁀' z := by simp [seqCons]

@[simp] lemma lh_mem_seqCons_iff {s x z : M} (H : Seq s) : ⟪lh s, x⟫ ∈ s ⁀' z ↔ x = z := by
  simp [seqCons]
  intro h; have := H.lt_lh_of_mem h; simp at this

lemma Seq.mem_seqCons_iff_of_lt {s x z : M} (hi : i < lh s) : ⟪i, x⟫ ∈ s ⁀' z ↔ ⟪i, x⟫ ∈ s := by
  simp [seqCons, hi]
  rintro rfl; simp at hi

section

lemma seqCons_graph (t x s : M) :
    t = s ⁀' x ↔ ∃ l ≤ 2 * s, l = lh s ∧ ∃ p ≤ (2 * s + x + 1)^2, p = ⟪l, x⟫ ∧ t = insert p s :=
  ⟨by rintro rfl
      exact ⟨lh s, by simp[lt_succ_iff_le], rfl, ⟪lh s, x⟫,
        le_trans (pair_le_pair_left (by simp) x) (pair_polybound (2 * s) x), rfl, by rfl⟩,
   by rintro ⟨l, _, rfl, p, _, rfl, rfl⟩; rfl⟩

def _root_.LO.FirstOrder.Arith.seqConsDef : 𝚺₀-Semisentence 3 := .mkSigma
  “t s x | ∃ l <⁺ 2 * s, !lhDef l s ∧ ∃ p <⁺ (2 * s + x + 1)², !pairDef p l x ∧ !insertDef t p s” (by simp)

lemma seqCons_defined : 𝚺₀-Function₂ (seqCons : M → M → M) via seqConsDef := by
  intro v; simp [seqConsDef, seqCons_graph]

@[simp] lemma seqCons_defined_iff (v) :
    Semiformula.Evalbm M v seqConsDef.val ↔ v 0 = v 1 ⁀' v 2 := seqCons_defined.df.iff v

instance seqCons_definable : 𝚺₀-Function₂ (seqCons : M → M → M) := Defined.to_definable _ seqCons_defined

instance seqCons_definable' (Γ) : Γ-Function₂ (seqCons : M → M → M) := .of_zero seqCons_definable _

end

lemma domain_bitRemove_of_isMapping_of_mem {x y s : M} (hs : IsMapping s) (hxy : ⟪x, y⟫ ∈ s) :
    domain (bitRemove ⟪x, y⟫ s) = bitRemove x (domain s) := by
  apply mem_ext; simp [mem_domain_iff]; intro x₁
  constructor
  · rintro ⟨y₁, hy₁, hx₁y₁⟩; exact ⟨by rintro rfl; exact hy₁ rfl (hs.uniq hx₁y₁ hxy), y₁, hx₁y₁⟩
  · intro ⟨hx, y₁, hx₁y₁⟩
    exact ⟨y₁, by intro _; contradiction, hx₁y₁⟩

lemma Seq.eq_of_eq_of_subset {s₁ s₂ : M} (H₁ : Seq s₁) (H₂ : Seq s₂)
    (hl : lh s₁ = lh s₂) (h : s₁ ⊆ s₂) : s₁ = s₂ := by
  apply mem_ext; intro u
  constructor
  · intro hu; exact h hu
  · intro hu
    have : π₁ u < lh s₁ := by simpa [hl] using H₂.lt_lh_of_mem (show ⟪π₁ u, π₂ u⟫ ∈ s₂ from by simpa using hu)
    have : ∃ y, ⟪π₁ u, y⟫ ∈ s₁ := H₁.exists this
    rcases this with ⟨y, hy⟩
    have : y = π₂ u := H₂.isMapping.uniq (h hy) (show ⟪π₁ u, π₂ u⟫ ∈ s₂ from by simpa using hu)
    rcases this with rfl
    simpa using hy

lemma subset_pair {s t : M} (h : ∀ i x, ⟪i, x⟫ ∈ s → ⟪i, x⟫ ∈ t) : s ⊆ t := by
  intro u hu
  simpa using h (π₁ u) (π₂ u) (by simpa using hu)

@[simp] lemma Seq.seqCons_ext {a₁ a₂ s₁ s₂ : M} (H₁ : Seq s₁) (H₂ : Seq s₂) :
    s₁ ⁀' a₁ = s₂ ⁀' a₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intro h
      have hs₁s₂ : lh s₁ = lh s₂ := by simpa [H₁, H₂] using congr_arg lh h
      have hs₁ : ⟪lh s₁, a₁⟫ ∈ s₂ ⁀' a₂ := by simpa [h] using lh_mem_seqCons s₁ a₁
      have hs₂ : ⟪lh s₁, a₂⟫ ∈ s₂ ⁀' a₂ := by simp [hs₁s₂]
      have ha₁a₂ : a₁ = a₂ := (H₂.seqCons a₂).isMapping.uniq hs₁ hs₂
      have : s₁ ⊆ s₂ := subset_pair <| by
        intro i x hix
        have : i = lh s₂ ∧ x = a₂ ∨ ⟪i, x⟫ ∈ s₂ := by simpa [mem_seqCons_iff, h] using Seq.subset_seqCons s₁ a₁ hix
        rcases this with (⟨rfl, rfl⟩ | hix₂)
        · have := H₁.lt_lh_of_mem hix; simp [hs₁s₂] at this
        · assumption
      exact ⟨ha₁a₂, H₁.eq_of_eq_of_subset H₂ hs₁s₂ this⟩,
   by rintro ⟨rfl, rfl⟩; rfl⟩

/-- TODO: move to Lemmata.lean-/
lemma ne_zero_iff_one_le {a : M} : a ≠ 0 ↔ 1 ≤ a := Iff.trans pos_iff_ne_zero.symm (pos_iff_one_le (a := a))

lemma Seq.cases_iff {s : M} : Seq s ↔ s = ∅ ∨ ∃ x s', Seq s' ∧ s = s' ⁀' x := ⟨fun h ↦ by
  by_cases hs : lh s = 0
  · left
    simpa [hs] using h.domain_eq
  · right
    let i := lh s - 1
    have hi : i < lh s := pred_lt_self_of_pos (pos_iff_ne_zero.mpr hs)
    have lhs_eq : lh s = i + 1 := Eq.symm <| tsub_add_cancel_of_le <| ne_zero_iff_one_le.mp hs
    let s' := bitRemove ⟪i, h.nth hi⟫ s
    have his : ⟪i, h.nth hi⟫ ∈ s := h.nth_mem hi
    have hdoms' : domain s' = under i := by
      simp only [domain_bitRemove_of_isMapping_of_mem h.isMapping his, h.domain_eq, s']
      apply mem_ext
      simp [lhs_eq, and_or_left]
      intro j hj; exact ne_of_lt hj
    have hs' : Seq s' := ⟨ h.isMapping.of_subset (by simp [s']), i, hdoms' ⟩
    have hs'i : lh s' = i := by simpa [hs'.domain_eq] using hdoms'
    exact ⟨h.nth hi, s', hs', mem_ext <| fun v ↦ by
      simp only [seqCons, hs'i, mem_bitInsert_iff]
      simp [s']
      by_cases hv : v = ⟪i, h.nth hi⟫ <;> simp [hv]⟩,
  by  rintro (rfl | ⟨x, s', hs', rfl⟩)
      · simp
      · exact hs'.seqCons x⟩

alias ⟨Seq.cases, _⟩ := Seq.cases_iff

@[elab_as_elim]
theorem seq_induction (Γ) {P : M → Prop} (hP : DefinablePred ℒₒᵣ (Γ, 1) P)
  (hnil : P ∅) (hcons : ∀ s x, Seq s → P s → P (s ⁀' x)) :
    ∀ {s : M}, Seq s → P s := by
  intro s sseq
  induction s using order_induction_h_iSigmaOne
  · exact Γ
  · definability
  case ind s ih =>
    have : s = ∅ ∨ ∃ x s', Seq s' ∧ s = s' ⁀' x := sseq.cases
    rcases this with (rfl | ⟨x, s, hs, rfl⟩)
    · exact hnil
    · exact hcons s x hs (ih s (hs.lt_seqCons x) hs)

/-- `!⟨x, y, z, ...⟩` notation for `Seq` -/
syntax (name := vecNotation) "!⟨" term,* "⟩" : term

macro_rules
  | `(!⟨$term:term, $terms:term,*⟩) => `(seqCons !⟨$terms,*⟩ $term)
  | `(!⟨$term:term⟩) => `(seqCons ∅ $term)
  | `(!⟨⟩) => `(∅)

@[app_unexpander seqCons]
def vecConsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !⟨$term2, $terms,*⟩) => `(!⟨$term, $term2, $terms,*⟩)
  | `($_ $term !⟨$term2⟩) => `(!⟨$term, $term2⟩)
  | `($_ $term ∅) => `(!⟨$term⟩)
  | _ => throw ()

@[simp] lemma singleton_seq (x : M) : Seq !⟨x⟩ := by apply Seq.seqCons; simp

section seqMap

variable {f : M → M} (hf : 𝚺₁-Function₁ f)

lemma Seq.seqMap_exists {s : M} (Hs : Seq s) :
    ∃ t, Seq t ∧ lh t = lh s ∧ ∀ i x, ⟪i, x⟫ ∈ s → ⟪i, f x⟫ ∈ t := by
  suffices ∃ t, Seq t ∧ lh t = lh s ∧ ∀ i < lh s, ∀ x < s, ⟪i, x⟫ ∈ s → ⟪i, f x⟫ ∈ t
  by  rcases this with ⟨t, Ht, hts, h⟩
      exact ⟨t, Ht, hts, fun i x hx ↦ h i (Hs.lt_lh_of_mem hx) x (lt_of_mem_rng hx) hx⟩
  revert Hs
  apply @seq_induction M _ _ _ _ _ _ 𝚺
  · definability
  case hnil =>
    exact ⟨∅, by simp⟩
  case hcons =>
    intro s x Hs ⟨t, Ht, hts, ih⟩
    exact ⟨t ⁀' f x, Ht.seqCons (f x), by simp [Hs, Ht, hts], by
      simp [Hs, Ht]
      intro i hi z _ hz
      have : i ≤ lh s := lt_succ_iff_le.mp hi
      rcases this with (rfl | hi)
      · have : z = x := by simpa [Hs] using hz
        simp [this, ←hts, Ht]
      · have : ⟪i, f z⟫ ∈ t ⁀' f x ↔ ⟪i, f z⟫ ∈ t := mem_seqCons_iff_of_lt (x := f z) (z := f x) (by simpa [hts] using hi)
        rw [this]
        have : ⟪i, z⟫ ∈ s := mem_seqCons_iff_of_lt hi |>.mp hz
        exact ih i hi z (lt_of_mem_rng this) this ⟩

lemma seqMap_existsUnique (s : M) (Hs : Seq s) :
    ∃! t, Seq t ∧ lh t = lh s ∧ ∀ i x, ⟪i, x⟫ ∈ s → ⟪i, f x⟫ ∈ t := by
  rcases Hs.seqMap_exists hf with ⟨t, Ht, hts, h⟩
  apply ExistsUnique.intro t ⟨Ht, hts, h⟩
  rintro t' ⟨Ht', ht's, h'⟩
  apply Ht'.eq_of_eq_of_subset Ht (by simp [hts, ht's])
  intro u hu
  have : π₁ u < lh s := by simpa [←ht's] using Ht'.lt_lh_of_mem (show ⟪π₁ u, π₂ u⟫ ∈ t' from by simpa using hu)
  have : ∃ y, ⟪π₁ u, y⟫ ∈ s := Hs.exists this
  rcases this with ⟨y, hy⟩
  have : f y = π₂ u := Ht'.isMapping.uniq (h' _ _ hy) (show ⟪π₁ u, π₂ u⟫ ∈ t' from by simpa using hu)
  simpa [this] using h _ _ hy

def seqMap (s : M) : M := Classical.extendedChoose! (seqMap_existsUnique hf) 0 s

lemma Seq.seqMap_spec' {s : M} (H : Seq s) :
    Seq (seqMap hf s) ∧ lh (seqMap hf s) = lh s ∧ ∀ i x, ⟪i, x⟫ ∈ s → ⟪i, f x⟫ ∈ seqMap hf s :=
  Classical.extendedchoose!_spec (seqMap_existsUnique hf) 0 H

@[simp] lemma seqMap_spec_of_not_seq {s : M} (H : ¬Seq s) :
    seqMap hf s = 0 :=
  Classical.extendedchoose!_spec_not (seqMap_existsUnique hf) 0 H

variable {hf} {s : M} (H : Seq s)

@[simp] protected lemma Seq.seqMap : Seq (seqMap hf s) := H.seqMap_spec' hf |>.1

@[simp] lemma Seq.seqMap_lh_eq : lh (seqMap hf s) = lh s := H.seqMap_spec' hf |>.2.1

lemma Seq.seqMap_spec {i x : M} : ⟪i, x⟫ ∈ s → ⟪i, f x⟫ ∈ seqMap hf s := H.seqMap_spec' hf |>.2.2 i x

lemma Seq.mem_seqMap_iff {i y : M} : ⟪i, y⟫ ∈ seqMap hf s ↔ ∃ x, f x = y ∧ ⟪i, x⟫ ∈ s :=
  ⟨by intro hu
      have : i < lh s := by simpa [H] using H.seqMap.lt_lh_of_mem hu
      have : ∃ x, ⟪i, x⟫ ∈ s := H.exists this
      rcases this with ⟨x, hx⟩
      exact ⟨x, H.seqMap.isMapping.uniq (H.seqMap_spec hx) hu, hx⟩,
   by rintro ⟨x, rfl, hx⟩; exact H.seqMap_spec hx⟩

lemma seqMap_graph (t s : M) :
    t = seqMap hf s ↔
    (Seq s → Seq t ∧ (∃ l ≤ 2 * s, l = lh s ∧ l = lh t) ∧ ∀ i < s, ∀ x < s, ⟪i, x⟫ ∈ s → ∃ y < t, y = f x ∧ ⟪i, y⟫ ∈ t) ∧
    (¬Seq s → t = 0) :=
  ⟨by rintro rfl;
      by_cases H : Seq s <;> simp only [H, Seq.seqMap, lt_succ_iff_le, Seq.seqMap_lh_eq, and_self,
        exists_eq_right, lh_bound, true_and, forall_true_left, not_true_eq_false, IsEmpty.forall_iff, and_true,
        not_false_eq_true, H, seqMap_spec_of_not_seq, forall_true_left]
      intro i _ x _ hix
      have : ⟪i, f x⟫ ∈ seqMap hf s := H.seqMap_spec hix
      exact ⟨f x, lt_of_mem_rng this, rfl, this⟩,
   by by_cases H : Seq s <;>
        simp only [H, lt_succ_iff_le, exists_eq_right_right, forall_true_left,
          not_true_eq_false, IsEmpty.forall_iff, and_true, and_imp]
      intro Ht _ hl h
      apply Classical.extendedChoose!_uniq
      · exact H
      · exact ⟨Ht, hl, by intro i x hi; rcases h i (lt_of_mem_dom hi) x (lt_of_mem_rng hi) hi with ⟨_, _, rfl, h⟩; exact h⟩
      · simp [H]⟩

end seqMap

section seqMap₀

variable (p : HSemisentence ℒₒᵣ 2 𝚺₀)

def _root_.LO.FirstOrder.Arith.seqMap₀Def : 𝚺₀-Semisentence 2 := .mkSigma
  “t s |
    (:Seq s → :Seq t ∧ (∃ l <⁺ 2 * s, !lhDef l s ∧ !lhDef l t) ∧ ∀ i < s, ∀ x < s, i ~[s] x → ∃ y < t, !p y x ∧ i ~[t] y) ∧
    (¬:Seq s → t = 0)” (by simp)

variable {p} {f : M → M} (hf : 𝚺₀-Function₁ f via p)

lemma seqMap₀_defined : 𝚺₀-Function₁ (seqMap (f := f) (Definable.of_zero hf.to_definable _) : M → M) via (seqMap₀Def p) := by
  intro v; simp [seqMap₀Def, seqMap_graph, hf.df.iff]

end seqMap₀

end seq

end LO.FirstOrder.Arith.Model

end
