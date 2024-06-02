import Arithmetization.ISigmaOne.Bit

/-!

# Hereditary Finite Set Theory in $\mathsf{I} \Sigma_1$

-/

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M]

variable [M ⊧ₘ* 𝐈𝚺₁]

@[simp] lemma susbset_insert (x a : M) : a ⊆ insert x a := by intro z hz; simp [hz]

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
  “∀[#0 < #1 + #2](#0 ∈ #1 ↔ [∃∈ #2](#1 ∈ #0))” (by simp)

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

instance : Bounded₂ ℒₒᵣ ((· ∪ ·) : M → M → M) := ⟨ᵀ“2 * (#0 + #1)”, λ _ ↦ by simp⟩

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
  “∀[#0 < #1 + (#2 + #3 + 1) ^' 2](#0 ∈ #1 ↔ [∃∈ #2][∃∈ #4](!pairDef.val [#2, #1, #0]))” (by simp)

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
  “∀[#0 < #1 + #2](#0 ∈ #1 ↔ ∃[#0 < #3] [∃∈ #3](!pairDef.val [#0, #2, #1]))” (by simp)

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

/-- TODO: prove `domain s ≤ s` -/
@[simp] lemma domain_bound (s : M) : domain s ≤ 2 * s := le_iff_lt_succ.mpr
  <| lt_of_lt_log (by simp) (by
    simp [mem_domain_iff]; intro i x hix
    exact lt_of_le_of_lt (le_trans (le_pair_left i x) (le_log_of_mem hix))
      (by simp [log_two_mul_add_one_of_pos (pos_of_nonempty hix)]))

instance : Bounded₁ ℒₒᵣ (domain : M → M) := ⟨ᵀ“2 * #0”, λ _ ↦ by simp⟩

lemma mem_domain_of_pair_mem {x y s : M} (h : ⟪x, y⟫ ∈ s) : x ∈ domain s := mem_domain_iff.mpr ⟨y, h⟩

lemma domain_subset_domain_of_subset {s t : M} (h : s ⊆ t) : domain s ⊆ domain t := by
  intro x hx
  rcases mem_domain_iff.mp hx with ⟨y, hy⟩
  exact mem_domain_iff.mpr ⟨y, h hy⟩

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

private lemma isMapping_iff {m : M} : IsMapping m ↔ ∃ d ≤ 2 * m, d = domain m ∧ ∀ x ∈ d, ∃ y < m, ⟪x, y⟫ ∈ m ∧ ∀ y' < m, ⟪x, y'⟫ ∈ m → y' = y :=
  ⟨by intro hm
      exact ⟨domain m, by simp, rfl, fun x hx ↦ by
        rcases hm x hx with ⟨y, hy, uniq⟩
        exact ⟨y, lt_of_mem_rng hy, hy, fun y' _ h' ↦ uniq y' h'⟩⟩,
   by rintro ⟨_, _, rfl, h⟩ x hx
      rcases h x hx with ⟨y, _, hxy, h⟩
      exact ExistsUnique.intro y hxy (fun y' hxy' ↦ h y' (lt_of_mem_rng hxy') hxy')⟩

/-
def _root_.LO.FirstOrder.Arith.isMappingDef : 𝚺₀-Semisentence 1 := .mkSigma
  “∃[#0 < 2 * #1 + 1](!domainDef.val [#0, #1] ∧ [∀∈ #0] ∃[#0 < #3](#1 ~[#3] #0 ∧ ∀[#0 < #4](#2 ~[#4] #0 → #0 = #1)))” (by simp)

lemma domain_defindded : 𝚺₀-Function₁ (domain : M → M) via domainDef := by
  intro v; simp [domainDef, domain_graph]

@[simp] lemma length_defined_iff (v) :
    Semiformula.Evalbm M v lengthDef.val ↔ v 0 = ‖v 1‖ := length_defined.df.iff v

instance domain_definable : DefinableFunction₁ ℒₒᵣ 𝚺₀ (domain : M → M) := Defined.to_definable _ domain_defined

instance domain_definable' (Γ) : DefinableFunction₁ ℒₒᵣ Γ (domain : M → M) := .of_zero domain_definable _
-/

end mapping

section seq

def Seq (s : M) : Prop := IsMapping s ∧ ∃ l, domain s = under l

def Seq.isMapping {s : M} (h : Seq s) : IsMapping s := h.1

lemma lh_exists_uniq (s : M) : ∃! l, (Seq s → domain s = under l) ∧ (¬Seq s → l = 0) := by
  by_cases h : Seq s
  · rcases h with ⟨h, l, hl⟩
    exact ExistsUnique.intro l
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
      (by simp [show Seq s from ⟨h, l, hl⟩, hl]; intro y hy; exact Eq.symm <| under_inj hy)
  · simp [h]

def lh (s : M) : M := Classical.choose! (lh_exists_uniq s)

lemma lh_prop (s : M) : (Seq s → domain s = under (lh s)) ∧ (¬Seq s → lh s = 0) := Classical.choose!_spec (lh_exists_uniq s)

lemma Seq.domain_eq {s : M} (h : Seq s) : domain s = under (lh s) := (Model.lh_prop s).1 h

lemma lh_prop_of_not_seq {s : M} (h : ¬Seq s) : lh s = 0 := (lh_prop s).2 h

def seqcons (x s : M) : M := insert ⟪lh s, x⟫ s

@[simp] lemma seq_empty : Seq (∅ : M) := ⟨by simp, 0, by simp⟩

@[simp] lemma lh_empty : lh (∅ : M) = 0 := by
  have : under (lh ∅ : M) = under 0 := by simpa using Eq.symm <| Seq.domain_eq (M := M) (s := ∅) (by simp)
  exact under_inj this

scoped infixr:67 " ::ˢ " => seqcons

@[simp] lemma Seq.subset_seqcons (s x : M) : s ⊆ x ::ˢ s := by simp [seqcons]

@[simp] lemma Seq.mem_seqcons (s x : M) : ⟪lh s, x⟫ ∈ x ::ˢ s := by simp [seqcons]

lemma Seq.seq_seqcons {s : M} (h : Seq s) (x : M) : Seq (x ::ˢ s) :=
  ⟨h.isMapping.insert (by simp [h.domain_eq]), lh s + 1, by simp [seqcons, h.domain_eq]⟩

-- lemma seq_seqcons_iff (x s : M) : Seq (x ::ˢ s) ↔ Seq s := ⟨by { intro h; exact ⟨by {  },by { have := h.domain_eq; simp at this }⟩ }, by {  }⟩

@[simp] lemma Seq.lh_seqcons (x : M) {s} (h : Seq s) : lh (x ::ˢ s) = lh s + 1 := by
  have : under (lh s + 1) = under (lh (x ::ˢ s)) := by
    simpa [seqcons, h.domain_eq] using (h.seq_seqcons x).domain_eq
  exact Eq.symm <| under_inj this



end seq

/-
@[simp] lemma empty_seq : Seq (∅ : M) := ⟨0, by simp, by simp⟩



def IsMapping (m a b : M) : Prop := m ⊆ a ×ʰᶠ b ∧ ∀ x ∈ a, ∃! y, ⟪x, y⟫ ∈ m

scoped notation m:50 " :mapping " a " to " b:51 => IsMapping m a b

private lemma isMapping_graph (m a b : M) :
    m :mapping a to b ↔ (∀ x ∈ m, (∃ p₁ ≤ x, p₁ = π₁ x ∧ p₁ ∈ a) ∧ (∃ p₂ ≤ x, p₂ = π₂ x ∧ p₂ ∈ b)) ∧ ∀ x ∈ a, ∃! y, ⟪x, y⟫ ∈ m := by
  simp [IsMapping, subset_iff, mem_product_iff']; intro _
  constructor
  · intro hm x hx; exact ⟨⟨π₁ x, by simp, rfl, (hm x hx).1⟩, ⟨π₂ x, by simp, rfl, (hm x hx).2⟩⟩
  · intro h x hx; rcases h x hx with ⟨⟨_, _, rfl, h₁⟩, ⟨_, _, rfl, h₂⟩⟩; exact ⟨h₁, h₂⟩

def _root_.LO.FirstOrder.Arith.isMappingDef : 𝚺₀-Semisentence 3 := .mkSigma
  “∀[#0 < #1 + (#2 + #3 + 1) ^' 2](#0 ∈ #1 ↔ [∃∈ #2][∃∈ #4](!pairDef.val [#2, #1, #0]))” (by simp)

private lemma isMapping_iff (s t m : M) :
  IsMapping s t m ↔ ∀ x ∈ s, ∀ y

end mapping

-/

end LO.FirstOrder.Arith.Model

end
