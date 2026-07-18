module

public import Foundation.FirstOrder.SetTheory.Function
public import Foundation.FirstOrder.SetTheory.Ordinal

@[expose] public section
/-!

# Sequences for set theory

This implements sequences for set theory. Here a sequence is a function whose domain is an ordinal.

-/

namespace LO.FirstOrder.SetTheory

open SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]

/--
A sequence is a function with an ordinal domain.
-/
def Seq (s : V) : Prop := IsFunction s ∧ ∃ l, domain s = l ∧ IsOrdinal l

def Seq.IsFunction {s : V} (h : Seq s) : IsFunction s := h.1

def _root_.LO.FirstOrder.SetTheory.seqDef : SetTheorySemisentence 1 :=
  f“s. !IsFunction.dfn s ∧ ∃ l, l = !domain.dfn s ∧ !IsOrdinal.dfn l”

instance seq_defined : ℒₛₑₜ-predicate[V] (Seq : V → Prop) via seqDef := .mk <| by
  intro v; simp [Seq, seqDef]

instance seq_definable : ℒₛₑₜ-predicate (Seq : V → Prop) := seq_defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance seq_definable' (ℌ) : ℌ-Predicate (Seq : V → Prop) := seq_definable.of_zero

section

open Lean PrettyPrinter Delaborator

syntax ":Seq " first_order_term : first_order_formula

scoped macro_rules
  | `(⤫formula($type)[$binders* | $fbinders* | :Seq $t:first_order_term]) =>
    `(⤫formula($type)[$binders* | $fbinders* | !seqDef.val $t])

end

lemma lh_exists_uniq (s : V) : ∃! l, (Seq s → domain s = l) ∧ (¬Seq s → l = 0) := by
  by_cases h : Seq s
  · rcases h with ⟨h, l, hl⟩
    exact ExistsUnique.intro l
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
  · simp [h]

/--
The length of a sequence, or `0` if it is not a sequence.
-/
noncomputable def lh (s : V) : V := Classical.choose! (lh_exists_uniq s)

lemma lh_prop (s : V) : (Seq s → domain s = lh s) ∧ (¬Seq s → lh s = 0) := Classical.choose!_spec (lh_exists_uniq s)

lemma lh_prop_of_not_seq {s : V} (h : ¬Seq s) : lh s = 0 := (lh_prop s).2 h

lemma Seq.domain_eq {s : V} (h : Seq s) : domain s = lh s := (lh_prop s).1 h

def _root_.LO.FirstOrder.SetTheory.lhDef : SetTheorySemisentence 2 :=
  f“l s. (!seqDef s → l = !domain.dfn s) ∧ (¬!seqDef s → !isEmpty l)”

instance lh_defined : ℒₛₑₜ-function₁ (lh : V → V) via lhDef := .mk fun v ↦ by simp [lhDef, lh]; aesop

instance lh_definable : ℒₛₑₜ-function₁ (lh : V → V) := lh_defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance lh_definable' (ℌ) : ℌ-Function₁ (lh : V → V) := lh_definable.of_zero

lemma Seq.nth_exists_uniq {s : V} (h : Seq s) {α : V} (hα : α ∈ lh s) : ∃! y, ⟨α, y⟩ₖ ∈ s := (exists_unique_of_mem_function (isFunction_iff.mp h.IsFunction)) α (Seq.domain_eq h ▸ hα)

lemma Seq.exists {s : V} (h : Seq s) {α : V} (hα : α ∈ lh s) : ∃ y, ⟨α, y⟩ₖ ∈ s := (nth_exists_uniq h hα) |> ExistsUnique.exists

/-- The `α`th entry in a sequence, assuming `α` is in the length of the sequence. -/
noncomputable def Seq.nth {s : V} (h : Seq s) {α : V} (hα : α ∈ lh s) : V := Classical.choose! (h.nth_exists_uniq hα)

@[simp] lemma Seq.nth_mem {s : V} (h : Seq s) {α : V} (hα : α ∈ lh s) :
    ⟨α, h.nth hα⟩ₖ ∈ s := Classical.choose!_spec (h.nth_exists_uniq hα)

lemma Seq.nth_uniq {s : V} (h : Seq s) {α y : V} (hα : α ∈ lh s) (hy : ⟨α, y⟩ₖ ∈ s) : y = h.nth hα :=
    (h.nth_exists_uniq hα).unique hy (by simp)

lemma Seq.lh_eq_of {s : V} (h : Seq s) {l} (hdomain : domain s = l) : lh s = l := by
  simpa [h.domain_eq] using hdomain

lemma Seq.lh_eq_domain_of {s : V} (h : Seq s) : lh s = domain s := by
  have := h.IsFunction
  exact (forall_eq' (p := fun l ↦ lh s = l) (a' := domain s)).mp (fun l ↦ (lh_eq_of h (l := l)))

lemma Seq.lt_lh_iff {s : V} (h : Seq s) {α : V} : α ∈ lh s ↔ α ∈ domain s := by simp [h.domain_eq]

lemma Seq.lt_lh_of_mem {s : V} (h : Seq s) {α x : V} (hαx : ⟨α, x⟩ₖ ∈ s) : α ∈ lh s := by
  simpa [h.lt_lh_iff, mem_domain_iff] using ⟨x, hαx⟩

noncomputable def seqCons (s x : V) : V := insert ⟨lh s, x⟩ₖ s

section znth

def znth_existsUnique (s α : V) : ∃! x, (Seq s ∧ α ∈ lh s → ⟨α, x⟩ₖ ∈ s) ∧ (¬(Seq s ∧ α ∈ lh s) → x = ∅) := by
  by_cases h : Seq s ∧ α ∈ lh s
  · simpa [h] using h.1.nth_exists_uniq h.2
  · simp [h]

/-- The `α`th entry in a sequence. Returns `∅` if `s` is not a sequence or `α` is not in its domain. -/
noncomputable def znth (s α : V) : V := Classical.choose! (znth_existsUnique s α)

protected lemma Seq.znth {s α : V} (h : Seq s) (hα : α ∈ lh s) : ⟨α, znth s α⟩ₖ ∈ s := Classical.choose!_spec (znth_existsUnique s α) |>.1 ⟨h, hα⟩

lemma Seq.znth_eq_of_mem {s α x : V} (h : Seq s) (hα : ⟨α, x⟩ₖ ∈ s) : znth s α = x := by
  have hlt : α ∈ lh s := (by simp_all [lh] : domain s = lh s) ▸ (mem_domain_iff.mpr ⟨x, hα⟩)
  exact (h.1.unique hα (Seq.znth h hlt)).symm

lemma znth_prop_not {s α : V} (h : ¬Seq s ∨ α ∉ lh s) : znth s α = 0 :=
  Classical.choose!_spec (znth_existsUnique s α) |>.2 (by simpa [-not_and, not_and_or] using h)

def _root_.LO.FirstOrder.SetTheory.znthDef : SetTheorySemisentence 3 :=
  f“x s α. ∃ l, !lhDef l s ∧ (!seqDef s ∧ α ∈ l → !kpair.dfn α x ∈ s) ∧ (¬(!seqDef s ∧ α ∈ l) → !isEmpty x)”

private lemma znth_graph {x s α : V} : (∃ l, l = lh s ∧ (Seq s ∧ α ∈ l → ⟨α, x⟩ₖ ∈ s) ∧ (¬(Seq s ∧ α ∈ l) → x = ∅)) ↔ x = znth s α := by
  simp [znth, Classical.choose!_eq_iff_right]

instance znth_defined : ℒₛₑₜ-function₂ (znth : V → V → V) via znthDef := .mk fun v ↦ by
  simpa [znthDef, -not_and, not_and_or] using znth_graph (V := V)

instance znth_definable : ℒₛₑₜ-function₂ (znth : V → V → V) := znth_defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance znth_definable' (ℌ) : ℌ-Function₂ (znth : V → V → V) := znth_definable.of_zero

end znth

-- infixr:67 " ::ˢ " => seqCons

infixr:67 " ⁀' " => seqCons

@[simp] lemma seq_empty : Seq (∅ : V) := ⟨by simp, ∅, by simp⟩

@[simp] lemma lh_empty : lh (∅ : V) = ∅ := by
  simpa using Eq.symm <| Seq.domain_eq (V := V) (s := ∅) (by simp)

lemma Seq.isempty_of_lh_eq_zero {s : V} (hs : Seq s) (h : lh s = ∅) : s = ∅ :=
  subset_empty_iff_eq_empty.mp (empty_prod (range s) ▸ (mem_function_iff.mp ((hs.domain_eq ▸ h) ▸ isFunction_iff.mp hs.IsFunction)).1)

@[simp] lemma Seq.subset_seqCons (s x : V) : s ⊆ s ⁀' x := by simp [seqCons]

lemma Seq.subseteq_seqCons {s} (_ : Seq s) (x : V) : s ⊆ s ⁀' x := by
  intro z hz
  simp only [seqCons, mem_insert]
  exact Or.inr hz

@[simp] lemma Seq.mem_seqCons (s x : V) : ⟨lh s, x⟩ₖ ∈ s ⁀' x := by simp [seqCons]

protected lemma Seq.seqCons {s : V} (h : Seq s) (x : V) : Seq (s ⁀' x) := by
  have := h.IsFunction
  have heq := (forall_eq' (p := fun l ↦ lh s = l) (a' := domain s)).mp (fun l ↦ (lh_eq_of h (l := l)))
  have hlh := (((exists_eq_left' (a' := lh s)).mp (heq ▸ h.2)))
  have hnmem : lh s ∉ domain s := (domain_eq h) ▸ mem_irrefl (lh s)
  exact ⟨IsFunction.insert s (lh s) x hnmem,
    succ (lh s), by simpa [seqCons, h.domain_eq, succ] using IsOrdinal.succ (h := hlh)⟩

@[simp] lemma Seq.lh_seqCons (x : V) {s} (h : Seq s) : lh (s ⁀' x) = succ (lh s) := by
  simpa [seqCons, h.domain_eq, succ] using (h.seqCons x).domain_eq.symm

lemma kpair_mem_seqCons_iff {α x z s : V} : ⟨α, x⟩ₖ ∈ s ⁀' z ↔ (α = lh s ∧ x = z) ∨ ⟨α, x⟩ₖ ∈ s := by simp [seqCons]

@[simp] lemma lh_mem_seqCons (s z : V) : ⟨lh s, z⟩ₖ ∈ s ⁀' z := by simp [seqCons]

@[simp] lemma lh_mem_seqCons_iff {s x z : V} (h : Seq s) : ⟨lh s, x⟩ₖ ∈ s ⁀' z ↔ x = z := by
  suffices ⟨lh s, x⟩ₖ ∈ s → x = z by simpa [seqCons]
  intro hmem; have := h.lt_lh_of_mem hmem; simp at this

lemma Seq.mem_seqCons_iff_of_lt {s x z : V} (hα : α ∈ lh s) : ⟨α, x⟩ₖ ∈ s ⁀' z ↔ ⟨α, x⟩ₖ ∈ s := by
  suffices α = lh s → x = z → ⟨α, x⟩ₖ ∈ s by simpa [seqCons, hα]
  rintro rfl; simp at hα

@[simp] lemma lh_not_mem {s} (h : Seq s) (x : V) : ⟨lh s, x⟩ₖ ∉ s := fun hmem ↦ by have := h.lt_lh_of_mem hmem; simp at this

section

lemma seqCons_graph (t x s : V) :
    t = s ⁀' x ↔ ∃ l, l = lh s ∧ ∃ p, p = ⟨l, x⟩ₖ ∧ t = insert p s :=
  ⟨by rintro rfl
      exact ⟨lh s, rfl, ⟨lh s, x⟩ₖ,
        rfl, by rfl⟩,
   by rintro ⟨l, rfl, p, rfl, rfl⟩; rfl⟩

def _root_.LO.FirstOrder.SetTheory.seqConsDef : SetTheorySemisentence 3 :=
  “t s x. ∃ l, !lhDef l s ∧ ∃ p, !kpair.dfn p l x ∧ !insert.dfn t p s”

instance seqCons_defined : ℒₛₑₜ-function₂ (seqCons : V → V → V) via seqConsDef := .mk fun v ↦ by simp [seqConsDef, seqCons_graph]

instance seqCons_definable : ℒₛₑₜ-function₂ (seqCons : V → V → V) := seqCons_defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance seqCons_definable' (ℌ) : ℌ-Function₂ (seqCons : V → V → V) := seqCons_definable.of_zero

end

lemma Seq.restrict {s : V} (h : Seq s) {α : V} [hα : IsOrdinal α] (hsubseteq : α ⊆ lh s) : Seq (s ↾ α) :=
  ⟨h.IsFunction.restrict s α, α, by simp [h.domain_eq, hsubseteq, hα]⟩

lemma Seq.restrict_lh {s : V} (h : Seq s) {α : V} [hα : IsOrdinal α] (hsubseteq : α ⊆ lh s) : lh (s ↾ α) = α := by
  simp only [domain_restrict_eq, lh_eq_of (Seq.restrict h hsubseteq)]
  exact inter_eq_right_of_subset (lh_eq_domain_of h ▸ hsubseteq)

lemma domain_setdiff_of_IsFunction_of_mem {x y s : V} (hs : Seq s) (hxy : ⟨x, y⟩ₖ ∈ s) :
    domain (s \ {⟨x, y⟩ₖ}) = (domain s) \ {x} := by
  ext z
  simp only [mem_sdiff_iff, mem_singleton_iff, mem_domain_iff]
  constructor <;> intro h
  · obtain ⟨y₁, hy₁left, hy₁right⟩ := h
    constructor
    ·
      sorry
    · by_contra
      rw [this, (hs.IsFunction.unique hxy (this ▸ hy₁left))] at hy₁right
      contradiction
  · sorry

lemma Seq.eq_of_eq_of_subset {s₁ s₂ : V} (h₁ : Seq s₁) (h₂ : Seq s₂)
    (hl : lh s₁ = lh s₂) (hsubseteq : s₁ ⊆ s₂) : s₁ = s₂ := by
  ext z
  constructor <;> intro h
  · exact hsubseteq z h
  · rw [lh_eq_domain_of h₁, lh_eq_domain_of h₂] at hl
    obtain ⟨α, y, rfl⟩ := h₂.IsFunction.mem_eq_kpair h
    have hdefined : ∃ y', ⟨α, y'⟩ₖ ∈ s₁ := by
      apply mem_domain_iff.mp
      have h := mem_domain_iff.mpr ⟨y, h⟩
      exact hl ▸ h
    obtain ⟨y', hy'⟩ := hdefined
    exact h₂.IsFunction.unique (hsubseteq ⟨α, y'⟩ₖ hy') h ▸ hy'

lemma Seq.lh_ext {s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂) (h : lh s₁ = lh s₂)
    (H : ∀ α x₁ x₂, ⟨α, x₁⟩ₖ ∈ s₁ → ⟨α, x₂⟩ₖ ∈ s₂ → x₁ = x₂) : s₁ = s₂ := H₁.eq_of_eq_of_subset H₂ h <| subset_pair <| by
      intro α x hx
      have hα : α < lh s₂ := by simpa [← h] using H₁.lt_lh_of_mem hx
      rcases H α _ _ hx (H₂.nth_mem hα)
      simp

@[simp] lemma Seq.seqCons_ext {a₁ a₂ s₁ s₂ : V} (h₁ : Seq s₁) (h₂ : Seq s₂) :
    s₁ ⁀' a₁ = s₂ ⁀' a₂ ↔ a₁ = a₂ ∧ s₁ = s₂ := by
  constructor
  · intro h
    have hs₁s₂ : lh s₁ = lh s₂ := by simpa [h₁, h₂] using congr_arg lh h
    have hs₁ : ⟨lh s₁, a₁⟩ₖ ∈ s₂ ⁀' a₂ := by simpa [h] using lh_mem_seqCons s₁ a₁
    have hs₂ : ⟨lh s₁, a₂⟩ₖ ∈ s₂ ⁀' a₂ := by simp [hs₁s₂]
    have ha₁a₂ : a₁ = a₂ := (h₂.seqCons a₂).IsFunction.unique hs₁ hs₂
    have : s₁ ⊆ s₂ := subset_pair <| by
      intro i x hix
      have : i = lh s₂ ∧ x = a₂ ∨ ⟨i, x⟩ₖ ∈ s₂ := by
        simpa [kpair_mem_seqCons_iff, h] using Seq.subset_seqCons s₁ a₁ hix
      rcases this with (⟨rfl, rfl⟩ | hix₂)
      · have := h₁.lt_lh_of_mem hix; simp [hs₁s₂] at this
      · assumption
    exact ⟨ha₁a₂, h₁.eq_of_eq_of_subset h₂ hs₁s₂ this⟩
  · rintro ⟨rfl, rfl⟩; rfl
  -- ⟨by intro h
  --     have hs₁s₂ : lh s₁ = lh s₂ := by simpa [H₁, H₂] using congr_arg lh h
  --     have hs₁ : ⟨lh s₁, a₁⟩ₖ ∈ s₂ ⁀' a₂ := by simpa [h] using lh_mem_seqCons s₁ a₁
  --     have hs₂ : ⟨lh s₁, a₂⟩ₖ ∈ s₂ ⁀' a₂ := by simp [hs₁s₂]
  --     have ha₁a₂ : a₁ = a₂ := (H₂.seqCons a₂).IsFunction.uniq hs₁ hs₂
  --     have : s₁ ⊆ s₂ := subset_pair <| by
  --       intro i x hix
  --       have : i = lh s₂ ∧ x = a₂ ∨ ⟨i, x⟩ₖ ∈ s₂ := by
  --         simpa [kpair_mem_seqCons_iff, h] using Seq.subset_seqCons s₁ a₁ hix
  --       rcases this with (⟨rfl, rfl⟩ | hix₂)
  --       · have := H₁.lt_lh_of_mem hix; simp [hs₁s₂] at this
  --       · assumption
  --     exact ⟨ha₁a₂, H₁.eq_of_eq_of_subset H₂ hs₁s₂ this⟩,
  --  by rintro ⟨rfl, rfl⟩; rfl⟩

/-
TODO: It might be useful to make a zero/succ/limit version of this lemma.
I am not sure how to best state the limit case for usability.

lemma Seq.cases_iff {s : V} : Seq s ↔ s = ∅ ∨ ∃ x s', Seq s' ∧ s = s' ⁀' x ∨ ⋃ˢ (lh s) = lh s := by
  constructor
  · intro h
    by_cases hs : lh s = ∅
    · left
      exact isempty_of_lh_eq_zero h hs
    · right
      let i := lh s - 1
      have hi : i < lh s := pred_lt_self_of_pos (pos_iff_ne_zero.mpr hs)
      have lhs_eq : lh s = i + 1 := Eq.symm <| tsub_add_cancel_of_le <| ne_zero_iff_one_le.mp hs
      let s' := bitRemove ⟨i, h.nth hi⟩ₖ s
      have his : ⟨i, h.nth hi⟩ₖ ∈ s := h.nth_mem hi
      have hdoms' : domain s' = under i := by
        simp only [domain_bitRemove_of_IsFunction_of_mem h.IsFunction his, h.domain_eq, s']
        apply mem_ext
        simpa [lhs_eq, and_or_left] using fun j hj ↦ ne_of_lt hj
      have hs' : Seq s' := ⟨ h.IsFunction.of_subset (by simp [s']), i, hdoms' ⟩
      have hs'i : lh s' = i := by simpa [hs'.domain_eq] using hdoms'
      exact ⟨h.nth hi, s', hs', mem_ext <| fun v ↦ by
        simp only [seqCons, hs'i, mem_bitInsert_iff]
        simp [s']
        by_cases hv : v = ⟨i, h.nth hi⟩ₖ <;> simp [hv]⟩
  · rintro (rfl | ⟨x, s', hs', rfl⟩)
    · simp
    · exact hs'.seqCons x

alias ⟨Seq.cases, _⟩ := Seq.cases_iff
-/

/-- `!⟦x, y, z, ...⟧` notation for `Seq` -/
syntax "!⟦" term,* "⟧" : term

macro_rules
  | `(!⟦$terms:term,*, $term:term⟧) => `(seqCons !⟦$terms,*⟧ $term)
  | `(!⟦$term:term⟧) => `(seqCons ∅ $term)
  | `(!⟦⟧) => `(∅)

@[app_unexpander seqCons]
meta def vecConsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ !⟦$term2, $terms,*⟧ $term) => `(!⟦$term2, $terms,*, $term⟧)
  | `($_ !⟦$term2⟧ $term) => `(!⟦$term2, $term⟧)
  | `($_ ∅ $term) => `(!⟦$term⟧)
  | _ => throw ()

@[simp] lemma singleton_seq (x : V) : Seq !⟦x⟧ := by apply Seq.seqCons; simp

@[simp] lemma doubleton_seq (x y : V) : Seq !⟦x, y⟧ := by apply Seq.seqCons; simp

@[simp] lemma mem_singleton_seq_iff (x y : V) : ⟨∅, x⟩ₖ ∈ !⟦y⟧ ↔ x = y := by simp [kpair_mem_seqCons_iff]

section

def _root_.LO.FirstOrder.SetTheory.mkSeq₁Def : SetTheorySemisentence 2 :=
  “s x. ∀ z, !isEmpty z → !seqConsDef s z x”

instance mkSeq₁_defined : ℒₛₑₜ-function₁ (fun x : V ↦ !⟦x⟧) via mkSeq₁Def := .mk fun v ↦ by simp [mkSeq₁Def]; rfl

instance mkSeq₁_definable : ℒₛₑₜ-function₁ (fun x : V ↦ !⟦x⟧) := mkSeq₁_defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance mkSeq₁_definable' (Γ) : Γ-Function₁ (fun x : V ↦ !⟦x⟧) := mkSeq₁_definable.of_zero

def _root_.LO.FirstOrder.SetTheory.mkSeq₂Def : SetTheorySemisentence 3 :=
  “s x y. ∃ sx, !mkSeq₁Def sx x ∧ !seqConsDef s sx y”

instance mkSeq₂_defined : ℒₛₑₜ-function₂ (fun x y : V ↦ !⟦x, y⟧) via mkSeq₂Def := .mk fun v ↦ by simp [mkSeq₂Def]

instance mkSeq₂_definable : ℒₛₑₜ-function₂ (fun x y : V ↦ !⟦x, y⟧) := mkSeq₂_defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance mkSeq₂_definable' (Γ m) : Γ-[m + 1]-Function₂ (fun x y : V ↦ !⟦x, y⟧) := mkSeq₂_definable.of_sigmaOne

end

theorem skolem_seq {R : V → V → Prop} (hP : ℒₛₑₜ-relation R) {l : V} [IsOrdinal l]
    (h : ∀ x ∈ l, ∃ y, R x y) : ∃ s : V, Seq s ∧ lh s = l ∧ ∀ α x, ⟨α, x⟩ₖ ∈ s → R α x := by
  have h' : ∀ x : {x // x ∈ l}, ∃ y, R x.val y := by aesop
  obtain ⟨s, hs⟩ := Classical.skolem.mp h'

  sorry

  -- rcases sigmaOne_skolem hP (show ∀ x ∈ under l, ∃ y, R x y by simpa using H) with ⟨s, ms, sdom, h⟩
  -- have : Seq s := ⟨ms, l, sdom⟩
  -- exact ⟨s, this, by simpa [this.domain_eq] using sdom, h⟩

theorem sigmaOne_skolem_seq! {R : V → V → Prop} (hP : 𝚺₁-Relation R) {l}
    (h : ∀ x < l, ∃! y, R x y) : ∃! s, Seq s ∧ lh s = l ∧ ∀ i x, ⟪i, x⟫ ∈ s → R i x := by
  have : ∀ x < l, ∃ y, R x y := fun x hx ↦ (h x hx).exists
  rcases sigmaOne_skolem_seq hP this with ⟨s, Ss, rfl, hs⟩
  exact ExistsUnique.intro s ⟨Ss, rfl, hs⟩ (by
    rintro s' ⟨Ss', hss', hs'⟩
    exact Seq.lh_ext Ss' Ss hss' (fun i x₁ x₂ h₁ h₂ ↦ H i (Ss.lt_lh_of_mem h₂) |>.unique (hs' i x₁ h₁) (hs i x₂ h₂)))

section seqToVec

noncomputable def vecToSeq : {n : ℕ} → (Fin n → V) → V
  | 0,     _ => ∅
  | n + 1, v => vecToSeq (v ·.castSucc) ⁀' v (Fin.last n)

@[simp] lemma vecToSeq_nil : vecToSeq ![] = (∅ : V) := by simp [vecToSeq]

@[simp] lemma vecToSeq_vecCons {n} (v : Fin n → V) (a : V) :
    vecToSeq (v <: a) = vecToSeq v ⁀' a := by simp [vecToSeq]

@[simp] lemma vecToSeq_seq {n} (v : Fin n → V) : Seq (vecToSeq v) := by
  induction' n with n ih
  · simp [vecToSeq]
  · exact (ih _).seqCons _

@[simp] lemma lh_vecToSeq {n} (v : Fin n → V) : lh (vecToSeq v) = n := by
  induction' n with n ih <;> simp [vecToSeq, *]

/-
TODO: No coercion from `ℕ` to `V` yet.

lemma mem_vectoSeq {n : ℕ} (v : Fin n → V) (i : Fin n) : ⟪(i : V), v i⟫ ∈ vecToSeq v := by
  induction' n with n ih
  · exact i.elim0
  · cases' i using Fin.lastCases with i
    · simp [vecToSeq, kpair_mem_seqCons_iff]
    · simpa [vecToSeq, kpair_mem_seqCons_iff] using Or.inr <| ih (v ·.castSucc) i
-/

end seqToVec

end LO.FirstOrder.SetTheory
