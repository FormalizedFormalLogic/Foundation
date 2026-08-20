module

public import Foundation.FirstOrder.SetTheory.Function
public import Foundation.FirstOrder.SetTheory.Ordinal

@[expose] public section
/-!

# Sequences for set theory

This implements sequences for set theory. Here a sequence is a function whose domain is an ordinal.

Compare to `Foundation.FirstOrder.Arithmetic.HFS.Seq`.

-/

namespace LO.FirstOrder.SetTheory

open SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]

/--
A sequence is a function with an ordinal domain.
-/
def Seq (s : V) : Prop := IsFunction s ∧ ∃ l, domain s = l ∧ IsOrdinal l

def Seq.IsFunction {s : V} (h : Seq s) : IsFunction s := h.1

def _root_.LO.FirstOrder.SetTheory.seq.dfn : SetTheorySemisentence 1 :=
  f“s. !IsFunction.dfn s ∧ ∃ l, l = !domain.dfn s ∧ !IsOrdinal.dfn l”

instance seq.defined : ℒₛₑₜ-predicate[V] (Seq : V → Prop) via seq.dfn := .mk <| by
  intro v; simp [Seq, seq.dfn]

instance seq.definable : ℒₛₑₜ-predicate (Seq : V → Prop) := seq.defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance seq_definable' (ℌ) : ℌ-Predicate (Seq : V → Prop) := seq_definable.of_zero

section

open Lean PrettyPrinter Delaborator

syntax ":Seq " first_order_term : first_order_formula

scoped macro_rules
  | `(⤫formula($type)[$binders* | $fbinders* | :Seq $t:first_order_term]) =>
    `(⤫formula($type)[$binders* | $fbinders* | !seq.dfn $t])

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

def _root_.LO.FirstOrder.SetTheory.lh.dfn : SetTheorySemisentence 2 :=
  f“l s. (!seq.dfn s → l = !domain.dfn s) ∧ (¬!seq.dfn s → !isEmpty l)”

instance lh.defined : ℒₛₑₜ-function₁ (lh : V → V) via lh.dfn := .mk fun v ↦ by simp [lh.dfn, lh]; aesop

instance lh.definable : ℒₛₑₜ-function₁ (lh : V → V) := lh.defined.to_definable

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

theorem znth_existsUnique (s α : V) : ∃! x, (Seq s ∧ α ∈ lh s → ⟨α, x⟩ₖ ∈ s) ∧ (¬(Seq s ∧ α ∈ lh s) → x = ∅) := by
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

def _root_.LO.FirstOrder.SetTheory.znth.dfn : SetTheorySemisentence 3 :=
  f“x s α. ∃ l, !lh.dfn l s ∧ (!seq.dfn s ∧ α ∈ l → !kpair.dfn α x ∈ s) ∧ (¬(!seq.dfn s ∧ α ∈ l) → !isEmpty x)”

private lemma znth_graph {x s α : V} : (∃ l, l = lh s ∧ (Seq s ∧ α ∈ l → ⟨α, x⟩ₖ ∈ s) ∧ (¬(Seq s ∧ α ∈ l) → x = ∅)) ↔ x = znth s α := by
  simp [znth, Classical.choose!_eq_iff_right]

instance znth.defined : ℒₛₑₜ-function₂ (znth : V → V → V) via znth.dfn := .mk fun v ↦ by
  simpa [znth.dfn, -not_and, not_and_or] using znth_graph (V := V)

instance znth.definable : ℒₛₑₜ-function₂ (znth : V → V → V) := znth.defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance znth.definable' (ℌ) : ℌ-Function₂ (znth : V → V → V) := znth.definable.of_zero

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

def _root_.LO.FirstOrder.SetTheory.seqCons.dfn : SetTheorySemisentence 3 :=
  “t s x. ∃ l, !lh.dfn l s ∧ ∃ p, !kpair.dfn p l x ∧ !insert.dfn t p s”

instance seqCons.defined : ℒₛₑₜ-function₂ (seqCons : V → V → V) via seqCons.dfn := .mk fun v ↦ by simp [seqCons.dfn, seqCons_graph]

instance seqCons.definable : ℒₛₑₜ-function₂ (seqCons : V → V → V) := seqCons.defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance seqCons.definable' (ℌ) : ℌ-Function₂ (seqCons : V → V → V) := seqCons.definable.of_zero

end

@[simp] lemma Seq.restrict {s : V} (h : Seq s) {α : V} [hα : IsOrdinal α] (hsubseteq : α ⊆ lh s) : Seq (s ↾ α) :=
  ⟨h.IsFunction.restrict s α, α, by simp [h.domain_eq, hsubseteq, hα]⟩

@[simp] lemma Seq.lh_restrict {s : V} (h : Seq s) {α : V} [hα : IsOrdinal α] (hsubseteq : α ⊆ lh s) : lh (s ↾ α) = α := by
  simp only [domain_restrict_eq, lh_eq_of (Seq.restrict h hsubseteq)]
  exact inter_eq_right_of_subset (h.lh_eq_domain_of ▸ hsubseteq)

@[simp] lemma domain_setdiff_of_Seq_of_mem {x y s : V} (hs : Seq s) (hxy : ⟨x, y⟩ₖ ∈ s) :
    domain (s \ {⟨x, y⟩ₖ}) = (domain s) \ {x} := by
  ext z
  simp only [mem_sdiff_iff, mem_singleton_iff, mem_domain_iff]
  constructor <;> intro h
  · obtain ⟨y₁, hy₁left, hy₁right⟩ := h
    constructor
    · aesop
    · by_contra
      rw [this, (hs.IsFunction.unique hxy (this ▸ hy₁left))] at hy₁right
      contradiction
  · aesop

lemma Seq.eq_of_eq_of_subset {s₁ s₂ : V} (h₁ : Seq s₁) (h₂ : Seq s₂)
    (hl : lh s₁ = lh s₂) (hsubseteq : s₁ ⊆ s₂) : s₁ = s₂ := by
  ext z
  constructor <;> intro h
  · exact hsubseteq z h
  · rw [h₁.lh_eq_domain_of, h₂.lh_eq_domain_of] at hl
    obtain ⟨α, y, rfl⟩ := h₂.IsFunction.mem_eq_kpair h
    have hdefined : ∃ y', ⟨α, y'⟩ₖ ∈ s₁ := mem_domain_iff.mp (hl ▸ mem_domain_iff.mpr ⟨y, h⟩)
    obtain ⟨y', hy'⟩ := hdefined
    exact h₂.IsFunction.unique (hsubseteq ⟨α, y'⟩ₖ hy') h ▸ hy'

lemma Seq.lh_ext {s₁ s₂ : V} (h₁ : Seq s₁) (h₂ : Seq s₂) (h : lh s₁ = lh s₂)
    (H : ∀ α x₁ x₂, ⟨α, x₁⟩ₖ ∈ s₁ → ⟨α, x₂⟩ₖ ∈ s₂ → x₁ = x₂) : s₁ = s₂ := by
  refine h₁.eq_of_eq_of_subset h₂ h ?_
  intro z hy
  rw [h₁.lh_eq_domain_of, h₂.lh_eq_domain_of] at h
  obtain ⟨x, y, rfl⟩ := h₁.1.mem_eq_kpair hy
  obtain ⟨y', hy'⟩ := mem_domain_iff.mp (h ▸ mem_domain_of_kpair_mem hy)
  exact H x y y' hy hy' ▸ hy'

@[simp] lemma Seq.seqCons_ext {a₁ a₂ s₁ s₂ : V} (h₁ : Seq s₁) (h₂ : Seq s₂) :
    s₁ ⁀' a₁ = s₂ ⁀' a₂ ↔ a₁ = a₂ ∧ s₁ = s₂ := by
  constructor
  · intro h
    have hs₁s₂ : lh s₁ = lh s₂ := by simpa [h₁, h₂] using congr_arg lh h
    have hs₁ : ⟨lh s₁, a₁⟩ₖ ∈ s₂ ⁀' a₂ := by simpa [h] using lh_mem_seqCons s₁ a₁
    have hs₂ : ⟨lh s₁, a₂⟩ₖ ∈ s₂ ⁀' a₂ := by simp [hs₁s₂]
    have ha₁a₂ : a₁ = a₂ := (h₂.seqCons a₂).IsFunction.unique hs₁ hs₂
    have : s₁ ⊆ s₂ := by
      intro p hp
      obtain ⟨x, y, rfl⟩ := h₁.1.mem_eq_kpair hp
      have hmem : x ∈ lh s₁ := (h₁.lh_eq_domain_of) ▸ mem_domain_of_kpair_mem hp
      have hp : ⟨x, y⟩ₖ ∈ s₁ ⁀' a₁ := (mem_insert).mpr (Or.inr hp)
      rw [h] at hp
      apply mem_insert.mp at hp
      aesop
    exact ⟨ha₁a₂, h₁.eq_of_eq_of_subset h₂ hs₁s₂ this⟩
  · rintro ⟨rfl, rfl⟩; rfl

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

def _root_.LO.FirstOrder.SetTheory.mkSeq₁.dfn : SetTheorySemisentence 2 :=
  “s x. ∀ z, !isEmpty z → !seqCons.dfn s z x”

instance mkSeq₁.defined : ℒₛₑₜ-function₁ (fun x : V ↦ !⟦x⟧) via mkSeq₁.dfn := .mk fun v ↦ by simp [mkSeq₁.dfn]

instance mkSeq₁.definable : ℒₛₑₜ-function₁ (fun x : V ↦ !⟦x⟧) := mkSeq₁.defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance mkSeq₁.definable' (Γ) : Γ-Function₁ (fun x : V ↦ !⟦x⟧) := mkSeq₁.definable.of_zero

def _root_.LO.FirstOrder.SetTheory.mkSeq₂.dfn : SetTheorySemisentence 3 :=
  “s x y. ∃ sx, !mkSeq₁.dfn sx x ∧ !seqCons.dfn s sx y”

instance mkSeq₂.defined : ℒₛₑₜ-function₂ (fun x y : V ↦ !⟦x, y⟧) via mkSeq₂.dfn := .mk fun v ↦ by simp [mkSeq₂.dfn]

instance mkSeq₂.definable : ℒₛₑₜ-function₂ (fun x y : V ↦ !⟦x, y⟧) := mkSeq₂.defined.to_definable

/- TODO: Once the Lévy hierarchy is added, add a hierarchy-symbol-specific version. -/
-- instance mkSeq₂.definable' (Γ m) : Γ-[m + 1]-Function₂ (fun x y : V ↦ !⟦x, y⟧) := mkSeq₂.definable.of_sigmaOne

end

/- TODO: Add these once the Lévy hierarchy is added. -/
/- theorem sigmaOne_skolem_seq {R : V → V → Prop} (hP : 𝚺₁-Relation R) {l}
    (H : ∀ x < l, ∃ y, R x y) : ∃ s, Seq s ∧ lh s = l ∧ ∀ α x, ⟨α, x⟩ₖ ∈ s → R α x := by
  rcases sigmaOne_skolem hP (show ∀ x ∈ under l, ∃ y, R x y by simpa using H) with ⟨s, ms, sdom, h⟩
  have : Seq s := ⟨ms, l, sdom⟩
  exact ⟨s, this, by simpa [this.domain_eq] using sdom, h⟩

theorem sigmaOne_skolem_seq! {R : V → V → Prop} (hP : 𝚺₁-Relation R) {l}
    (h : ∀ x < l, ∃! y, R x y) : ∃! s, Seq s ∧ lh s = l ∧ ∀ α x, ⟨α, x⟩ₖ ∈ s → R α x := by
  have : ∀ x < l, ∃ y, R x y := fun x hx ↦ (h x hx).exists
  rcases sigmaOne_skolem_seq hP this with ⟨s, Ss, rfl, hs⟩
  exact ExistsUnique.intro s ⟨Ss, rfl, hs⟩ (by
    rintro s' ⟨Ss', hss', hs'⟩
    exact Seq.lh_ext Ss' Ss hss' (fun i x₁ x₂ h₁ h₂ ↦ H i (Ss.lt_lh_of_mem h₂) |>.unique (hs' i x₁ h₁) (hs i x₂ h₂)))
-/

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
  induction' n with n ih <;> (simp [vecToSeq, *]; rfl)

lemma mem_vectoSeq {n : ℕ} (v : Fin n → V) (i : Fin n) : ⟨(i : V), v i⟩ₖ ∈ vecToSeq v := by
  induction' n with n ih
  · exact i.elim0
  · cases' i using Fin.lastCases with i
    · simp [vecToSeq, kpair_mem_seqCons_iff]
    · simpa [vecToSeq, kpair_mem_seqCons_iff] using Or.inr <| ih (v ·.castSucc) i

end seqToVec

section notations

/-! ### Macros for binder notation -/

def memRel : SetTheorySemisentence 3 :=
  “R x y. ∃ p, !kpair.dfn p x y ∧ p ∈ R”

/-- The relation `⟨x, y⟩ₖ ∈ R` as an operator. -/
def memRelOpr : Semiformula.Operator ℒₛₑₜ 3 := ⟨memRel⟩

open Lean PrettyPrinter Delaborator

/-- `x ~[f] y` states that `⟨x, y⟩ₖ` is in `f` -/
syntax:45 first_order_term:45 " ∼[" first_order_term "]" first_order_term:0 : first_order_formula
syntax:45 first_order_term:45 " ≁[" first_order_term "]" first_order_term:0 : first_order_formula

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t₁:first_order_term ∼[ $u:first_order_term ] $t₂:first_order_term]) =>
    `(memRelOpr.operator ![⤫term(lit)[$binders* | $fbinders* | $u], ⤫term(lit)[$binders* | $fbinders* | $t₁], ⤫term(lit)[$binders* | $fbinders* | $t₂]])
  /- TODO: Add support for `∅ ∼[u] t` and `t ∼[u] ∅`. -/
  -- | `(⤫formula(lit)[ $binders* | $fbinders* | ∅ ∼[ $u:first_order_term ] $t:first_order_term]) => -- The problem is with this line
  --   `(⤫formula(lit)[ $binders* | $fbinders* | ∃¹ ((∀¹[#0 ∈ #1] ⊥) ∧ (#0 ∼[$u] $t₂))])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t₁:first_order_term ≁[ $u:first_order_term ] $t₂:first_order_term]) =>
    `(∼memRelOpr.operator ![⤫term(lit)[$binders* | $fbinders* | $u], ⤫term(lit)[$binders* | $fbinders* | $t₁], ⤫term(lit)[$binders* | $fbinders* | $t₂]])
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t₁:first_order_term ∼[ $u:first_order_term ] $t₂:first_order_term]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    let x₃ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t₁] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $x₃ $binders* | $fbinders* | $t₂ ] 🡒 “#2 ∼[#1] #0”))))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t₁:first_order_term ≁[ $u:first_order_term ] $t₂:first_order_term]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    let x₃ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t₁] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $x₃ $binders* | $fbinders* | $t₂ ] 🡒 “#2 ≁[#1] #0”))))

#check f“x y. x ∈ y”

#check f“f x y. x ∼[f] y”

#check f“f x y. x ∈ (!kpair.dfn y y)”

#check f“f x y. x ∼[f] (!kpair.dfn y y)”

end notations

end LO.FirstOrder.SetTheory
