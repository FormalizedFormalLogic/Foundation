module

public import Foundation.FirstOrder.Arithmetic.HFS.Basic

@[expose] public section
/-!

# Sequence

-/

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Seq (s : V) : Prop := IsMapping s ∧ ∃ l, domain s = under l

def Seq.isMapping {s : V} (h : Seq s) : IsMapping s := h.1

private lemma seq_iff (s : V) : Seq s ↔ IsMapping s ∧ ∃ l ≤ 2 * s, ∃ d ≤ 2 * s, d = domain s ∧ d = under l :=
  ⟨by rintro ⟨hs, l, h⟩
      exact ⟨hs, l, (by
      calc
        l ≤ domain s := by simp [h]
        _ ≤ 2 * s    := by simp), ⟨domain s , by simp,  rfl, h⟩⟩,
   by rintro ⟨hs, l, _, _, _, rfl, h⟩; exact ⟨hs, l, h⟩⟩

def _root_.LO.FirstOrder.Arithmetic.seqDef : 𝚺₀.Semisentence 1 := .mkSigma
  “s. !isMappingDef s ∧ ∃ l <⁺ 2 * s, ∃ d <⁺ 2 * s, !domainDef d s ∧ !underDef d l”

instance seq_defined : 𝚺₀-Predicate (Seq : V → Prop) via seqDef := .mk <| by
  intro v; simp [seqDef, seq_iff, -existsAndEq]

instance seq_definable : 𝚺₀-Predicate (Seq : V → Prop) := seq_defined.to_definable

instance seq_definable' (ℌ) : ℌ-Predicate (Seq : V → Prop) := seq_definable.of_zero

section

open Lean PrettyPrinter Delaborator

syntax ":Seq " first_order_term : first_order_formula

scoped macro_rules
  | `(⤫formula($type)[$binders* | $fbinders* | :Seq $t:first_order_term]) =>
    `(⤫formula($type)[$binders* | $fbinders* | !seqDef.val $t])

end

lemma lh_exists_uniq (s : V) : ∃! l, (Seq s → domain s = under l) ∧ (¬Seq s → l = 0) := by
  by_cases h : Seq s
  · rcases h with ⟨h, l, hl⟩
    exact ExistsUnique.intro l
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
      (by simp [show Seq s from ⟨h, l, hl⟩, hl])
  · simp [h]

noncomputable def lh (s : V) : V := Classical.choose! (lh_exists_uniq s)

lemma lh_prop (s : V) : (Seq s → domain s = under (lh s)) ∧ (¬Seq s → lh s = 0) := Classical.choose!_spec (lh_exists_uniq s)

lemma lh_prop_of_not_seq {s : V} (h : ¬Seq s) : lh s = 0 := (lh_prop s).2 h

lemma Seq.domain_eq {s : V} (h : Seq s) : domain s = under (lh s) := (lh_prop s).1 h

@[simp] lemma lh_bound (s : V) : lh s ≤ 2 * s := by
  by_cases hs : Seq s
  · calc
      lh s ≤ under (lh s) := le_under _
      _    ≤ 2 * s        := by simp [←hs.domain_eq]
  · simp [lh_prop_of_not_seq hs]

private lemma lh_graph (l s : V) : l = lh s ↔ (Seq s → ∃ d ≤ 2 * s, d = domain s ∧ d = under l) ∧ (¬Seq s → l = 0) :=
  ⟨by
    rintro rfl
    by_cases Hs : Seq s <;> simp [Hs, ←Seq.domain_eq, lh_prop_of_not_seq], by
    rintro ⟨h, hn⟩
    by_cases Hs : Seq s
    · rcases h Hs with ⟨_, _, rfl, h⟩; simpa [h] using Hs.domain_eq
    · simp [lh_prop_of_not_seq Hs, hn Hs]⟩

def _root_.LO.FirstOrder.Arithmetic.lhDef : 𝚺₀.Semisentence 2 := .mkSigma
  “l s. (!seqDef s → ∃ d <⁺ 2 * s, !domainDef d s ∧ !underDef d l) ∧ (¬!seqDef s → l = 0)”

instance lh_defined : 𝚺₀-Function₁ (lh : V → V) via lhDef := .mk fun v ↦ by simp [lhDef, -exists_eq_right_right, lh_graph]

instance lh_definable : 𝚺₀-Function₁ (lh : V → V) := lh_defined.to_definable

instance lh_definable' (ℌ) : ℌ-Function₁ (lh : V → V) := lh_definable.of_zero

instance : Bounded₁ (lh : V → V) := ⟨‘x. 2 * x’, fun _ ↦ by simp⟩

lemma Seq.exists {s : V} (h : Seq s) {x : V} (hx : x < lh s) : ∃ y, ⟪x, y⟫ ∈ s := h.isMapping x (by simpa [h.domain_eq] using hx) |>.exists

lemma Seq.nth_exists_uniq {s : V} (h : Seq s) {x : V} (hx : x < lh s) : ∃! y, ⟪x, y⟫ ∈ s := h.isMapping x (by simpa [h.domain_eq] using hx)

noncomputable def Seq.nth {s : V} (h : Seq s) {x : V} (hx : x < lh s) : V := Classical.choose! (h.nth_exists_uniq hx)

@[simp] lemma Seq.nth_mem {s : V} (h : Seq s) {x : V} (hx : x < lh s) :
    ⟪x, h.nth hx⟫ ∈ s := Classical.choose!_spec (h.nth_exists_uniq hx)

lemma Seq.nth_uniq {s : V} (h : Seq s) {x y : V} (hx : x < lh s) (hy : ⟪x, y⟫ ∈ s) : y = h.nth hx :=
    (h.nth_exists_uniq hx).unique hy (by simp)

@[simp] lemma Seq.nth_lt {s : V} (h : Seq s) {x} (hx : x < lh s) : h.nth hx < s := lt_of_mem_rng (h.nth_mem hx)

lemma Seq.lh_eq_of {s : V} (H : Seq s) {l} (h : domain s = under l) : lh s = l := by
  simpa [H.domain_eq] using h

lemma Seq.lt_lh_iff {s : V} (h : Seq s) {i} : i < lh s ↔ i ∈ domain s := by simp [h.domain_eq]

lemma Seq.lt_lh_of_mem {s : V} (h : Seq s) {i x} (hix : ⟪i, x⟫ ∈ s) : i < lh s := by
  simpa [h.lt_lh_iff, mem_domain_iff] using ⟨x, hix⟩

noncomputable def seqCons (s x : V) : V := insert ⟪lh s, x⟫ s

section znth

def znth_existsUnique (s i : V) : ∃! x, (Seq s ∧ i < lh s → ⟪i, x⟫ ∈ s) ∧ (¬(Seq s ∧ i < lh s) → x = 0) := by
  by_cases h : Seq s ∧ i < lh s
  · simpa [h] using h.1.nth_exists_uniq h.2
  · simp [h]

noncomputable def znth (s i : V) : V := Classical.choose! (znth_existsUnique s i)

protected lemma Seq.znth {s i : V} (h : Seq s) (hi : i < lh s) : ⟪i, znth s i⟫ ∈ s := Classical.choose!_spec (znth_existsUnique s i) |>.1 ⟨h, hi⟩

lemma Seq.znth_eq_of_mem {s i : V} (h : Seq s) (hi : ⟪i, x⟫ ∈ s) : znth s i = x :=
  h.isMapping.uniq (h.znth (h.lt_lh_of_mem hi)) hi

lemma znth_prop_not {s i : V} (h : ¬Seq s ∨ lh s ≤ i) : znth s i = 0 :=
  Classical.choose!_spec (znth_existsUnique s i) |>.2 (by simpa [-not_and, not_and_or] using h)

def _root_.LO.FirstOrder.Arithmetic.znthDef : 𝚺₀.Semisentence 3 := .mkSigma
  “x s i. ∃ l <⁺ 2 * s, !lhDef l s ∧ (:Seq s ∧ i < l → i ∼[s] x) ∧ (¬(:Seq s ∧ i < l) → x = 0)”

private lemma znth_graph {x s i : V} : (∃ l ≤ 2 * s, l = lh s ∧ (Seq s ∧ i < l → ⟪i, x⟫ ∈ s) ∧ (¬(Seq s ∧ i < l) → x = 0)) ↔ x = znth s i := by
  simp [znth, Classical.choose!_eq_iff_right]

instance znth_defined : 𝚺₀-Function₂ (znth : V → V → V) via znthDef := .mk fun v ↦ by
  simpa [znthDef, -not_and, not_and_or] using znth_graph (V := V)

instance znth_definable : 𝚺₀-Function₂ (znth : V → V → V) := znth_defined.to_definable

instance znth_definable' (ℌ) : ℌ-Function₂ (znth : V → V → V) := znth_definable.of_zero

end znth

-- infixr:67 " ::ˢ " => seqCons

infixr:67 " ⁀' " => seqCons

@[simp] lemma seq_empty : Seq (∅ : V) := ⟨by simp, 0, by simp⟩

@[simp] lemma lh_empty : lh (∅ : V) = 0 := by
  have : under (lh ∅ : V) = under 0 := by simpa using Eq.symm <| Seq.domain_eq (V := V) (s := ∅) (by simp)
  exact under_inj.mp this

lemma Seq.isempty_of_lh_eq_zero {s : V} (Hs : Seq s) (h : lh s = 0) : s = ∅ := by simpa [h] using Hs.domain_eq

@[simp] lemma Seq.subset_seqCons (s x : V) : s ⊆ s ⁀' x := by simp [seqCons]

lemma Seq.lt_seqCons {s} (hs : Seq s) (x : V) : s < s ⁀' x :=
  lt_iff_le_and_ne.mpr <| ⟨le_of_subset <| by simp, by
    simp only [seqCons, ne_eq]; intro A
    have : ⟪lh s, x⟫ ∈ s := by simpa [←A] using mem_insert ⟪lh s, x⟫ s
    simpa using hs.lt_lh_of_mem this⟩

@[simp] lemma Seq.mem_seqCons (s x : V) : ⟪lh s, x⟫ ∈ s ⁀' x := by simp [seqCons]

protected lemma Seq.seqCons {s : V} (h : Seq s) (x : V) : Seq (s ⁀' x) :=
  ⟨h.isMapping.insert (by simp [h.domain_eq]), lh s + 1, by simp [seqCons, h.domain_eq]⟩

@[simp] lemma Seq.lh_seqCons (x : V) {s} (h : Seq s) : lh (s ⁀' x) = lh s + 1 := by
  have : under (lh s + 1) = under (lh (s ⁀' x)) := by
    simpa [seqCons, h.domain_eq] using (h.seqCons x).domain_eq
  exact Eq.symm <| under_inj.mp this

lemma mem_seqCons_iff {i x z s : V} : ⟪i, x⟫ ∈ s ⁀' z ↔ (i = lh s ∧ x = z) ∨ ⟪i, x⟫ ∈ s := by simp [seqCons]

@[simp] lemma lh_mem_seqCons (s z : V) : ⟪lh s, z⟫ ∈ s ⁀' z := by simp [seqCons]

@[simp] lemma lh_mem_seqCons_iff {s x z : V} (H : Seq s) : ⟪lh s, x⟫ ∈ s ⁀' z ↔ x = z := by
  suffices ⟪lh s, x⟫ ∈ s → x = z by simpa [seqCons]
  intro h; have := H.lt_lh_of_mem h; simp at this

lemma Seq.mem_seqCons_iff_of_lt {s x z : V} (hi : i < lh s) : ⟪i, x⟫ ∈ s ⁀' z ↔ ⟪i, x⟫ ∈ s := by
  suffices i = lh s → x = z → ⟪i, x⟫ ∈ s by simpa [seqCons, hi]
  rintro rfl; simp at hi

@[simp] lemma lh_not_mem {s} (Ss : Seq s) (x : V) : ⟪lh s, x⟫ ∉ s := fun h ↦ by have := Ss.lt_lh_of_mem h; simp at this

section

lemma seqCons_graph (t x s : V) :
    t = s ⁀' x ↔ ∃ l ≤ 2 * s, l = lh s ∧ ∃ p ≤ (2 * s + x + 1)^2, p = ⟪l, x⟫ ∧ t = insert p s :=
  ⟨by rintro rfl
      exact ⟨lh s, by simp, rfl, ⟪lh s, x⟫,
        le_trans (pair_le_pair_left (by simp) x) (pair_polybound (2 * s) x), rfl, by rfl⟩,
   by rintro ⟨l, _, rfl, p, _, rfl, rfl⟩; rfl⟩

def _root_.LO.FirstOrder.Arithmetic.seqConsDef : 𝚺₀.Semisentence 3 := .mkSigma
  “t s x. ∃ l <⁺ 2 * s, !lhDef l s ∧ ∃ p <⁺ (2 * s + x + 1)², !pairDef p l x ∧ !insertDef t p s”

instance seqCons_defined : 𝚺₀-Function₂ (seqCons : V → V → V) via seqConsDef := .mk fun v ↦ by simp [seqConsDef, seqCons_graph]

instance seqCons_definable : 𝚺₀-Function₂ (seqCons : V → V → V) := seqCons_defined.to_definable

instance seqCons_definable' (ℌ) : ℌ-Function₂ (seqCons : V → V → V) := seqCons_definable.of_zero

@[simp] lemma natCast_empty : ((∅ : ℕ) : V) = ∅ := by simp [emptyset_def]

lemma seqCons_absolute (s a : ℕ) : ((s ⁀' a : ℕ) : V) = (s : V) ⁀' (a : V) := by
  simpa using DefinedFunction.shigmaZero_absolute_func V seqCons_defined seqCons_defined ![s, a]

end

lemma Seq.restr {s : V} (H : Seq s) {i : V} (hi : i ≤ lh s) : Seq (s ↾ under i) :=
  ⟨H.isMapping.restr (under i), i, domain_restr_of_subset_domain (by simp [H.domain_eq, hi])⟩

lemma Seq.restr_lh {s : V} (H : Seq s) {i : V} (hi : i ≤ lh s) : lh (s ↾ under i) = i :=
  (H.restr hi).lh_eq_of (domain_restr_of_subset_domain <| by simp [H.domain_eq, hi])

lemma domain_bitRemove_of_isMapping_of_mem {x y s : V} (hs : IsMapping s) (hxy : ⟪x, y⟫ ∈ s) :
    domain (bitRemove ⟪x, y⟫ s) = bitRemove x (domain s) := by
  suffices ∀ x₁, (∃ y₁, (x₁ = x → y₁ ≠ y) ∧ ⟪x₁, y₁⟫ ∈ s) ↔ x₁ ≠ x ∧ ∃ y, ⟪x₁, y⟫ ∈ s by
    apply mem_ext; simpa [mem_domain_iff]
  intro x₁
  constructor
  · rintro ⟨y₁, hy₁, hx₁y₁⟩; exact ⟨by rintro rfl; exact hy₁ rfl (hs.uniq hx₁y₁ hxy), y₁, hx₁y₁⟩
  · intro ⟨hx, y₁, hx₁y₁⟩
    exact ⟨y₁, by intro _; contradiction, hx₁y₁⟩

lemma Seq.eq_of_eq_of_subset {s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂)
    (hl : lh s₁ = lh s₂) (h : s₁ ⊆ s₂) : s₁ = s₂ := by
  apply mem_ext; intro u
  constructor
  · intro hu; exact h hu
  · intro hu
    have : π₁ u < lh s₁ := by
      simpa [hl] using H₂.lt_lh_of_mem (show ⟪π₁ u, π₂ u⟫ ∈ s₂ from by simpa using hu)
    have : ∃ y, ⟪π₁ u, y⟫ ∈ s₁ := H₁.exists this
    rcases this with ⟨y, hy⟩
    have : y = π₂ u := H₂.isMapping.uniq (h hy) (show ⟪π₁ u, π₂ u⟫ ∈ s₂ from by simpa using hu)
    rcases this with rfl
    simpa using hy

lemma subset_pair {s t : V} (h : ∀ i x, ⟪i, x⟫ ∈ s → ⟪i, x⟫ ∈ t) : s ⊆ t := by
  intro u hu
  simpa using h (π₁ u) (π₂ u) (by simpa using hu)

lemma Seq.lh_ext {s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂) (h : lh s₁ = lh s₂)
    (H : ∀ i x₁ x₂, ⟪i, x₁⟫ ∈ s₁ → ⟪i, x₂⟫ ∈ s₂ → x₁ = x₂) : s₁ = s₂ := H₁.eq_of_eq_of_subset H₂ h <| subset_pair <| by
      intro i x hx
      have hi : i < lh s₂ := by simpa [← h] using H₁.lt_lh_of_mem hx
      rcases H i _ _ hx (H₂.nth_mem hi)
      simp

@[simp] lemma Seq.seqCons_ext {a₁ a₂ s₁ s₂ : V} (H₁ : Seq s₁) (H₂ : Seq s₂) :
    s₁ ⁀' a₁ = s₂ ⁀' a₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intro h
      have hs₁s₂ : lh s₁ = lh s₂ := by simpa [H₁, H₂] using congr_arg lh h
      have hs₁ : ⟪lh s₁, a₁⟫ ∈ s₂ ⁀' a₂ := by simpa [h] using lh_mem_seqCons s₁ a₁
      have hs₂ : ⟪lh s₁, a₂⟫ ∈ s₂ ⁀' a₂ := by simp [hs₁s₂]
      have ha₁a₂ : a₁ = a₂ := (H₂.seqCons a₂).isMapping.uniq hs₁ hs₂
      have : s₁ ⊆ s₂ := subset_pair <| by
        intro i x hix
        have : i = lh s₂ ∧ x = a₂ ∨ ⟪i, x⟫ ∈ s₂ := by
          simpa [mem_seqCons_iff, h] using Seq.subset_seqCons s₁ a₁ hix
        rcases this with (⟨rfl, rfl⟩ | hix₂)
        · have := H₁.lt_lh_of_mem hix; simp [hs₁s₂] at this
        · assumption
      exact ⟨ha₁a₂, H₁.eq_of_eq_of_subset H₂ hs₁s₂ this⟩,
   by rintro ⟨rfl, rfl⟩; rfl⟩

/-- TODO: move to Lemmata.lean-/
lemma ne_zero_iff_one_le {a : V} : a ≠ 0 ↔ 1 ≤ a := Iff.trans pos_iff_ne_zero.symm (pos_iff_one_le (a := a))

lemma Seq.cases_iff {s : V} : Seq s ↔ s = ∅ ∨ ∃ x s', Seq s' ∧ s = s' ⁀' x := ⟨fun h ↦ by
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
      simpa [lhs_eq, and_or_left] using fun j hj ↦ ne_of_lt hj
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
theorem seq_induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
  (hnil : P ∅) (hcons : ∀ s x, Seq s → P s → P (s ⁀' x)) :
    ∀ {s : V}, Seq s → P s := by
  intro s sseq
  induction s using ISigma1.order_induction
  · exact Γ
  · definability
  case ind s ih =>
    have : s = ∅ ∨ ∃ x s', Seq s' ∧ s = s' ⁀' x := sseq.cases
    rcases this with (rfl | ⟨x, s, hs, rfl⟩)
    · exact hnil
    · exact hcons s x hs (ih s (hs.lt_seqCons x) hs)

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

@[simp] lemma mem_singleton_seq_iff (x y : V) : ⟪0, x⟫ ∈ !⟦y⟧ ↔ x = y := by simp [mem_seqCons_iff]

section

def _root_.LO.FirstOrder.Arithmetic.mkSeq₁Def : 𝚺₀.Semisentence 2 := .mkSigma
  “s x. !seqConsDef s 0 x”

instance mkSeq₁_defined : 𝚺₀-Function₁ (fun x : V ↦ !⟦x⟧) via mkSeq₁Def := .mk fun v ↦ by simp [mkSeq₁Def]; rfl

instance mkSeq₁_definable : 𝚺₀-Function₁ (fun x : V ↦ !⟦x⟧) := mkSeq₁_defined.to_definable

instance mkSeq₁_definable' (Γ) : Γ-Function₁ (fun x : V ↦ !⟦x⟧) := mkSeq₁_definable.of_zero

def _root_.LO.FirstOrder.Arithmetic.mkSeq₂Def : 𝚺₁.Semisentence 3 := .mkSigma
  “s x y. ∃ sx, !mkSeq₁Def sx x ∧ !seqConsDef s sx y”

instance mkSeq₂_defined : 𝚺₁-Function₂ (fun x y : V ↦ !⟦x, y⟧) via mkSeq₂Def := .mk fun v ↦ by simp [mkSeq₂Def]

instance mkSeq₂_definable : 𝚺₁-Function₂ (fun x y : V ↦ !⟦x, y⟧) := mkSeq₂_defined.to_definable

instance mkSeq₂_definable' (Γ m) : Γ-[m + 1]-Function₂ (fun x y : V ↦ !⟦x, y⟧) := mkSeq₂_definable.of_sigmaOne

end

theorem sigmaOne_skolem_seq {R : V → V → Prop} (hP : 𝚺₁-Relation R) {l}
    (H : ∀ x < l, ∃ y, R x y) : ∃ s, Seq s ∧ lh s = l ∧ ∀ i x, ⟪i, x⟫ ∈ s → R i x := by
  rcases sigmaOne_skolem hP (show ∀ x ∈ under l, ∃ y, R x y by simpa using H) with ⟨s, ms, sdom, h⟩
  have : Seq s := ⟨ms, l, sdom⟩
  exact ⟨s, this, by simpa [this.domain_eq] using sdom, h⟩

theorem sigmaOne_skolem_seq! {R : V → V → Prop} (hP : 𝚺₁-Relation R) {l}
    (H : ∀ x < l, ∃! y, R x y) : ∃! s, Seq s ∧ lh s = l ∧ ∀ i x, ⟪i, x⟫ ∈ s → R i x := by
  have : ∀ x < l, ∃ y, R x y := fun x hx ↦ (H x hx).exists
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

lemma mem_vectoSeq {n : ℕ} (v : Fin n → V) (i : Fin n) : ⟪(i : V), v i⟫ ∈ vecToSeq v := by
  induction' n with n ih
  · exact i.elim0
  · cases' i using Fin.lastCases with i
    · simp [vecToSeq, mem_seqCons_iff]
    · simpa [vecToSeq, mem_seqCons_iff] using Or.inr <| ih (v ·.castSucc) i

end seqToVec

end LO.FirstOrder.Arithmetic
