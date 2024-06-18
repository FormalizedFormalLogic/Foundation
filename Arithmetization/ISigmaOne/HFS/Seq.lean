import Arithmetization.ISigmaOne.HFS.Basic

/-!

# Sequence

-/

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

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

lemma Seq.lh_eq_of {s : M} (H : Seq s) {l} (h : domain s = under l) : lh s = l := by
  simpa [H.domain_eq] using h

lemma Seq.lt_lh_iff {s : M} (h : Seq s) {i} : i < lh s ↔ i ∈ domain s := by simp [h.domain_eq]

lemma Seq.lt_lh_of_mem {s : M} (h : Seq s) {i x} (hix : ⟪i, x⟫ ∈ s) : i < lh s := by simp [h.lt_lh_iff, mem_domain_iff]; exact ⟨x, hix⟩

def seqCons (s x : M) : M := insert ⟪lh s, x⟫ s

-- infixr:67 " ::ˢ " => seqCons

infixr:67 " ⁀' " => seqCons

@[simp] lemma seq_empty : Seq (∅ : M) := ⟨by simp, 0, by simp⟩

@[simp] lemma lh_empty : lh (∅ : M) = 0 := by
  have : under (lh ∅ : M) = under 0 := by simpa using Eq.symm <| Seq.domain_eq (M := M) (s := ∅) (by simp)
  exact under_inj.mp this

lemma Seq.isempty_of_lh_eq_zero {s : M} (Hs : Seq s) (h : lh s = 0) : s = ∅ := by simpa [h] using Hs.domain_eq

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

lemma seqCons_absolute (s a : ℕ) : ((s ⁀' a : ℕ) : M) = (s : M) ⁀' (a : M) := by
  simpa using DefinedFunction.shigmaZero_absolute_func M seqCons_defined seqCons_defined ![s, a]

end

lemma Seq.restr {s : M} (H : Seq s) {i : M} (hi : i ≤ lh s) : Seq (s ↾ under i) :=
  ⟨H.isMapping.restr (under i), i, domain_restr_of_subset_domain (by simp [H.domain_eq, hi])⟩

lemma Seq.restr_lh {s : M} (H : Seq s) {i : M} (hi : i ≤ lh s) : lh (s ↾ under i) = i :=
  (H.restr hi).lh_eq_of (domain_restr_of_subset_domain <| by simp [H.domain_eq, hi])

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

lemma Seq.lh_ext {s₁ s₂ : M} (H₁ : Seq s₁) (H₂ : Seq s₂) (h : lh s₁ = lh s₂)
    (H : ∀ i x₁ x₂, ⟪i, x₁⟫ ∈ s₁ → ⟪i, x₂⟫ ∈ s₂ → x₁ = x₂) : s₁ = s₂ := H₁.eq_of_eq_of_subset H₂ h <| subset_pair <| by
      intro i x hx
      have hi : i < lh s₂ := by simpa [← h] using H₁.lt_lh_of_mem hx
      rcases H i _ _ hx (H₂.nth_mem hi)
      simp

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
  | `(!⟨$terms:term,*, $term:term⟩) => `(seqCons !⟨$terms,*⟩ $term)
  | `(!⟨$term:term⟩) => `(seqCons ∅ $term)
  | `(!⟨⟩) => `(∅)

@[app_unexpander seqCons]
def vecConsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term !⟨$term2, $terms,*⟩) => `(!⟨$term, $term2, $terms,*⟩)
  | `($_ $term !⟨$term2⟩) => `(!⟨$term, $term2⟩)
  | `($_ $term ∅) => `(!⟨$term⟩)
  | _ => throw ()

@[simp] lemma singleton_seq (x : M) : Seq !⟨x⟩ := by apply Seq.seqCons; simp

/-
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
-/

theorem sigmaOne_skolem_seq {R : M → M → Prop} (hP : 𝚺₁-Relation R) {l}
    (H : ∀ x < l, ∃ y, R x y) : ∃ s, Seq s ∧ lh s = l ∧ ∀ i x, ⟪i, x⟫ ∈ s → R i x := by
  rcases sigmaOne_skolem hP (show ∀ x ∈ under l, ∃ y, R x y by simpa using H) with ⟨s, ms, sdom, h⟩
  have : Seq s := ⟨ms, l, sdom⟩
  exact ⟨s, this, by simpa [this.domain_eq] using sdom, h⟩

end LO.FirstOrder.Arith.Model

end
