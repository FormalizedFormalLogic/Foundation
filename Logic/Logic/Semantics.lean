import Logic.Logic.LogicSymbol

/-!
# Basic definitions and properties of semantics-related notions

This file defines the semantics of formulas based on Tarski's truth definitions.
Also provides 𝓜 characterization of compactness.

## Main Definitions
* `LO.Semantics`: The realization of 𝓜 formula.
* `LO.Compact`: The semantic compactness of logic.

-/

namespace LO

class Semantics (F : outParam Type*) (M : Type*) where
  Realize : M → F → Prop

variable {M : Type*} {F : Type*} [LogicalConnective F] [𝓢 : Semantics F M]

namespace Semantics

infix:45 " ⊧ " => Realize

section

variable (M)

protected class Top where
  realize_top (𝓜 : M) : 𝓜 ⊧ (⊤ : F)

protected class Bot where
  realize_bot (𝓜 : M) : ¬𝓜 ⊧ (⊥ : F)

class Tarski extends Semantics.Top M, Semantics.Bot M where
  realize_not (𝓜 : M) (p : F) : 𝓜 ⊧ ~p ↔ ¬𝓜 ⊧ p
  realize_imp {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ q ↔ (𝓜 ⊧ p → 𝓜 ⊧ q)
  realize_and {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⋏ q ↔ 𝓜 ⊧ p ∧ 𝓜 ⊧ q
  realize_or {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⋎ q ↔ 𝓜 ⊧ p ∨ 𝓜 ⊧ q

attribute [simp]
  Top.realize_top
  Bot.realize_bot
  Tarski.realize_not
  Tarski.realize_imp
  Tarski.realize_and
  Tarski.realize_or

variable {M}

variable [Tarski M]

variable {𝓜 : M}

@[simp] lemma realize_iff {p q : F} :
    𝓜 ⊧ p ⟷ q ↔ ((𝓜 ⊧ p) ↔ (𝓜 ⊧ q)) := by
  simp [LogicalConnective.iff, iff_iff_implies_and_implies]

@[simp] lemma realize_list_conj {l : List F} :
    𝓜 ⊧ l.conj ↔ ∀ p ∈ l, 𝓜 ⊧ p := by induction l <;> simp [*]

@[simp] lemma realize_finset_conj {s : Finset F} :
    𝓜 ⊧ s.conj ↔ ∀ p ∈ s, 𝓜 ⊧ p := by simp [Finset.conj]

@[simp] lemma realize_list_disj {l : List F} :
    𝓜 ⊧ l.disj ↔ ∃ p ∈ l, 𝓜 ⊧ p := by induction l <;> simp [*]

@[simp] lemma realize_finset_disj {s : Finset F} :
    𝓜 ⊧ s.disj ↔ ∃ p ∈ s, 𝓜 ⊧ p := by simp [Finset.disj]

end

class RealizeSet (𝓜 : M) (T : Set F) : Prop where
  RealizeSet : ∀ ⦃f⦄, f ∈ T → Realize 𝓜 f

infix:45 " ⊧* " => RealizeSet

variable (M)

def Valid (f : F) : Prop := ∀ 𝓜 : M, 𝓜 ⊧ f

def Satisfiable (T : Set F) : Prop := ∃ 𝓜 : M, 𝓜 ⊧* T

def models (T : Set F) : Set M := {𝓜 | 𝓜 ⊧* T}

variable {M}

def theory (𝓜 : M) : Set F := {f | 𝓜 ⊧ f}

class Meaningful (𝓜 : M) : Prop where
  exists_unrealize : ∃ f, ¬𝓜 ⊧ f

instance [Semantics.Bot M] (𝓜 : M) : Meaningful 𝓜 := ⟨⟨⊥, by simp⟩⟩

lemma meaningful_iff {𝓜 : M} : Meaningful 𝓜 ↔ ∃ f, ¬𝓜 ⊧ f :=
  ⟨by rintro ⟨h⟩; exact h, fun h ↦ ⟨h⟩⟩

lemma not_meaningful_iff (𝓜 : M) : ¬Meaningful 𝓜 ↔ ∀ f, 𝓜 ⊧ f := by simp [meaningful_iff]

lemma realizeSet_iff {𝓜 : M} {T : Set F} : 𝓜 ⊧* T ↔ ∀ ⦃f⦄, f ∈ T → Realize 𝓜 f :=
  ⟨by rintro ⟨h⟩; exact h, by intro h; exact ⟨h⟩⟩

lemma not_satisfiable_finset [Tarski M] [DecidableEq F] (t : Finset F) :
    ¬Satisfiable M (t : Set F) ↔ Valid M (t.image (~·)).disj := by
  simp [Satisfiable, realizeSet_iff, Valid, Finset.map_disj]

lemma satisfiableSet_iff_models_nonempty {T : Set F} :
    Satisfiable M T ↔ (models M T).Nonempty :=
  ⟨by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩, by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩⟩

namespace RealizeSet

lemma realize {T : Set F} (𝓜 : M) [𝓜 ⊧* T] (hf : f ∈ T) : 𝓜 ⊧ f :=
  RealizeSet hf

lemma of_subset {T U : Set F} {𝓜 : M} (h : 𝓜 ⊧* U) (ss : T ⊆ U) : 𝓜 ⊧* T :=
  ⟨fun _ hf => h.RealizeSet (ss hf)⟩

lemma of_subset' {T U : Set F} {𝓜 : M} [𝓜 ⊧* U] (ss : T ⊆ U) : 𝓜 ⊧* T :=
  of_subset (𝓜 := 𝓜) inferInstance ss

instance empty' (𝓜 : M) : 𝓜 ⊧* (∅ : Set F) := ⟨fun p => by simp⟩

@[simp] lemma empty (𝓜 : M) : 𝓜 ⊧* (∅ : Set F) := ⟨fun p => by simp⟩

@[simp] lemma singleton_iff {f : F} {𝓜 : M} :
    𝓜 ⊧* {f} ↔ 𝓜 ⊧ f := by simp [realizeSet_iff]

@[simp] lemma insert_iff {T : Set F} {f : F} {𝓜 : M} :
    𝓜 ⊧* insert f T ↔ 𝓜 ⊧ f ∧ 𝓜 ⊧* T := by
  simp [realizeSet_iff]

@[simp] lemma union_iff {T U : Set F} {𝓜 : M} :
    𝓜 ⊧* T ∪ U ↔ 𝓜 ⊧* T ∧ 𝓜 ⊧* U := by
  simp [realizeSet_iff]
  exact
  ⟨fun h => ⟨fun f hf => h (Or.inl hf), fun f hf => h (Or.inr hf)⟩,
   by rintro ⟨h₁, h₂⟩ f (h | h); exact h₁ h; exact h₂ h⟩

@[simp] lemma image_iff {ι} {f : ι → F} {A : Set ι} {𝓜 : M} :
    𝓜 ⊧* f '' A ↔ ∀ i ∈ A, 𝓜 ⊧ (f i) := by simp [realizeSet_iff]

@[simp] lemma range_iff {ι} {f : ι → F} {𝓜 : M} :
    𝓜 ⊧* Set.range f ↔ ∀ i, 𝓜 ⊧ (f i) := by simp [realizeSet_iff]

@[simp] lemma setOf_iff {P : F → Prop} {𝓜 : M} :
    𝓜 ⊧* setOf P ↔ ∀ f, P f → 𝓜 ⊧ f := by simp [realizeSet_iff]

end RealizeSet

lemma valid_neg_iff [Tarski M] (f : F) : Valid M (~f) ↔ ¬Satisfiable M {f} := by simp [Valid, Satisfiable]

lemma Satisfiable.of_subset {T U : Set F} (h : Satisfiable M U) (ss : T ⊆ U) : Satisfiable M T :=
  by rcases h with ⟨𝓜, h⟩; exact ⟨𝓜, RealizeSet.of_subset h ss⟩

variable (M)

instance [Semantics F M] : Semantics F (Set M) := ⟨fun s f ↦ ∀ 𝓜 ∈ s, 𝓜 ⊧ f⟩

@[simp] lemma empty_models (f : F) : (∅ : Set M) ⊧ f := by rintro h; simp

abbrev Consequence (T : Set F) (f : F) : Prop := models M T ⊧ f

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
notation T:45 " ⊨[" M "] " p:46 => Consequence M T p

variable {M}

lemma set_models_iff {s : Set M} : s ⊧ f ↔ ∀ 𝓜 ∈ s, 𝓜 ⊧ f := iff_of_eq rfl

instance [Semantics.Top M] : Semantics.Top (Set M) := ⟨fun s ↦ by simp [set_models_iff]⟩

lemma set_meaningful_iff_nonempty [∀ 𝓜 : M, Meaningful 𝓜] {s : Set M} : Meaningful s ↔ s.Nonempty :=
  ⟨by rintro ⟨f, hf⟩; by_contra A; rcases Set.not_nonempty_iff_eq_empty.mp A; simp at hf,
   by rintro ⟨𝓜, h𝓜⟩
      rcases Meaningful.exists_unrealize (𝓜 := 𝓜) with ⟨f, hf⟩
      exact ⟨f, by simp [set_models_iff]; exact ⟨𝓜, h𝓜, hf⟩⟩⟩

lemma meaningful_iff_satisfiableSet [∀ 𝓜 : M, Meaningful 𝓜] : Satisfiable M T ↔ Meaningful (models M T) := by
  simp [set_meaningful_iff_nonempty, satisfiableSet_iff_models_nonempty]

lemma consequence_iff {T : Set F} {f} : T ⊨[M] f ↔ ∀ {𝓜 : M}, 𝓜 ⊧* T → 𝓜 ⊧ f := iff_of_eq rfl

lemma consequence_iff' {T : Set F} {f : F} : T ⊨[M] f ↔ (∀ (𝓜 : M) [𝓜 ⊧* T], 𝓜 ⊧ f) :=
  ⟨fun h _ _ => consequence_iff.mp h inferInstance, fun H 𝓜 hs => @H 𝓜 hs⟩

lemma consequence_iff_not_satisfiable [Tarski M] {f : F} :
    T ⊨[M] f ↔ ¬Satisfiable M (insert (~f) T) := by
  simp [consequence_iff, Satisfiable]; constructor
  · intro h 𝓜 hf hT; have : 𝓜 ⊧ f := h hT; contradiction
  · intro h 𝓜; contrapose; exact h 𝓜

lemma weakening {T U : Set F} {f} (h : T ⊨[M] f) (ss : T ⊆ U) : U ⊨[M] f :=
  consequence_iff.mpr fun hs => consequence_iff.mp h (RealizeSet.of_subset hs ss)

lemma of_mem {T : Set F} {f} (h : f ∈ T) : T ⊨[M] f := fun _ hs => hs.RealizeSet h

end Semantics

def Cumulative (T : ℕ → Set F) : Prop := ∀ s, T s ⊆ T (s + 1)

namespace Cumulative

lemma subset_of_le {T : ℕ → Set F} (H : Cumulative T)
    {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : T s₁ ⊆ T s₂ := by
  suffices ∀ s d, T s ⊆ T (s + d) by
    simpa[Nat.add_sub_of_le h] using this s₁ (s₂ - s₁)
  intro s d
  induction' d with d ih
  · simp; rfl
  · simpa[Nat.add_succ] using subset_trans ih (H (s + d))

lemma finset_mem {T : ℕ → Set F}
    (H : Cumulative T) {u : Finset F} (hu : ↑u ⊆ ⋃ s, T s) : ∃ s, ↑u ⊆ T s := by
  haveI := Classical.decEq
  induction u using Finset.induction
  case empty => exact ⟨0, by simp⟩
  case insert f u _ ih =>
    simp at hu
    have : ∃ s, ↑u ⊆ T s := ih (subset_trans (Set.subset_insert _ _) hu)
    rcases this with ⟨s, hs⟩
    have : ∃ s', f ∈ T s' := by simpa using (Set.insert_subset_iff.mp hu).1
    rcases this with ⟨s', hs'⟩
    exact ⟨max s s', by
      simp; exact Set.insert_subset
        (subset_of_le H (Nat.le_max_right s s') hs')
        (subset_trans hs (subset_of_le H $ Nat.le_max_left s s'))⟩

end Cumulative

variable (M F)

class Compact : Prop where
  compact {T : Set F} :
    Semantics.Satisfiable M T ↔ (∀ u : Finset F, ↑u ⊆ T → Semantics.Satisfiable M (u : Set F))

variable {F}

namespace Compact

variable [Compact M F]

variable {𝓜 : M}

lemma conseq_compact [Semantics.Tarski M] [DecidableEq F] {f : F} :
    T ⊨[M] f ↔ ∃ u : Finset F, ↑u ⊆ T ∧ u ⊨[M] f := by
  simp [Semantics.consequence_iff_not_satisfiable, compact (T := insert (~f) T)]
  constructor
  · intro ⟨u, ss, hu⟩
    exact ⟨Finset.erase u (~f), by simp [ss],
      by simp; intro h; exact hu (Semantics.Satisfiable.of_subset h (by simp))⟩
  · intro ⟨u, ss, hu⟩
    exact ⟨insert (~f) u,
      by simpa using Set.insert_subset_insert ss, by simpa using hu⟩

lemma compact_cumulative {T : ℕ → Set F} (hT : Cumulative T) :
    Semantics.Satisfiable M (⋃ s, T s) ↔ ∀ s, Semantics.Satisfiable M (T s) :=
  ⟨by intro H s
      exact H.of_subset (Set.subset_iUnion T s),
   by intro H
      apply compact.mpr
      intro u hu
      rcases hT.finset_mem hu with ⟨s, hs⟩
      exact (H s).of_subset hs ⟩

end Compact

end LO
