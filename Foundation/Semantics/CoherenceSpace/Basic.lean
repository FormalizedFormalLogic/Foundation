module

public import Foundation.Vorspiel

/-!
# Coherence space for denotational semantics of logics

reference:
- Jean-Yves Girard, Proofs and Types
- nLab, coherence space, https://ncatlab.org/nlab/show/coherence+space
-/

@[expose] public section

namespace LO

/-- A coherence space is a set equipped with a coherence relation `⁐`, which is reflexive and symmetric. -/
class CoherenceSpace (α : Type*) where
  /-- A coherence relation -/
  Coherence : α → α → Prop
  reflexive : Reflexive Coherence
  symmetric : Symmetric Coherence

namespace CoherenceSpace

infix:40 " ⁐ " => Coherence

variable {α : Type*} [CoherenceSpace α]

instance : Std.Refl (α := α) Coherence := ⟨reflexive⟩

instance : Std.Symm (α := α) Coherence := ⟨symmetric⟩

@[simp, refl, grind .] protected lemma Coherence.refl (x : α) : x ⁐ x := reflexive x

lemma Coherence.symm {x y : α} : x ⁐ y → y ⁐ x := fun h ↦ symmetric h

@[grind =] lemma Coherence.symm_iff {x y : α} : x ⁐ y ↔ y ⁐ x := ⟨symm, symm⟩

def Incoherence (x y : α) : Prop := ¬x ⁐ y ∨ x = y

infix:40 (priority := high) " ≍ " => Incoherence

@[simp, refl, grind .] lemma Incoherence.refl (x : α) : x ≍ x := by simp [Incoherence]

lemma Incoherence.symm {x y : α} : x ≍ y → y ≍ x := by
  intro h; cases h
  · left; grind
  · right; simp_all

@[grind =] lemma Incoherence.symm_iff {x y : α} : x ≍ y ↔ y ≍ x := ⟨symm, symm⟩

instance : Std.Refl (α := α) Incoherence := ⟨Incoherence.refl⟩

instance : Std.Symm (α := α) Incoherence := ⟨fun _ _ ↦ Incoherence.symm⟩

def StrictIncoherence (x y : α) : Prop := ¬x ⁐ y

infix:40 " ⌣ " => StrictIncoherence

lemma StrictIncoherence.iff_incoherence_ne (x y : α) : x ⌣ y ↔ x ≍ y ∧ x ≠ y := by
  simp [StrictIncoherence, Incoherence]; grind

lemma Incoherence.iff_strictIncoherence_or_eq (x y : α) : x ≍ y ↔ x ⌣ y ∨ x = y := by
  simp [StrictIncoherence, Incoherence]

lemma StrictIncoherence.symm {x y : α} : x ⌣ y → y ⌣ x := by
  simp [StrictIncoherence]; grind

@[grind =] lemma StrictIncoherence.symm_iff {x y : α} : x ⌣ y ↔ y ⌣ x := ⟨symm, symm⟩

instance : Std.Symm (α := α) StrictIncoherence := ⟨fun _ _ ↦ StrictIncoherence.symm⟩

def StrictCoherence (x y : α) : Prop := ¬x ≍ y

infix:40 " ⌢ " => StrictCoherence

lemma StrictCoherence.iff_coherence_ne (x y : α) : x ⌢ y ↔ x ⁐ y ∧ x ≠ y := by
  simp [StrictCoherence, Incoherence]

lemma Coherences.iff_strictCoherence_or_eq (x y : α) : x ⁐ y ↔ x ⌢ y ∨ x = y := by
  simp [StrictCoherence, Incoherence]; grind

lemma StrictCoherence.symm {x y : α} : x ⌢ y → y ⌢ x := by
  simp [StrictCoherence]; grind

@[grind =] lemma StrictCoherence.symm_iff {x y : α} : x ⌢ y ↔ y ⌢ x := ⟨symm, symm⟩

instance : Std.Symm (α := α) StrictCoherence := ⟨fun _ _ ↦ StrictCoherence.symm⟩

@[grind .] lemma trichotomous (x y : α) : x ⌢ y ∨ x = y ∨ x ⌣ y := by
  simp [StrictCoherence, StrictIncoherence, Incoherence]; grind

end CoherenceSpace

/-! ### Cliques and cocliques -/

def IsClique [CoherenceSpace α] (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, x ⁐ y

def IsCoclique [CoherenceSpace α] (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, x ≍ y

def Clique (α : Type*) [CoherenceSpace α] : Set (Set α) := {s | IsClique s}

namespace IsClique

variable {α : Type*} [CoherenceSpace α]

@[simp] lemma emptyset : IsClique (∅ : Set α) := fun _ ↦ by simp

@[simp] lemma singleton (x : α) : IsClique {x} := by
  rintro _ rfl _ rfl; simp

lemma of_subset {s u : Set α} (hs : IsClique s) (h : u ⊆ s) : IsClique u :=
  fun x hx y hy ↦ hs x (h hx) y (h hy)

@[simp] lemma insert_iff {x : α} {s : Set α} : IsClique (insert x s) ↔ (∀ y ∈ s, x ⁐ y) ∧ IsClique s := by
  constructor
  · intro h
    refine ⟨fun y hy ↦ h x (by simp) y (by simp [hy]), h.of_subset <| by simp⟩
  · rintro ⟨h, hs⟩
    intro y hy z hz
    have hy : y = x ∨ y ∈ s := by simpa using hy
    have hz : z = x ∨ z ∈ s := by simpa using hz
    rcases hy with (rfl | hy_) <;> rcases hz with (rfl | hz_)
    · simp
    · exact h z hz_
    · exact symm (h y hy_)
    · exact hs y hy_ z hz_

@[simp] lemma doubleton_iff {x y : α} : IsClique {x, y} ↔ x ⁐ y := by simp

lemma sUnion_of_union {M : Set (Set α)} (h : ∀ a ∈ M, ∀ b ∈ M, IsClique (a ∪ b)) : IsClique (⋃₀ M) := by
  intro x ⟨a, ha, hx⟩ y ⟨b, hb, hy⟩
  exact h a ha b hb x (by simp [hx]) y (by simp [hy])

end IsClique

namespace Clique

open IsClique

variable {α : Type*} [CoherenceSpace α]

@[simp] lemma mem_clique_iff {s : Set α} : s ∈ Clique α ↔ IsClique s := by rfl

def colimit' (s : Set (Set α)) (h : ∀ a ∈ s, IsClique a) (directed : DirectedOn (· ⊆ ·) s) : Clique α :=
  ⟨⋃₀ s, sUnion_of_union fun a ha b hb ↦ by
    have : ∃ c ∈ s, a ⊆ c ∧ b ⊆ c := directed a ha b hb
    rcases this with ⟨c, hcs, hac, hbc⟩
    refine (h c hcs).of_subset (Set.union_subset hac hbc)⟩

def colimit (s : Set (Clique α)) (directed : DirectedOn (· ≤ ·) s) : Clique α :=
  colimit' s (by simp; tauto) (directedOn_onFun_iff.mp directed)

@[simp] lemma val_colimit (s : Set (Clique α)) (directed : DirectedOn (· ≤ ·) s) :
    (colimit s directed : Set α) = ⋃₀ s := by rfl

instance : Min (Clique α) := ⟨fun a b ↦ ⟨a ∩ b, a.prop.of_subset <| by simp⟩⟩

@[simp] lemma inf_def (a b : Clique α) : ((a ⊓ b : Clique α) : Set α) = ↑a ∩ ↑b := by rfl

@[simp] lemma prop_iff (a : Clique α) : IsClique (a : Set α) := a.prop

lemma le_def (a b : Clique α) : a ≤ b ↔ (a : Set α) ⊆ b := by rfl

end Clique

/-! ### Basic coherence spaces -/

open CoherenceSpace

instance : Bot (CoherenceSpace α) := ⟨{
  Coherence := Eq
  reflexive := refl
  symmetric _ _ := symm }⟩

instance : Top (CoherenceSpace α) := ⟨{
  Coherence _ _ := True
  reflexive _ := by trivial
  symmetric _ _ _ := by trivial }⟩

inductive CoherenceSpace.Top

inductive CoherenceSpace.Zero

instance : CoherenceSpace CoherenceSpace.Top := ⊥

instance : CoherenceSpace CoherenceSpace.Zero := ⊥

inductive CoherenceSpace.One where
  | star : CoherenceSpace.One

inductive CoherenceSpace.Bot where
  | absurd : CoherenceSpace.Bot

instance : CoherenceSpace CoherenceSpace.One := ⊤

instance : CoherenceSpace CoherenceSpace.Bot := ⊤

/-- A empty set is a coherence space -/
instance : CoherenceSpace PEmpty := ⊥

/-- A singleton set is a coherence space -/
instance : CoherenceSpace Unit := ⊥

/-- A doubleton set is a coherence space -/
instance : CoherenceSpace Bool := ⊥

variable {α β : Type*} [CoherenceSpace α] [CoherenceSpace β]

/-! #### Linear negation -/

inductive LNeg (α : Type*) : Type _
  | mk : α → LNeg α

postfix:max (priority := low) "ᗮ" => LNeg

namespace LNeg

inductive Coherence : αᗮ → αᗮ → Prop
  | mk {a₀ a₁ : α} : a₀ ≍ a₁ → Coherence (mk a₀) (mk a₁)

instance : CoherenceSpace αᗮ where
  Coherence p q := Coherence p q
  reflexive p := by
    rcases p with ⟨a⟩
    exact Coherence.mk (by simp)
  symmetric p q := by
    rintro ⟨h⟩
    exact Coherence.mk (symm h)

lemma coherence_def (p q : αᗮ) : p ⁐ q ↔ Coherence p q := by rfl

@[simp] lemma mk_coherence_mk_iff {a₀ a₁ : α} :
    mk a₀ ⁐ mk a₁ ↔ a₀ ≍ a₁ := by
  constructor
  · rintro ⟨h⟩
    exact h
  · rintro h
    exact Coherence.mk h

end LNeg

/-! #### ⨂: Multiplicative conjunction -/

inductive Tensor (α β : Type*) : Type _
  | mk : α → β → Tensor α β

infixr:30 (priority := low) " ⨂ " => Tensor

namespace Tensor

inductive Coherence : α ⨂ β → α ⨂ β → Prop
  | pair {a₀ a₁ : α} {b₀ b₁ : β} : a₀ ⁐ a₁ → b₀ ⁐ b₁ → Coherence (mk a₀ b₀) (mk a₁ b₁)

instance : CoherenceSpace (α ⨂ β) where
  Coherence p q := Coherence p q
  reflexive p := by
    rcases p with ⟨a, b⟩
    exact Coherence.pair (by rfl) (by rfl)
  symmetric p q := by
    rintro ⟨ha, hb⟩
    exact Coherence.pair (symm ha) (symm hb)

lemma coherence_def (p q : α ⨂ β) : p ⁐ q ↔ Coherence p q := by rfl

@[simp] lemma mk_coherence_mk_iff {a₀ a₁ : α} {b₀ b₁ : β} :
    mk a₀ b₀ ⁐ mk a₁ b₁ ↔ a₀ ⁐ a₁ ∧ b₀ ⁐ b₁ := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact Coherence.pair ha hb

end Tensor

/-! #### ⅋: Multiplicative disjunction -/

inductive Par (α β : Type*) : Type _
  | mk : α → β → Par α β

infixr:30 (priority := low) " ⅋ " => Par

namespace Par

def toPair : α ⅋ β → α × β
| mk a b => (a, b)

inductive Coherence : α ⅋ β → α ⅋ β → Prop
  | refl (p) : Coherence p p
  | left {a₀ a₁ : α} {b₀ b₁ : β} : a₀ ⌢ a₁ → Coherence (mk a₀ b₀) (mk a₁ b₁)
  | right {a₀ a₁ : α} {b₀ b₁ : β} : b₀ ⌢ b₁ → Coherence (mk a₀ b₀) (mk a₁ b₁)

instance : CoherenceSpace (α ⅋ β) where
  Coherence p q := Coherence p q
  reflexive p := Coherence.refl _
  symmetric p q := by
    rintro (h | h | h)
    · exact Coherence.refl _
    · exact Coherence.left (symm h)
    · exact Coherence.right (symm h)

lemma coherence_def (p q : α ⅋ β) : p ⁐ q ↔ Coherence p q := by rfl

lemma mk_coherence_mk_iff {a₀ a₁ : α} {b₀ b₁ : β} :
    mk a₀ b₀ ⁐ mk a₁ b₁ ↔ (a₀ = a₁ ∧ b₀ = b₁) ∨ a₀ ⌢ a₁ ∨ b₀ ⌢ b₁ := by
  constructor
  · rintro (h | h | h)
    · simp
    · right; left; exact h
    · right; right; exact h
  · rintro (h | h | h)
    · simp [h]
    · exact Coherence.left h
    · exact Coherence.right h

@[simp] lemma mk_strictCoherence_mk_iff {a₀ a₁ : α} {b₀ b₁ : β} :
    mk a₀ b₀ ⌢ mk a₁ b₁ ↔ a₀ ⌢ a₁ ∨ b₀ ⌢ b₁ := by
  simp [StrictCoherence, Incoherence, mk_coherence_mk_iff]
  tauto

end Par

namespace CoherenceSpace

variable {ι : Type*} {ρ : ι → Type*} [(i : ι) → CoherenceSpace (ρ i)]

inductive ArrowParCoherence : (f g : (i : ι) → ρ i) → Prop
  | refl (f) : ArrowParCoherence f f
  | pointwise {f g : (i : ι) → ρ i} (i : ι) : f i ⌢ g i → ArrowParCoherence f g

instance arrowPar : CoherenceSpace ((i : ι) → ρ i) where
  Coherence f g := ArrowParCoherence f g
  reflexive f := ArrowParCoherence.refl f
  symmetric f g := by
    rintro (h | ⟨_, h⟩)
    · exact ArrowParCoherence.refl _
    · exact ArrowParCoherence.pointwise _ (symm h)

lemma arrowPar_coherence_def (f g : (i : ι) → ρ i) : f ⁐ g ↔ ArrowParCoherence f g := by rfl

lemma arrowPar_coherence_iff (f g : (i : ι) → ρ i) :
    f ⁐ g ↔ f = g ∨ ∃ i, f i ⌢ g i := by
  constructor
  · rintro (h | ⟨i, h⟩) <;> grind
  · rintro (rfl | ⟨i, h⟩)
    · exact ArrowParCoherence.refl _
    · exact ArrowParCoherence.pointwise i h


lemma arrowPar_strictCoherence_iff (f g : (i : ι) → ρ i) :
    f ⌢ g ↔ ∃ i, f i ⌢ g i := by
  simp [StrictCoherence.iff_coherence_ne, arrowPar_coherence_iff]
  grind

end CoherenceSpace

/-! #### &: Additive conjunction -/

/-- An additive conjunction of two types -/
inductive With (α β : Type*) : Type _
  | inl : α → With α β
  | inr : β → With α β

infixr:30 (priority := low) " & " => With

namespace With

inductive Coherence : α & β → α & β → Prop
  | inl {a₀ a₁ : α} : a₀ ⁐ a₁ → Coherence (inl a₀) (inl a₁)
  | inr {b₀ b₁ : β} : b₀ ⁐ b₁ → Coherence (inr b₀) (inr b₁)
  | inl_inr (a : α) (b : β) : Coherence (inl a) (inr b)
  | inr_inl (a : α) (b : β) : Coherence (inr b) (inl a)

/-- An additive conjunction of coherence spaces is also a coherence space -/
instance : CoherenceSpace (α & β) where
  Coherence p q := Coherence p q
  reflexive p := by
    rcases p
    · exact Coherence.inl (by rfl)
    · exact Coherence.inr (by rfl)
  symmetric p q := by
    rintro (h | h | _ | _)
    · exact Coherence.inl (symm h)
    · exact Coherence.inr (symm h)
    · exact Coherence.inr_inl _ _
    · exact Coherence.inl_inr _ _

lemma coherence_def (p q : α & β) : p ⁐ q ↔ Coherence p q := by rfl

end With

/-! #### ⨁: Additive disjunction -/

/-- An additive disjunction of two types -/
inductive Plus (α β : Type*) : Type _
  | inl : α → Plus α β
  | inr : β → Plus α β

infixr:30 " ⨁ " => Plus

namespace Plus

inductive Coherence : α ⨁ β → α ⨁ β → Prop
  | inl {a₀ a₁ : α} : a₀ ⁐ a₁ → Coherence (inl a₀) (inl a₁)
  | inr {b₀ b₁ : β} : b₀ ⁐ b₁ → Coherence (inr b₀) (inr b₁)

/-- An additive conjunction of coherence spaces is also a coherence space -/
instance : CoherenceSpace (α ⨁ β) where
  Coherence p q := Coherence p q
  reflexive p := by
    rcases p
    · exact Coherence.inl (by rfl)
    · exact Coherence.inr (by rfl)
  symmetric p q := by
    rintro (h | h)
    · exact Coherence.inl (symm h)
    · exact Coherence.inr (symm h)

lemma coherence_def (p q : α ⨁ β) : p ⁐ q ↔ Coherence p q := by rfl

end Plus

end LO
