module

public import Foundation.Vorspiel.AdjunctiveSet
public import Foundation.Vorspiel.ExistsUnique
public import Foundation.Vorspiel.Finset.Basic
public import Foundation.Vorspiel.Finset.Card
public import Foundation.Vorspiel.Fintype
public import Foundation.Vorspiel.Function
public import Foundation.Vorspiel.Graph
public import Foundation.Vorspiel.List.Chain
public import Foundation.Vorspiel.List.ChainI
public import Foundation.Vorspiel.Nat.Matrix
public import Foundation.Vorspiel.NotationClass
public import Foundation.Vorspiel.Order
public import Foundation.Vorspiel.Rel.Equality
public import Foundation.Vorspiel.Rel.Isolated
public import Foundation.Vorspiel.Rel.Universal
public import Foundation.Vorspiel.Rel.WCWF
public import Foundation.Vorspiel.Set.Basic
public import Foundation.Vorspiel.Set.Cofinite
public import Foundation.Vorspiel.Set.Fin
public import Foundation.Vorspiel.Small
public import Foundation.Vorspiel.String


/-!
# Coherence space for denotational semantics of logics

Reference: Jean-Yves Girard, Paul Taylor, Yves Lafont, Proofs and Types [G.T.L89]
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

def Point (α : Type*) [CoherenceSpace α] : Set (Set α) := {s | IsClique s}

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

namespace Point

open IsClique

variable {α : Type*} [CoherenceSpace α]

@[simp] lemma mem_clique_iff {s : Set α} : s ∈ Point α ↔ IsClique s := by rfl

def colimit' (s : Set (Set α)) (h : ∀ a ∈ s, IsClique a) (directed : DirectedOn (· ⊆ ·) s) : Point α :=
  ⟨⋃₀ s, sUnion_of_union fun a ha b hb ↦ by
    have : ∃ c ∈ s, a ⊆ c ∧ b ⊆ c := directed a ha b hb
    rcases this with ⟨c, hcs, hac, hbc⟩
    refine (h c hcs).of_subset (Set.union_subset hac hbc)⟩

def colimit (s : Set (Point α)) (directed : DirectedOn (· ≤ ·) s) : Point α :=
  colimit' s (by simp; tauto) (directedOn_onFun_iff.mp directed)

@[simp] lemma val_colimit (s : Set (Point α)) (directed : DirectedOn (· ≤ ·) s) :
    (colimit s directed : Set α) = ⋃₀ s := by rfl

instance : Min (Point α) := ⟨fun a b ↦ ⟨a ∩ b, a.prop.of_subset <| by simp⟩⟩

@[simp] lemma inf_def (a b : Point α) : ((a ⊓ b : Point α) : Set α) = ↑a ∩ ↑b := by rfl

@[simp] lemma prop_iff (a : Point α) : IsClique (a : Set α) := a.prop

lemma le_def (a b : Point α) : a ≤ b ↔ (a : Set α) ⊆ b := by rfl

end Point

/-! ### Basic coherence spaces -/

namespace CoherenceSpace

instance : Bot (CoherenceSpace α) := ⟨{
  Coherence := Eq
  reflexive := refl
  symmetric _ _ := symm }⟩

instance : Top (CoherenceSpace α) := ⟨{
  Coherence _ _ := True
  reflexive _ := by trivial
  symmetric _ _ _ := by trivial }⟩

inductive Top

inductive Zero

instance : CoherenceSpace Top := ⊥

instance : CoherenceSpace CoherenceSpace.Zero := ⊥

inductive One where
  | star : One

inductive Bot where
  | absurd : CoherenceSpace.Bot

instance : CoherenceSpace One := ⊤

instance : CoherenceSpace Bot := ⊤

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

@[simp] lemma mk_strictCoherence_mk_iff {a₀ a₁ : α} :
    mk a₀ ⌢ mk a₁ ↔ a₀ ⌣ a₁ := by
  simp [StrictCoherence.iff_coherence_ne,
    StrictIncoherence.iff_incoherence_ne, mk_coherence_mk_iff]

@[simp] lemma mk_incoherence_mk_iff {a₀ a₁ : α} :
    mk a₀ ≍ mk a₁ ↔ a₀ ⁐ a₁ := by
  simp [Incoherence, mk_coherence_mk_iff]; grind

@[simp] lemma mk_strictIncoherence_mk_iff {a₀ a₁ : α} :
    mk a₀ ⌣ mk a₁ ↔ a₀ ⌢ a₁ := by
  simp [StrictIncoherence, mk_coherence_mk_iff]; rfl

end LNeg

/-! #### ⨂: Multiplicative conjunction -/

inductive Tensor (α β : Type*) : Type _
  | mk : α → β → Tensor α β

namespace Tensor

inductive Coherence : Tensor α β → Tensor α β → Prop
  | pair {a₀ a₁ : α} {b₀ b₁ : β} : a₀ ⁐ a₁ → b₀ ⁐ b₁ → Coherence (mk a₀ b₀) (mk a₁ b₁)

instance : CoherenceSpace (Tensor α β) where
  Coherence p q := Coherence p q
  reflexive p := by
    rcases p with ⟨a, b⟩
    exact Coherence.pair (by rfl) (by rfl)
  symmetric p q := by
    rintro ⟨ha, hb⟩
    exact Coherence.pair (symm ha) (symm hb)

lemma coherence_def (p q : Tensor α β) : p ⁐ q ↔ Coherence p q := by rfl

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

namespace Par

def toPair : Par α β → α × β
| mk a b => (a, b)

inductive Coherence : Par α β → Par α β → Prop
  | refl (p) : Coherence p p
  | left {a₀ a₁ : α} {b₀ b₁ : β} : a₀ ⌢ a₁ → Coherence (mk a₀ b₀) (mk a₁ b₁)
  | right {a₀ a₁ : α} {b₀ b₁ : β} : b₀ ⌢ b₁ → Coherence (mk a₀ b₀) (mk a₁ b₁)

instance : CoherenceSpace (Par α β) where
  Coherence p q := Coherence p q
  reflexive p := Coherence.refl _
  symmetric p q := by
    rintro (h | h | h)
    · exact Coherence.refl _
    · exact Coherence.left (symm h)
    · exact Coherence.right (symm h)

lemma coherence_def (p q : Par α β) : p ⁐ q ↔ Coherence p q := by rfl

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

section ArrowPar

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

end ArrowPar

/-! #### ⊸: Linear implication -/

abbrev Lolli (α β : Type*) : Type _ := Par αᗮ β

namespace Lolli

variable {α β : Type*} [CoherenceSpace α] [CoherenceSpace β]

protected def id : Point (Lolli α α) := ⟨{.mk (.mk a) a | a}, by
  rintro ⟨a₀, n₀⟩ h₀ ⟨a₁, n₁⟩ h₁
  have : .mk n₀ = a₀ := by simpa using h₀
  rcases this
  have : .mk n₁ = a₁ := by simpa using h₁
  rcases this
  simp [Par.mk_coherence_mk_iff]; grind⟩

end Lolli

/-! #### &: Additive conjunction -/

/-- An additive conjunction of two types -/
inductive With (α β : Type*) : Type _
  | inl : α → With α β
  | inr : β → With α β

namespace With

inductive Coherence : With α β → With α β → Prop
  | inl {a₀ a₁ : α} : a₀ ⁐ a₁ → Coherence (inl a₀) (inl a₁)
  | inr {b₀ b₁ : β} : b₀ ⁐ b₁ → Coherence (inr b₀) (inr b₁)
  | inl_inr (a : α) (b : β) : Coherence (inl a) (inr b)
  | inr_inl (a : α) (b : β) : Coherence (inr b) (inl a)

/-- An additive conjunction of coherence spaces is also a coherence space -/
instance : CoherenceSpace (With α β) where
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

lemma coherence_def (p q : With α β) : p ⁐ q ↔ Coherence p q := by rfl

end With

inductive BigWith {ι : Type*} (ρ : ι → Type*) : Type _
  | mk : ρ i → BigWith ρ

namespace BigWith

variable {ι : Type*} {ρ : ι → Type*} [(i : ι) → CoherenceSpace (ρ i)]

inductive Coherence : BigWith ρ → BigWith ρ → Prop
  | mk {a₀ a₁ : ρ i} : a₀ ⁐ a₁ → Coherence (mk a₀) (mk a₁)
  | of_ne (a : ρ i) (b : ρ j) : i ≠ j → Coherence (mk a) (mk b)

instance : CoherenceSpace (BigWith ρ) where
  Coherence p q := p.Coherence q
  reflexive p := by
    rcases p with ⟨a⟩
    exact Coherence.mk (by rfl)
  symmetric p q := by
    rintro (h | ⟨_, _, h⟩)
    · exact Coherence.mk (symm h)
    · exact Coherence.of_ne _ _ (Ne.symm h)

lemma coherence_def (p q : BigWith ρ) : p ⁐ q ↔ Coherence p q := by rfl

end BigWith

/-! #### ⨁: Additive disjunction -/

/-- An additive disjunction of two types -/
inductive Plus (α β : Type*) : Type _
  | inl : α → Plus α β
  | inr : β → Plus α β

namespace Plus

inductive Coherence : Plus α β → Plus α β → Prop
  | inl {a₀ a₁ : α} : a₀ ⁐ a₁ → Coherence (inl a₀) (inl a₁)
  | inr {b₀ b₁ : β} : b₀ ⁐ b₁ → Coherence (inr b₀) (inr b₁)

/-- An additive conjunction of coherence spaces is also a coherence space -/
instance : CoherenceSpace (Plus α β) where
  Coherence p q := Coherence p q
  reflexive p := by
    rcases p
    · exact Coherence.inl (by rfl)
    · exact Coherence.inr (by rfl)
  symmetric p q := by
    rintro (h | h)
    · exact Coherence.inl (symm h)
    · exact Coherence.inr (symm h)

lemma coherence_def (p q : Plus α β) : p ⁐ q ↔ Coherence p q := by rfl

end Plus

inductive BigPlus {ι : Type*} (ρ : ι → Type*) : Type _
  | mk : ρ i → BigPlus ρ

namespace BigPlus

variable {ι : Type*} {ρ : ι → Type*} [(i : ι) → CoherenceSpace (ρ i)]

inductive Coherence : BigPlus ρ → BigPlus ρ → Prop
  | mk {a₀ a₁ : ρ i} : a₀ ⁐ a₁ → Coherence (mk a₀) (mk a₁)

instance : CoherenceSpace (BigPlus ρ) where
  Coherence p q := p.Coherence q
  reflexive p := by
    rcases p with ⟨a⟩
    exact Coherence.mk (by rfl)
  symmetric p q := by
    rintro ⟨h⟩
    exact Coherence.mk (symm h)

lemma coherence_def (p q : BigPlus ρ) : p ⁐ q ↔ Coherence p q := by rfl

end BigPlus

end CoherenceSpace

end LO
