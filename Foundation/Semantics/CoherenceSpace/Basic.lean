import Foundation.Vorspiel.Vorspiel

/-!
# Coherence space for denotational semantics of logics

reference:
- Jean-Yves Girard, Proofs and Types
- nLab, coherence space, https://ncatlab.org/nlab/show/coherence+space
-/

namespace DirectedOn

variable {α : Type*} {r : α → α → Prop}

lemma of_terminal_elem (hu : u ∈ s) (h : ∀ x ∈ s, r x u) : DirectedOn r s := by
  intro x hx y hy
  exact ⟨u, hu, h x hx, h y hy⟩

end DirectedOn

namespace LO

/-- A coherence space is a set equipped with a coherence relation `◡`, which is reflexive and symmetric. -/
class CoherenceSpace (α : Type*) where
  /-- A coherence relation -/
  Rel : α → α → Prop
  reflexive : Reflexive Rel
  symmetric : Symmetric Rel

namespace CoherenceSpace

infix:40 " ◡ " => Rel

variable {α : Type*} [CoherenceSpace α]

instance : IsRefl α Rel := ⟨reflexive⟩

instance : IsSymm α Rel := ⟨symmetric⟩

@[simp, refl] protected lemma Rel.refl (x : α) : x ◡ x := reflexive x

@[grind .] lemma Rel.symm {x y : α} : x ◡ y → y ◡ x := fun h ↦ symmetric h

lemma Rel.symm_iff {x y : α} : x ◡ y ↔ y ◡ x := ⟨symm, symm⟩

end CoherenceSpace

/-! ### Cliques and cocliques -/

def IsClique [CoherenceSpace α] (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, x ◡ y

def IsCoclique [CoherenceSpace α] (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, x ◡ y → x = y

def Clique (α : Type*) [CoherenceSpace α] : Set (Set α) := {s | IsClique s}

namespace IsClique

variable {α : Type*} [CoherenceSpace α]

@[simp] lemma emptyset : IsClique (∅ : Set α) := fun _ ↦ by simp

@[simp] lemma singleton (x : α) : IsClique {x} := by
  rintro _ rfl _ rfl; simp

lemma of_subset {s u : Set α} (hs : IsClique s) (h : u ⊆ s) : IsClique u :=
  fun x hx y hy ↦ hs x (h hx) y (h hy)

@[simp] lemma insert_iff {x : α} {s : Set α} : IsClique (insert x s) ↔ (∀ y ∈ s, x ◡ y) ∧ IsClique s := by
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

@[simp] lemma doubleton_iff {x y : α} : IsClique {x, y} ↔ x ◡ y := by simp

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

@[ext]
structure StableFunction (α β : Type*) [CoherenceSpace α] [CoherenceSpace β] where
  toFun : Clique α → Clique β
  monotone' {a b : Clique α} : a ≤ b → toFun a ≤ toFun b
  colimit' (s : Set (Clique α)) (ds : DirectedOn (· ≤ ·) s) :
    toFun (Clique.colimit s ds) = Clique.colimit (toFun '' s) (ds.mono_comp @monotone')
  pullback' {a b : Clique α} : IsClique (a ∪ b : Set α) → toFun (a ⊓ b) = toFun a ⊓ toFun b

infix:30 " ⊸ " => StableFunction

attribute [coe] StableFunction.toFun

namespace StableFunction

variable {α β γ δ : Type*} [CoherenceSpace α] [CoherenceSpace β] [CoherenceSpace γ] [CoherenceSpace δ]

instance : FunLike (α ⊸ β) (Clique α) (Clique β) where
  coe := toFun
  coe_injective' _ _ := StableFunction.ext

lemma monotone {f : α ⊸ β} {a b : Clique α} : a ≤ b → f a ≤ f b := f.monotone'

lemma colimit {f : α ⊸ β} (s : Set (Clique α)) (ds : DirectedOn (· ≤ ·) s) :
    f (Clique.colimit s ds) = Clique.colimit (f '' s) (ds.mono_comp @f.monotone) := f.colimit' s ds

lemma pullback {f : α ⊸ β} {a b : Clique α} (h : IsClique (a ∪ b : Set α)) : f (a ⊓ b) = f a ⊓ f b := f.pullback' h

lemma union_clique {f : α ⊸ β} {a b : Clique α} (h : IsClique (a ∪ b : Set α)) : IsClique (f a ∪ f b : Set β) := by
  let u : Clique α := ⟨a ∪ b, h⟩
  have directed : DirectedOn (· ≤ ·) {a, b, u} :=
    DirectedOn.of_terminal_elem (u := u) (by simp) (by simp [u, Clique.le_def])
  have := f.colimit {a, b, u} directed
  have : (f (Clique.colimit {a, b, u} directed) : Set β) = ↑(f a) ∪ ↑(f b) ∪ ↑(f u) := by
    simpa [-Set.sUnion_image, Set.image_insert_eq, ←Set.union_assoc] using congr_arg Subtype.val this
  have : IsClique (↑(f a) ∪ ↑(f b) ∪ ↑(f u) : Set β) := by simp [←this]
  refine this.of_subset (by simp)

lemma ext_func {f g : α ⊸ β} : (f : Clique α → Clique β) = g → f = g := DFunLike.coe_fn_eq.mp

protected def id (α : Type*) [CoherenceSpace α] : α ⊸ α where
  toFun := id
  monotone' h := h
  colimit' s ds := by simp
  pullback' h := by simp

@[simp] lemma coe_id : (StableFunction.id α : Clique α → Clique α) = id := rfl

protected def comp (g : β ⊸ γ) (f : α ⊸ β) : α ⊸ γ where
  toFun := g ∘ f
  monotone' h := g.monotone (f.monotone h)
  colimit' s ds := by simp [colimit, Set.image_image]
  pullback' h := by simp [f.pullback h, g.pullback (union_clique h)]

@[simp] lemma coe_comp_def (g : β ⊸ γ) (f : α ⊸ β) : (g.comp f : Clique α → Clique γ) = g ∘ f := rfl

@[simp] lemma id_comp (f : α ⊸ β) : (StableFunction.id β).comp f = f := ext_func (by simp)

@[simp] lemma comp_id (f : α ⊸ β) : f.comp (StableFunction.id α) = f := ext_func (by simp)

lemma comp_assoc (h : γ ⊸ δ) (g : β ⊸ γ) (f : α ⊸ β) :
    h.comp (g.comp f) = (h.comp g).comp f := ext_func <| by simp; rfl

end StableFunction

instance : Bot (CoherenceSpace α) := ⟨{
  Rel := Eq
  reflexive := refl
  symmetric _ _ := symm }⟩

instance : Top (CoherenceSpace α) := ⟨{
  Rel _ _ := True
  reflexive _ := by trivial
  symmetric _ _ _ := by trivial }⟩

/-- A empty set is a coherence space -/
instance : CoherenceSpace PEmpty := ⊥

/-- A singleton set is a coherence space -/
instance : CoherenceSpace Unit := ⊥

/-- A doubleton set is a coherence space -/
instance : CoherenceSpace Bool := ⊥

/-- An additive conjunction, or a direct product of two types -/
inductive With (α β : Type*) : Type _
  | inl : α → With α β
  | inr : β → With α β

infixr:30 (priority := low) " & " => With

/-- An additive conjunction of coherence spaces is also a coherence space -/
instance [CoherenceSpace α] [CoherenceSpace β] : CoherenceSpace (α & β) where
  Rel p q :=
    match p, q with
    | .inl a₁, .inl a₂ => a₁ ◡ a₂
    | .inl a₁, .inr b₂ => True
    | .inr b₁, .inl a₂ => True
    | .inr b₁, .inr b₂ => b₁ ◡ b₂
  reflexive p := by rcases p <;> simp
  symmetric p q := by
    rcases p <;> rcases q <;> grind

end LO
