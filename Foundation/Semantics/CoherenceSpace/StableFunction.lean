module

public import Foundation.Semantics.CoherenceSpace.Basic

/-!
# Stable functions

reference:
- Jean-Yves Girard, Proofs and Types
-/

@[expose] public section

namespace DirectedOn

variable {α : Type*} {r : α → α → Prop}

lemma of_terminal_elem (hu : u ∈ s) (h : ∀ x ∈ s, r x u) : DirectedOn r s := by
  intro x hx y hy
  exact ⟨u, hu, h x hx, h y hy⟩

end DirectedOn

namespace LO

@[ext] structure StableFunction (α β : Type*) [CoherenceSpace α] [CoherenceSpace β] where
  toFun : Point α → Point β
  monotone' {a b : Point α} : a ≤ b → toFun a ≤ toFun b
  colimit' (s : Set (Point α)) (ds : DirectedOn (· ≤ ·) s) :
    toFun (Point.colimit s ds) = Point.colimit (toFun '' s) (ds.mono_comp @monotone')
  pullback' {a b : Point α} : IsClique (a ∪ b : Set α) → toFun (a ⊓ b) = toFun a ⊓ toFun b

infix:30 " →ₛ " => StableFunction

attribute [coe] StableFunction.toFun

namespace StableFunction

variable {α β γ δ : Type*} [CoherenceSpace α] [CoherenceSpace β] [CoherenceSpace γ] [CoherenceSpace δ]

instance : FunLike (α →ₛ β) (Point α) (Point β) where
  coe := toFun
  coe_injective' _ _ := StableFunction.ext

lemma monotone {f : α →ₛ β} {a b : Point α} : a ≤ b → f a ≤ f b := f.monotone'

lemma colimit {f : α →ₛ β} (s : Set (Point α)) (ds : DirectedOn (· ≤ ·) s) :
    f (Point.colimit s ds) = Point.colimit (f '' s) (ds.mono_comp @f.monotone) := f.colimit' s ds

lemma pullback {f : α →ₛ β} {a b : Point α} (h : IsClique (a ∪ b : Set α)) : f (a ⊓ b) = f a ⊓ f b := f.pullback' h

lemma union_clique {f : α →ₛ β} {a b : Point α} (h : IsClique (a ∪ b : Set α)) : IsClique (f a ∪ f b : Set β) := by
  let u : Point α := ⟨a ∪ b, h⟩
  have directed : DirectedOn (· ≤ ·) {a, b, u} :=
    DirectedOn.of_terminal_elem (u := u) (by simp) (by simp [u, Point.le_def])
  have := f.colimit {a, b, u} directed
  have : (f (Point.colimit {a, b, u} directed) : Set β) = ↑(f a) ∪ ↑(f b) ∪ ↑(f u) := by
    simpa [-Set.sUnion_image, Set.image_insert_eq, ←Set.union_assoc] using congr_arg Subtype.val this
  have : IsClique (↑(f a) ∪ ↑(f b) ∪ ↑(f u) : Set β) := by simp [←this]
  refine this.of_subset (by simp)

lemma ext_func {f g : α →ₛ β} : (f : Point α → Point β) = g → f = g := DFunLike.coe_fn_eq.mp

protected def id (α : Type*) [CoherenceSpace α] : α →ₛ α where
  toFun := id
  monotone' h := h
  colimit' s ds := by simp
  pullback' h := by simp

@[simp] lemma coe_id : (StableFunction.id α : Point α → Point α) = id := rfl

protected def comp (g : β →ₛ γ) (f : α →ₛ β) : α →ₛ γ where
  toFun := g ∘ f
  monotone' h := g.monotone (f.monotone h)
  colimit' s ds := by simp [colimit, Set.image_image]
  pullback' h := by simp [f.pullback h, g.pullback (union_clique h)]

@[simp] lemma coe_comp_def (g : β →ₛ γ) (f : α →ₛ β) : (g.comp f : Point α → Point γ) = g ∘ f := rfl

@[simp] lemma id_comp (f : α →ₛ β) : (StableFunction.id β).comp f = f := ext_func (by simp)

@[simp] lemma comp_id (f : α →ₛ β) : f.comp (StableFunction.id α) = f := ext_func (by simp)

lemma comp_assoc (h : γ →ₛ δ) (g : β →ₛ γ) (f : α →ₛ β) :
    h.comp (g.comp f) = (h.comp g).comp f := ext_func <| by simp; rfl

end StableFunction

end LO
