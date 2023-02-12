import Lean
import Mathlib.Order.BoundedOrder

universe u v

section logicNotation

@[notation_class] class HasNeg (α : Sort _) where
  neg : α → α

prefix:75 "¬'" => HasNeg.neg

@[notation_class] class HasArrow (α : Sort _) where
  arrow : α → α → α

infixr:60 " ⟶ " => HasArrow.arrow

@[notation_class] class HasAnd (α : Sort _) where
  and : α → α → α

infixl:69 " ⋏ " => HasAnd.and

@[match_pattern, notation_class] class HasOr (α : Sort _) where
  or : α → α → α

infixl:68 " ⋎ " => HasOr.or

class HasLogicSymbols (α : Sort _)
  extends Top α, Bot α, HasNeg α, HasArrow α, HasAnd α, HasOr α

@[notation_class] class HasUniv (α : ℕ → Sort _) where
  univ : ∀ {n}, α (n + 1) → α n

prefix:64 "∀' " => HasUniv.univ

@[notation_class] class HasEx (α : ℕ → Sort _) where
  ex : ∀ {n}, α (n + 1) → α n

prefix:64 "∃' " => HasEx.ex

attribute [match_pattern] HasAnd.and HasOr.or HasUniv.univ HasEx.ex

@[notation_class] class HasTurnstile (α : Sort _) (β : Sort _) where
  turnstile : Set α → α → β

infix:45 " ⊢ " => HasTurnstile.turnstile

@[notation_class] class HasVdash (α : Sort _) (β : outParam (Sort _)) where
  vdash : α → β

prefix:45 "⊩ " => HasVdash.vdash

@[notation_class] class HasDoubleTurnstile (α : Sort _) (β : Sort _) where
  doubleTurnstile : α → β → Prop

infix:55 " ⊧ " => HasDoubleTurnstile.doubleTurnstile

end logicNotation

namespace HasLogicSymbols

@[reducible]
instance Prop_HasLogicSymbols : HasLogicSymbols Prop where
  top := True
  bot := False
  neg := Not
  arrow := fun P Q => (P → Q)
  and := And
  or := Or

@[simp] lemma Prop_neg_eq (p : Prop) : ¬' p = ¬p := rfl   

@[simp] lemma Prop_arrow_eq (p q : Prop) : (p ⟶ q) = (p → q) := rfl

@[simp] lemma Prop_and_eq (p q : Prop) : (p ⋏ q) = (p ∧ q) := rfl

@[simp] lemma Prop_or_eq (p q : Prop) : (p ⋎ q) = (p ∨ q) := rfl

variable (α β γ : Type _) [HasLogicSymbols α] [HasLogicSymbols β] [HasLogicSymbols γ]

structure Hom where
  toFun : α → β
  map_top' : toFun ⊤ = ⊤
  map_bot' : toFun ⊥ = ⊥
  map_neg' : ∀ p, toFun (¬' p) = ¬'toFun p
  map_imp' : ∀ p q, toFun (p ⟶ q) = toFun p ⟶ toFun q
  map_and' : ∀ p q, toFun (p ⋏ q) = toFun p ⋏ toFun q
  map_or'  : ∀ p q, toFun (p ⋎ q) = toFun p ⋎ toFun q

infix:25 " →L " => Hom

namespace Hom
variable {α β γ}

instance coeToFun : CoeFun (α →L β) (fun _ => α → β) := ⟨fun f => f.toFun⟩

variable (f : α →L β) (a b : α)

@[simp] lemma map_top : f ⊤ = ⊤ := map_top' f

@[simp] lemma map_bot : f ⊥ = ⊥ := map_bot' f

@[simp] lemma map_neg : f (¬'a) = ¬'f a := Hom.map_neg' f a

@[simp] lemma map_imply : f (a ⟶ b) = f a ⟶ f b := map_imp' f a b

@[simp] lemma map_and : f (a ⋏ b) = f a ⋏ f b := map_and' f a b

@[simp] lemma map_or : f (a ⋎ b) = f a ⋎ f b := map_or' f a b

protected def id : α →L α where
  toFun := id
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imp' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_id (a : α) : HasLogicSymbols.Hom.id a = a := rfl

def comp (g : β →L γ) (f : α →L β) : α →L γ where
  toFun := g.toFun ∘ f.toFun
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imp' := by simp
  map_and' := by simp
  map_or' := by simp  

@[simp] lemma app_comp (g : β →L γ) (f : α →L β) (a : α) :
     g.comp f a = g (f a) := rfl

@[ext] lemma ext (f g : α →L β) (h : ∀ x, f x = g x) : f = g :=
  by rcases f; rcases g; simp; funext x; exact h x

end Hom

end HasLogicSymbols

