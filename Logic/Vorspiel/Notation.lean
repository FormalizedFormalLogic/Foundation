import Lean
import Mathlib.Order.BoundedOrder

universe u v

namespace LO

section logicNotation

@[notation_class] class HasNeg (α : Sort _) where
  neg : α → α

prefix:75 "~" => HasNeg.neg

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

section HasUniv

variable {α : ℕ → Sort u} [HasUniv α]

def univClosure : {n : ℕ} → α n → α 0
  | 0,     a => a
  | _ + 1, a => univClosure (∀' a)

@[simp] lemma univ_closure_zero (a : α 0) : univClosure a = a := rfl

@[simp] lemma univ_closure_succ {n} (a : α (n + 1)) : univClosure a = univClosure (∀' a) := rfl

end HasUniv

@[notation_class] class HasEx (α : ℕ → Sort _) where
  ex : ∀ {n}, α (n + 1) → α n

prefix:64 "∃' " => HasEx.ex

attribute [match_pattern] HasNeg.neg HasArrow.arrow HasAnd.and HasOr.or HasUniv.univ HasEx.ex

@[notation_class] class HasTurnstile (α : Sort _) (β : Sort _) where
  turnstile : Set α → α → β

infix:45 " ⊢ " => HasTurnstile.turnstile

@[notation_class] class HasVdash (α : Sort _) (β : outParam (Sort _)) where
  vdash : α → β

prefix:45 "⊩ " => HasVdash.vdash

end logicNotation

namespace HasLogicSymbols

section
variable {α : Sort _} [HasLogicSymbols α]

@[match_pattern] def iff (a b : α) := (a ⟶ b) ⋏ (b ⟶ a)

infix:61 " ⟷ " => HasLogicSymbols.iff

end

@[reducible]
instance Prop_HasLogicSymbols : HasLogicSymbols Prop where
  top := True
  bot := False
  neg := Not
  arrow := fun P Q => (P → Q)
  and := And
  or := Or

@[simp] lemma Prop_top_eq : ⊤ = True := rfl

@[simp] lemma Prop_bot_eq : ⊥ = False := rfl

@[simp] lemma Prop_neg_eq (p : Prop) : ~ p = ¬p := rfl

@[simp] lemma Prop_arrow_eq (p q : Prop) : (p ⟶ q) = (p → q) := rfl

@[simp] lemma Prop_and_eq (p q : Prop) : (p ⋏ q) = (p ∧ q) := rfl

@[simp] lemma Prop_or_eq (p q : Prop) : (p ⋎ q) = (p ∨ q) := rfl

@[simp] lemma Prop_iff_eq (p q : Prop) : (p ⟷ q) = (p ↔ q) := by simp[HasLogicSymbols.iff, iff_iff_implies_and_implies]

class HomClass (F : Type _) (α β : outParam (Type _)) [HasLogicSymbols α] [HasLogicSymbols β] extends FunLike F α (fun _ => β) where
  map_top : ∀ (f : F), f ⊤ = ⊤
  map_bot : ∀ (f : F), f ⊥ = ⊥
  map_neg : ∀ (f : F) (p : α), f (~ p) = ~f p
  map_imply : ∀ (f : F) (p q : α), f (p ⟶ q) = f p ⟶ f q
  map_and : ∀ (f : F) (p q : α), f (p ⋏ q) = f p ⋏ f q
  map_or  : ∀ (f : F) (p q : α), f (p ⋎ q) = f p ⋎ f q

attribute [simp] HomClass.map_top HomClass.map_bot HomClass.map_neg HomClass.map_imply HomClass.map_and HomClass.map_or

namespace HomClass

variable (F : Type _) (α β : outParam (Type _)) [HasLogicSymbols α] [HasLogicSymbols β]
variable [HomClass F α β]
variable (f : F) (a b : α)

instance : CoeFun F (fun _ => α → β) := ⟨FunLike.coe⟩

@[simp] lemma map_iff : f (a ⟷ b) = f a ⟷ f b := by simp[HasLogicSymbols.iff]

end HomClass

variable (α β γ : Type _) [HasLogicSymbols α] [HasLogicSymbols β] [HasLogicSymbols γ]

structure Hom where
  toTr : α → β
  map_top' : toTr ⊤ = ⊤
  map_bot' : toTr ⊥ = ⊥
  map_neg' : ∀ p, toTr (~ p) = ~toTr p
  map_imply' : ∀ p q, toTr (p ⟶ q) = toTr p ⟶ toTr q
  map_and' : ∀ p q, toTr (p ⋏ q) = toTr p ⋏ toTr q
  map_or'  : ∀ p q, toTr (p ⋎ q) = toTr p ⋎ toTr q

infix:25 " →L " => Hom

-- hide Hom.toTr
open Lean PrettyPrinter Delaborator SubExpr in
@[app_unexpander Hom.toTr]
def unexpsnderToFun : Unexpander
  | `($_ $h $x) => `($h $x)
  | _           => throw ()

namespace Hom
variable {α β γ}

instance : FunLike (α →L β) α (fun _ => β) where
  coe := toTr
  coe_injective' := by intro f g h; rcases f; rcases g; simp; exact h

instance : CoeFun (α →L β) (fun _ => α → β) := FunLike.hasCoeToFun

@[ext] lemma ext (f g : α →L β) (h : ∀ x, f x = g x) : f = g := FunLike.ext f g h

instance : HomClass (α →L β) α β where
  map_top := map_top'
  map_bot := map_bot'
  map_neg := map_neg'
  map_imply := map_imply'
  map_and := map_and'
  map_or := map_or'

variable (f : α →L β) (a b : α)

protected def id : α →L α where
  toTr := id
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp

@[simp] lemma app_id (a : α) : HasLogicSymbols.Hom.id a = a := rfl

def comp (g : β →L γ) (f : α →L β) : α →L γ where
  toTr := g ∘ f
  map_top' := by simp
  map_bot' := by simp
  map_neg' := by simp
  map_imply' := by simp
  map_and' := by simp
  map_or' := by simp  

@[simp] lemma app_comp (g : β →L γ) (f : α →L β) (a : α) :
     g.comp f a = g (f a) := rfl

end Hom

section quantifier
variable {α : ℕ → Type u} [∀ i, HasLogicSymbols (α i)] [HasUniv α] [HasEx α]

def ball (p : α (n + 1)) (q : α (n + 1)) : α n := ∀' (p ⟶ q)

def bex (p : α (n + 1)) (q : α (n + 1)) : α n := ∃' (p ⋏ q)

notation:64 "∀[" p "] " q => ball p q

notation:64 "∃[" p "] " q => bex p q

end quantifier

end HasLogicSymbols

end LO
