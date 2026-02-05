module

public import Mathlib.Tactic.TypeStar

/-!
# Supplemental notation classes
-/

@[expose] public section

namespace LO

class Tilde (α : Type*) where
  tilde : α → α

prefix:75 "∼" => Tilde.tilde

class Arrow (α : Type*) where
  arrow : α → α → α

infixr:60 " ➝ " => Arrow.arrow

class Wedge (α : Type*) where
  wedge : α → α → α

infixr:69 " ⋏ " => Wedge.wedge

class Vee (α : Type*) where
  vee : α → α → α

infixr:68 " ⋎ " => Vee.vee

class Box (α : Type*) where
  box : α → α

prefix:76 "□" => Box.box

class Dia (α : Type*) where
  dia : α → α

prefix:76 "◇" => Dia.dia

class HasTensor (α : Type*) where
  tensor : α → α → α

infix:69 " ⨂ " => HasTensor.tensor

class HasPar (α : Type*) where
  par : α → α → α

infix:68 " ⅋ " => HasPar.par

class HasWith (α : Type*) where
  with_ : α → α → α

infix:69 " & " => HasWith.with_

class HasPlus (α : Type*) where
  plus : α → α → α

infix:68 " ⨁ " => HasPlus.plus

class HasBang (α : Type*) where
  bang : α → α

/-- Note that this notation "！" (U+FF01) is distinct from "!" (U+0021) -/
prefix:75 "！" => HasBang.bang

class HasQuest (α : Type*) where
  quest : α → α

/-- Notice that this notation "？" (U+FF1F) is distinct from "?" (U+003F) -/
prefix:75 "？" => HasQuest.quest

class HasLolli (α : Type*) where
  lolli : α → α → α

infixr:60 " ⊸ " => HasLolli.lolli

attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee
  Box.box
  Dia.dia
  HasTensor.tensor
  HasPar.par
  HasWith.with_
  HasPlus.plus
  HasBang.bang
  HasQuest.quest
  HasLolli.lolli

class Exp (α : Type*) where
  exp : α → α

class Smash (α : Type*) where
  smash : α → α → α

infix:80 " ⨳ " => Smash.smash

class Length (α : Type*) where
  length : α → α

notation "‖" x "‖" => Length.length x

/-- Coding objects into syntactic objects (e.g. natural numbers, first-order terms) -/
class GödelQuote (α β : Sort*) where
  quote : α → β

notation:max "⌜" x "⌝" => GödelQuote.quote x

end LO

end
