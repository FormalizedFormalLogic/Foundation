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

class Rhd (α : Type*) where
  rhd : α → α → α

infixl:70 " ▷ " => Rhd.rhd

class Tensor (α : Type*) where
  tensor : α → α → α

infix:69 " ⨂ " => Tensor.tensor

class Par (α : Type*) where
  par : α → α → α

infix:68 " ⅋ " => Par.par

class With (α : Type*) where
  with_ : α → α → α

infix:69 " & " => With.with_

class Plus (α : Type*) where
  plus : α → α → α

infix:68 " ⨁ " => Plus.plus

class Lolli (α : Type*) where
  lolli : α → α → α

infixr:60 " ⊸ " => Lolli.lolli

class Bang (α : Type*) where
  bang : α → α

/-- Note that this notation "！" (U+FF01) is distinct from "!" (U+0021) -/
prefix:75 "！" => Bang.bang

class Quest (α : Type*) where
  quest : α → α

/-- Notice that this notation "？" (U+FF1F) is distinct from "?" (U+003F) -/
prefix:75 "？" => Quest.quest

attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee
  Box.box
  Dia.dia
  Rhd.rhd
  Tensor.tensor
  Par.par
  With.with_
  Plus.plus
  Lolli.lolli
  Bang.bang
  Quest.quest

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
