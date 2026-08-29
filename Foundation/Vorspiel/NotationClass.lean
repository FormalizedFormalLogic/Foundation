module

public import Mathlib.Tactic.TypeStar
public import Mathlib.Data.Nat.Basic

/-!
# Supplemental notation classes
-/

@[expose] public section

namespace LO

/-! ## Heterogeneous notation classes -/

class HTilde (α : Type*) (β : outParam Type*) where
  hTilde : α → β

prefix:75 "∼" => HTilde.hTilde
macro_rules | `(∼$x) => `(unop% HTilde.hTilde $x)

class HArrow (α β : Type*) (γ : outParam Type*) where
  hArrow : α → β → γ

infixr:60 " 🡒 " => HArrow.hArrow
macro_rules | `($x 🡒 $y) => `(binop% HArrow.hArrow $x $y)

class HWedge (α β : Type*) (γ : outParam Type*) where
  hWedge : α → β → γ

infixr:69 " ⋏ " => HWedge.hWedge
macro_rules | `($x ⋏ $y) => `(binop% HWedge.hWedge $x $y)

class HVee (α β : Type*) (γ : outParam Type*) where
  hVee : α → β → γ

infixr:68 " ⋎ " => HVee.hVee
macro_rules | `($x ⋎ $y) => `(binop% HVee.hVee $x $y)

attribute [match_pattern]
  HTilde.hTilde
  HArrow.hArrow
  HWedge.hWedge
  HVee.hVee

/-! ## Homogeneous notation classes -/

class Tilde (α : Type*) where
  tilde : α → α

class Arrow (α : Type*) where
  arrow : α → α → α

class Wedge (α : Type*) where
  wedge : α → α → α

class Vee (α : Type*) where
  vee : α → α → α

attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee

@[default_instance]
instance Tilde.instHTilde [Tilde α] : HTilde α α := ⟨Tilde.tilde⟩

@[default_instance]
instance Arrow.instHArrow [Arrow α] : HArrow α α α := ⟨Arrow.arrow⟩

@[default_instance]
instance Wedge.instHWedge [Wedge α] : HWedge α α α := ⟨Wedge.wedge⟩

@[default_instance]
instance Vee.instHVee [Vee α] : HVee α α α := ⟨Vee.vee⟩

class Box (α : Type*) where
  box : α → α

prefix:76 "□" => Box.box

class Dia (α : Type*) where
  dia : α → α

prefix:76 "◇" => Dia.dia

class Rhd (α : Type*) where
  rhd : α → α → α

infixl:70 " ▷ " => Rhd.rhd

attribute [match_pattern]
  Box.box
  Dia.dia
  Rhd.rhd

class Exp (α : Type*) where
  exp : α → α

class Superexp (α : Type*) where
  superexp : α → α

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

class SigmaSymbol (α : Type*) where
  sigma : α

class PiSymbol (α : Type*) where
  pi : α

class DeltaSymbol (α : Type*) where
  delta : α

notation "𝚺" => SigmaSymbol.sigma

notation "𝚷" => PiSymbol.pi

notation "𝚫" => DeltaSymbol.delta

attribute [match_pattern] SigmaSymbol.sigma PiSymbol.pi DeltaSymbol.delta

end LO

end
