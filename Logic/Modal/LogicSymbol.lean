 import Logic.Logic.LogicSymbol

namespace LO

@[notation_class] class Box (α : Sort _) where
  box : α → α

@[notation_class] class Dia (α : Sort _) where
  dia : α → α

class ModalLogicSymbol (α : Sort _) extends LogicSymbol α, Box α, Dia α

prefix:74 "□" => Box.box
prefix:74 "◇" => Dia.dia

attribute [match_pattern] Box.box Dia.dia

class ModalDeMorgan (F : Type*) [ModalLogicSymbol F] extends DeMorgan F where
  box (p : F) : □p = ~(◇(~p))
  dia (p : F) : ◇p = ~(□(~p))

attribute [simp] ModalDeMorgan.box ModalDeMorgan.dia

end LO
