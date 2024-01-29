 import Logic.Logic.LogicSymbol

namespace LO.Modal.Normal

@[notation_class] class Box (α : Sort _) where
  box : α → α

@[notation_class] class Dia (α : Sort _) where
  dia : α → α

class ModalLogicSymbol (α : Sort _) extends LogicSymbol α, Box α, Dia α

prefix:74 "□" => Box.box
prefix:74 "◇" => Dia.dia

attribute [match_pattern] Box.box Dia.dia

/-- Diamond(`◇`) defined by Box(`□`) -/
class ModalDuality (F : Type*) [ModalLogicSymbol F] where
  dia {p : F} : ◇p = ~(□(~p))

attribute [simp] ModalDuality.dia

/-- Box(`□`) defined by Diamond(`◇`) -/
class ModalDuality' (F : Type*) [ModalLogicSymbol F] where
  box {p : F} : □p = ~(◇(~p))

attribute [simp] ModalDuality'.box

end LO.Modal.Normal
