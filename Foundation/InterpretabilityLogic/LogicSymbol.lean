import Foundation.Modal.LogicSymbol

namespace LO

class Rhd (F : Type*) where
  rhd : F → F → F

infixl:70 " ▷ " => Rhd.rhd

attribute [match_pattern] Rhd.rhd

class InterpretabilityLogicalConnective (F : Type*) extends BasicModalLogicalConnective F, Rhd F

end LO
