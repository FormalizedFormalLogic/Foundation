import Logic.Propositional.Basic.Formula
import Logic.Logic.System

namespace LO

namespace Propositional

variable (α : Type*)

structure Structure (α : Type*) where
  val : α → Prop

namespace Formula

def val (s : Structure α) : Formula α → Prop
  | atom a  => s.val a
  | natom a => ¬s.val a
  | ⊤       => True
  | ⊥       => False
  | p ⋏ q   => p.val s ∧ q.val s
  | p ⋎ q   => p.val s ∨ q.val s

end Formula

end Propositional

end LO
