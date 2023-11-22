import Logic.Logic.System
import Logic.Vorspiel.Meta

namespace LO

open Primrec

namespace ManySorted

structure Language (S : Type w) where
  Func : S → (S → ℕ) → Type u
  Rel  : (S → ℕ) → Type u

namespace Language

protected def empty (S : Type w) : Language.{w, u} S where
  Func := fun _ _ => PEmpty
  Rel  := fun _ => PEmpty

instance : Inhabited (Language.{w, u} S) := ⟨Language.empty S⟩

end Language

end ManySorted

end LO
