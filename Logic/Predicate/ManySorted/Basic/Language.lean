import Logic.Logic.Logic
import Logic.Predicate.FirstOrder.Basic
import Logic.Vorspiel.Meta

namespace LO

open Primrec

namespace ManySorted

structure Language (S : Type w) where
  Func : S → {k : ℕ} → (Fin k → S) → Type u
  Rel  : {k : ℕ} → (Fin k → S) → Type u

namespace Language

protected def empty (S : Type w) : Language.{w, u} S where
  Func := fun _ _ _ => PEmpty
  Rel  := fun _ => PEmpty

instance : Inhabited (Language.{w, u} S) := ⟨Language.empty S⟩

namespace SO

inductive Func (L : FirstOrder.Language) : Fin 2 → {k : ℕ} → (Fin k → Fin 2) → Type
  | fo {k : ℕ} : L.func k → Func L 0 (fun _ : Fin k => 0)

inductive Rel (L : FirstOrder.Language) : {k : ℕ} → (Fin k → Fin 2) → Type
  | fo {k : ℕ} : L.func k → Rel L (fun _ : Fin k => 0)
  | mem : Rel L ![0, 1]

end SO

def sO (L : FirstOrder.Language) : Language (Fin 2) where
  Func := SO.Func L
  Rel := SO.Rel L

end Language

end ManySorted

end LO
