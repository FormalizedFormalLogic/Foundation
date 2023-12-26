import Logic.Propositional.Basic.Formula
import Logic.Logic.System

namespace LO

namespace Propositional

variable {α : Type*}

namespace Formula

section val

variable {F : Type*} [LogicSymbol F] [DeMorgan F] (v : α → F)

def valAux : Formula α → F
  | atom a  => v a
  | natom a => ~v a
  | ⊤       => ⊤
  | ⊥       => ⊥
  | p ⋏ q   => p.valAux ⋏ q.valAux
  | p ⋎ q   => p.valAux ⋎ q.valAux

lemma valAux_neg (p : Formula α) :
    valAux v (~p) = ~(valAux v p) :=
  by induction p using rec' <;> simp[*, valAux, ←neg_eq, or_iff_not_imp_left]

def val : Formula α →L F where
  toTr := valAux v
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ => rfl
  map_or' := fun _ _ => rfl
  map_imply' := fun _ _ => by simp[DeMorgan.imply, valAux, ←neg_eq, valAux_neg]
  map_neg' := fun _ => by simp[valAux, ←neg_eq, valAux_neg]

@[simp] lemma val_atom : val v (atom a) = v a := rfl

@[simp] lemma val_natom : val v (natom a) = ~v a := rfl

end val

instance : Semantics (Formula α) (Set α) := ⟨val⟩

namespace Val
variable {v : Set α}

@[simp] protected lemma atom : v ⊧ (atom a) ↔ a ∈ v := iff_of_eq rfl

@[simp] protected lemma natom : v ⊧ (natom a) ↔ a ∉ v := iff_of_eq rfl

end Val

end Formula

end Propositional

end LO
