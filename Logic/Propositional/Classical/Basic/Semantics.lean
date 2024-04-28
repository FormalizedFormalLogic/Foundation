import Logic.Propositional.Classical.Basic.Formula
import Logic.Logic.System

namespace LO

namespace Propositional.Classical

variable {α : Type*}

namespace Formula

section val

variable {F : Type*} [LogicalConnective F] [DeMorgan F] (v : α → F)

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

def val : Formula α →ˡᶜ F where
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

end Formula

structure Valuation (α : Type*) where
  val : α → Prop

instance : CoeFun (Valuation α) (fun _ ↦ α → Prop) := ⟨Valuation.val⟩

instance semantics : Semantics (Valuation α) (Formula α) := ⟨fun v ↦ Formula.val v⟩

lemma models_iff_val {v : Valuation α} {f : Formula α} : v ⊧ f ↔ Formula.val v f := iff_of_eq rfl

instance : Semantics.Tarski (Valuation α) where
  realize_top := by simp [models_iff_val]
  realize_bot := by simp [models_iff_val]
  realize_and := by simp [models_iff_val]
  realize_or := by simp [models_iff_val]
  realize_not := by simp [models_iff_val]
  realize_imp := by simp [models_iff_val]

namespace Formula
variable {v : Valuation α}

@[simp] protected lemma realize_atom : v ⊧ Formula.atom a ↔ v a := iff_of_eq rfl

@[simp] protected lemma realize_natom : v ⊧ Formula.natom a ↔ ¬v a := iff_of_eq rfl

end Formula

end Propositional.Classical

end LO
