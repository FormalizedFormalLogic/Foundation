import Foundation.Propositional.Classical.Basic
import Foundation.Propositional.NNFormula

namespace LO.Propositional

variable {α : Type*}


namespace NNFormula

section val

variable {F : Type*} [LogicalConnective F] [DeMorgan F] (v : α → F)

def valAux : NNFormula α → F
  | .atom a  => v a
  | .natom a => ∼v a
  | ⊤       => ⊤
  | ⊥       => ⊥
  | φ ⋏ ψ   => φ.valAux ⋏ ψ.valAux
  | φ ⋎ ψ   => φ.valAux ⋎ ψ.valAux

lemma valAux_neg (φ : NNFormula α) :
    valAux v (∼φ) = ∼(valAux v φ) :=
  by induction φ using rec' <;> simp[*, valAux, ←neg_eq, or_iff_not_imp_left]

def val : NNFormula α →ˡᶜ F where
  toTr := valAux v
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ => rfl
  map_or' := fun _ _ => rfl
  map_imply' := fun _ _ => by simp[DeMorgan.imply, valAux, ←neg_eq, valAux_neg]
  map_neg' := fun _ => by simp[valAux, ←neg_eq, valAux_neg]

@[simp] lemma val_atom : val v (atom a) = v a := rfl

@[simp] lemma val_natom : val v (natom a) = ∼v a := rfl

end val


section semantics

variable {v : Classical.Valuation α}

instance semantics : Semantics (NNFormula α) (Classical.Valuation α) := ⟨fun v ↦ NNFormula.val v⟩

lemma models_iff_val {v : Classical.Valuation α} {f : NNFormula α} : v ⊧ f ↔ NNFormula.val v f := iff_of_eq rfl

instance : Semantics.Tarski (Classical.Valuation α) where
  realize_top := by simp [models_iff_val]
  realize_bot := by simp [models_iff_val]
  realize_and := by simp [models_iff_val]
  realize_or := by simp [models_iff_val]
  realize_not := by simp [models_iff_val]
  realize_imp := by simp [models_iff_val]

@[simp] protected lemma realize_atom : v ⊧ .atom a ↔ v a := iff_of_eq rfl

@[simp] protected lemma realize_natom : v ⊧ .natom a ↔ ¬v a := iff_of_eq rfl

end semantics

end NNFormula


end LO.Propositional
