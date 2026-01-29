module

public import Foundation.Modal.Algebra.Basic

@[expose] public section

namespace LO

class MagariAlgebra (α : Type*) extends ModalAlgebra α where
  box_diag {a : α} : □(□a ⇨ a) = □a

namespace MagariAlgebra

open ModalAlgebra

variable {α : Type u} [MagariAlgebra α]
variable {a b : α}

lemma dia_diag : ◇(a ⊓ ￢(◇a)) = ◇a := by
  suffices □(￢a ⊔ (￢□(￢a))) = □(￢a) by simpa [ModalAlgebra.dual_dia];
  calc
  _ = □(□(￢a) ⇨ ￢a) := by simp [BooleanAlgebra.himp_eq]
  _ = _           := by rw [box_diag];

@[simp]
lemma dia_trans : ◇◇a ≤ ◇a := calc
  ◇◇a ≤ ◇a ⊔ ◇◇a                       := by simp
  _   = ◇(a ⊔ ◇a)                      := by simp [dia_or]
  _   = ◇((a ⊔ ◇a) ⊓ (￢◇(a ⊔ ◇a)))    := by rw [dia_diag]
  _   = ◇((a ⊔ ◇a) ⊓ ￢(◇a) ⊓ ￢(◇◇a)) := by simp only [dia_or, hnot_eq_compl, compl_sup, inf_assoc]
  _   = ◇(a ⊓ ￢(◇a) ⊓ ￢(◇◇a))        := by simp only [hnot_eq_compl, inf_sup_right, inf_compl_self, le_inf_iff, bot_le, and_self, sup_of_le_left]
  _   ≤ ◇a                             := dia_monotone (by simp [inf_assoc])

@[simp]
lemma box_trans : □a ≤ □□a := by
  rw [←compl_le_compl_iff_le, ←hnot_eq_compl, ←hnot_eq_compl, compl_box, compl_box];
  exact dia_trans;

instance : ModalAlgebra.Transitive α := ⟨box_trans⟩

end MagariAlgebra

end LO
end
