import Foundation.Modal.Algebra.Basic

namespace LO

class MagariAlgebra (α : Type*) extends ModalAlgebra α where
  box_diag {a : α} : □(□a ⇨ a) = □a

namespace MagariAlgebra

open ModalAlgebra

variable {α : Type u} [MagariAlgebra α]
variable {a b : α}

lemma dia_diag : ◇(a ⊓ (◇a)ᶜ) = ◇a := by
  suffices □(aᶜ ⊔ (□aᶜ)ᶜ) = □aᶜ by simpa [ModalAlgebra.dual_dia];
  calc
  _ = □(□aᶜ ⇨ aᶜ) := by rw [BooleanAlgebra.himp_eq]
  _ = _           := by rw [box_diag];

@[simp]
lemma dia_trans : ◇◇a ≤ ◇a := calc
  ◇◇a ≤ ◇a ⊔ ◇◇a                     := by simp
  _   = ◇(a ⊔ ◇a)                    := by simp [dia_or]
  _   = ◇((a ⊔ ◇a) ⊓ (◇(a ⊔ ◇a))ᶜ)   := by rw [dia_diag]
  _   = ◇((a ⊔ ◇a) ⊓ (◇a)ᶜ ⊓ (◇◇a)ᶜ) := by simp only [dia_or, compl_sup, inf_assoc]
  _   = ◇(a ⊓ (◇a)ᶜ ⊓ (◇◇a)ᶜ)        := by simp only [inf_sup_right, inf_compl_self, le_inf_iff, bot_le, and_self, sup_of_le_left]
  _   ≤ ◇a                           := dia_monotone (by simp [inf_assoc])

@[simp]
lemma box_trans : □a ≤ □□a := compl_le_compl_iff_le.mp <| by simp [compl_box]

instance : ModalAlgebra.Transitive α := ⟨box_trans⟩

end MagariAlgebra

end LO
