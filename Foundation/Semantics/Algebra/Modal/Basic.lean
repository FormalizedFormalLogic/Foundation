module

public import Foundation.Logic.LindenbaumAlgebra

@[expose] public section

namespace LO

/-- Algebra corresponding to `Modal.K` -/
class ModalAlgebra (α : Type*) extends BooleanAlgebra α, Box α, Dia α where
  box_top : □(⊤ : α) = ⊤
  box_meet (a b : α) : □(a ⊓ b) = □a ⊓ □b
  dual_dia {a : α} : (◇a) = (□aᶜ)ᶜ

namespace ModalAlgebra

variable {α : Type*} [ModalAlgebra α]
variable {a b : α}

attribute [grind =] dual_dia

@[grind =] lemma dual_box {a : α} : □a = (◇aᶜ)ᶜ := by simp [dual_dia]

@[grind =] lemma compl_box : (□a)ᶜ = ◇aᶜ := by simp [dual_box];
@[grind =] lemma compl_dia : (◇a)ᶜ = □aᶜ := by simp [dual_dia];

attribute [simp, grind .] box_top
@[simp, grind .] lemma dia_bot : ◇(⊥ : α) = ⊥ := by simp [dual_dia];

lemma box_imp_le_box_imp_box : □(a ⇨ b) ≤ (□a ⇨ □b) := by
  suffices □(a ⇨ b) ⊓ □a ≤ □b by simpa;
  calc
    □(a ⇨ b) ⊓ □a ≤ □(a ⇨ b) ⊓ □a ⊓ □b := by simp [←box_meet];
    _             ≤ □b                 := by simp;

lemma box_axiomK : □(a ⇨ b) ⇨ (□a ⇨ □b) = ⊤ := by
  rw [himp_eq_top_iff];
  exact box_imp_le_box_imp_box;

lemma dia_or : ◇(a ⊔ b) = ◇a ⊔ ◇b := by
  simp [dual_dia, compl_sup, box_meet];

@[grind <-]
lemma dia_monotone (h : a ≤ b) : ◇a ≤ ◇b := calc
  ◇a ≤ ◇(a ⊔ (b \ a)) := by simp [dia_or]
  _  = ◇b             := by simp [sup_sdiff_cancel_right h]

@[grind <-]
lemma box_monotone (h : a ≤ b) : □a ≤ □b := by
  simpa [dual_box] using dia_monotone (show bᶜ ≤ aᶜ by simpa);

end ModalAlgebra


namespace ModalAlgebra

protected class Transitive (α : Type*) extends ModalAlgebra α where
  box_trans {a : α} : □a ≤ □□a
export Transitive (box_trans)
attribute [simp, grind .] box_trans

protected class Reflexive (α : Type*) extends ModalAlgebra α where
  box_refl {a : α} : □a ≤ a
export Reflexive (box_refl)
attribute [simp, grind .] box_refl

end ModalAlgebra

end LO

end
