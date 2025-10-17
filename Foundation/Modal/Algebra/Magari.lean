import Foundation.Modal.LogicSymbol

namespace LO

class MagariAlgebra (α : Type*) extends Dia α, Box α, BooleanAlgebra α where
  box_def (a : α) : □a = (◇aᶜ)ᶜ
  dia_bot : ◇(⊥ : α) = ⊥
  dia_or (a b : α) : ◇(a ⊔ b) = ◇a ⊔ ◇b
  dia_loeb (a : α) : ◇a = ◇(a ⊓ (◇a)ᶜ)

namespace MagariAlgebra

variable {α : Type*} [MagariAlgebra α]

attribute [simp] dia_bot

lemma compl_box (a : α) : (□a)ᶜ = ◇aᶜ := by simp [box_def]

lemma compl_dia (a : α) : (◇a)ᶜ = □aᶜ := by simp [box_def]

@[simp] lemma box_top : □(⊤ : α) = ⊤ := by simp [box_def]

lemma dia_monotone {a b : α} (h : a ≤ b) : ◇a ≤ ◇b := calc
  ◇a ≤ ◇(a ⊔ (b \ a)) := by simp [dia_or]
  _  = ◇b             := by simp [sup_sdiff_cancel_right h]

@[simp] lemma dia_trans (a : α) : ◇◇a ≤ ◇a := calc
  ◇◇a ≤ ◇a ⊔ ◇◇a                     := by simp
  _   = ◇(a ⊔ ◇a)                    := by simp [dia_or]
  _   = ◇((a ⊔ ◇a) ⊓ (◇(a ⊔ ◇a))ᶜ)   := by rw [←dia_loeb]
  _   = ◇((a ⊔ ◇a) ⊓ (◇a)ᶜ ⊓ (◇◇a)ᶜ) := by simp only [dia_or, compl_sup, inf_assoc]
  _   = ◇(a ⊓ (◇a)ᶜ ⊓ (◇◇a)ᶜ)        := by simp only [inf_sup_right, inf_compl_self, le_inf_iff, bot_le, and_self, sup_of_le_left]
  _   ≤ ◇a                           := dia_monotone (by simp [inf_assoc])

@[simp] lemma box_trans (a : α) : □a ≤ □□a := compl_le_compl_iff_le.mp <| by simp [compl_box]

end MagariAlgebra

end LO
