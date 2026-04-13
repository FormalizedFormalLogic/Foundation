module

public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.CompleteBooleanAlgebra

public section

section frame

variable {α : Type*} [Order.Frame α]

theorem compl_iSup' {a : ι → α} : (⨆ i, a i)ᶜ = ⨅ i, (a i)ᶜ := by
  simpa using iSup_himp_eq (f := a) (a := ⊥)

end frame

section HeytingAlgebra

variable {α : Type*} [HeytingAlgebra α]

@[simp, grind .]
lemma himp_himp_inf_himp_inf_le (a b c : α) : (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c := calc
  (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a = (a ⇨ b ⇨ c) ⊓ b ⊓ a := by simp only [inf_assoc, himp_inf_self]
  _                         = (a ⇨ b ⇨ c) ⊓ a ⊓ b := by simp only [inf_assoc, inf_comm a b]
  _                         ≤ (b ⇨ c) ⊓ b         := by simp only [himp_inf_self a (b ⇨ c), le_inf_iff]
                                                        constructor
                                                        · simp only [inf_assoc, inf_le_left]
                                                        · exact inf_le_right
  _                         ≤ c                   := by simp

@[simp, grind .]
lemma himp_inf_himp_inf_sup_le (a b c : α) : (a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) ≤ c := by
  have ha : a ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have hb : b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, inf_comm (a ⇨ c) (b ⇨ c), ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have : a ⊔ b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := sup_le_iff.mpr ⟨ha, hb⟩
  simpa only [GeneralizedHeytingAlgebra.le_himp_iff, inf_comm (a ⊔ b)] using this

end HeytingAlgebra

namespace CompleteBooleanAlgebra

variable {α : Type*} [CompleteBooleanAlgebra α]



end CompleteBooleanAlgebra
