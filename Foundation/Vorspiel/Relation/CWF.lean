import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFounded

section

abbrev ConverseWellFounded {α : Sort*} (rel : α → α → Prop) := WellFounded $ flip rel

class IsConverseWellFounded (α : Sort*) (rel : α → α → Prop) : Prop where cwf : ConverseWellFounded rel

end


section

variable {α : Type*} {rel : α → α → Prop}

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded r ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(r m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

instance [Finite α] [IsTrans α rel] [IsIrrefl α rel] : IsConverseWellFounded _ rel := ⟨by
  apply @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, IsIrrefl.irrefl]⟩
⟩

lemma Finite.converseWellFounded_of_trans_irrefl'
    (hFinite : Finite α) (hTrans : Transitive rel) (hIrrefl : Irreflexive rel) : ConverseWellFounded rel :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by simp [flip]; intro a b c ba cb; exact hTrans cb ba;⟩
    ⟨by simp [flip]; exact hIrrefl⟩

end
