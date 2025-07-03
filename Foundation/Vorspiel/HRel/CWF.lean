import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFounded
import Foundation.Vorspiel.HRel.Connected

section

abbrev ConverseWellFounded {α} (rel : HRel α) := WellFounded $ flip rel

class IsConverseWellFounded (α) (rel : HRel α) : Prop where cwf : ConverseWellFounded rel

end


section

variable {α} {R : HRel α}

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded R ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(R m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

lemma ConverseWellFounded.has_max (h : ConverseWellFounded R) : ∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(R m x) := by
  apply ConverseWellFounded.iff_has_max.mp h;

instance [Finite α] [IsTrans α R] [IsIrrefl α R] : IsConverseWellFounded _ R := ⟨by
  apply @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, IsIrrefl.irrefl]⟩
⟩

lemma Finite.converseWellFounded_of_trans_irrefl'
    (hFinite : Finite α) (hTrans : Transitive R) (hIrrefl : Irreflexive R) : ConverseWellFounded R :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by simp [flip]; intro a b c ba cb; exact hTrans cb ba;⟩
    ⟨by simp [flip]; exact hIrrefl⟩

end
