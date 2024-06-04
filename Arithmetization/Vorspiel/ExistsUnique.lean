import Arithmetization.Vorspiel.Vorspiel

namespace Classical
variable {α : Sort*} {p : α → Prop} {r : α → α → Prop} (h : ∀ x, p x → ∃! y, r x y)

lemma exitsUnique_extend (default : α) (x : α) : ∃! y, (p x → r x y) ∧ (¬p x → y = default) := by
  by_cases hx : p x <;> simp [hx]; exact h _ hx

noncomputable def extendedChoose! (default : α) (x : α) : α := choose (exitsUnique_extend h default x).exists

variable (default : α)

lemma extendedchoose!_spec (hx : p x) : r x (extendedChoose! h default x) :=
  choose_spec (exitsUnique_extend h default x).exists |>.1 hx

lemma extendedchoose!_spec_not (hx : ¬p x) : extendedChoose! h default x = default :=
  choose_spec (exitsUnique_extend h default x).exists |>.2 hx

lemma extendedChoose!_uniq (hpx : p x) (hrx : r x y) : y = extendedChoose! h default x :=
  (h x hpx).unique hrx (extendedchoose!_spec h default hpx)

lemma extendedChoose!_eq_iff (hpx : p x) : y = extendedChoose! h default x ↔ r x y :=
  ⟨by rintro rfl; exact extendedchoose!_spec h default hpx, extendedChoose!_uniq h default hpx⟩

end Classical
