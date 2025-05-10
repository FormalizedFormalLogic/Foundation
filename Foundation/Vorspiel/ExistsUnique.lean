import Foundation.Vorspiel.Vorspiel

namespace Classical
variable {α : Sort*} {φ : α → Prop} {r : α → α → Prop} (h : ∃! x, φ x)

noncomputable def choose! : α := choose h.exists

lemma choose!_spec : φ (choose! h) := choose_spec h.exists

lemma choose_uniq (hx : φ x) : x = choose! h := h.unique hx (choose!_spec h)

lemma choose!_eq_iff : x = choose! h ↔ φ x :=
  ⟨by rintro rfl; exact choose!_spec h, choose_uniq _⟩

lemma exitsUnique_extend (h : ∀ x, φ x → ∃! y, r x y) (default : α) (x : α) : ∃! y, (φ x → r x y) ∧ (¬φ x → y = default) := by
  by_cases hx : φ x <;> simp [hx]; exact h _ hx

noncomputable def extendedChoose! (h : ∀ x, φ x → ∃! y, r x y)
    (default : α) (x : α) : α := choose (exitsUnique_extend h default x).exists

lemma extendedchoose!_spec (h : ∀ x, φ x → ∃! y, r x y) (default : α) (hx : φ x) :
    r x (extendedChoose! h default x) :=
  choose_spec (exitsUnique_extend h default x).exists |>.1 hx

lemma extendedchoose!_spec_not (h : ∀ x, φ x → ∃! y, r x y) (default : α) (hx : ¬φ x) :
    extendedChoose! h default x = default :=
  choose_spec (exitsUnique_extend h default x).exists |>.2 hx

lemma extendedChoose!_uniq (h : ∀ x, φ x → ∃! y, r x y) (default : α) (hpx : φ x) (hrx : r x y) :
    y = extendedChoose! h default x :=
  (h x hpx).unique hrx (extendedchoose!_spec h default hpx)

lemma extendedChoose!_eq_iff (h : ∀ x, φ x → ∃! y, r x y) (default : α) (hpx : φ x) :
    y = extendedChoose! h default x ↔ r x y :=
  ⟨by rintro rfl; exact extendedchoose!_spec h default hpx, extendedChoose!_uniq h default hpx⟩

end Classical
