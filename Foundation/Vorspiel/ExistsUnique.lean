import Foundation.Vorspiel.Vorspiel

namespace Classical
variable {α : Sort*} {p : α → Prop} (h : ∃! x, p x)

noncomputable def choose! : α := choose h.exists

lemma choose!_spec : p (choose! h) := choose_spec h.exists

lemma choose_uniq (hx : p x) : x = choose! h := h.unique hx (choose!_spec h)

lemma choose!_eq_iff : x = choose! h ↔ p x :=
  ⟨by rintro rfl; exact choose!_spec h, choose_uniq _⟩

end Classical
