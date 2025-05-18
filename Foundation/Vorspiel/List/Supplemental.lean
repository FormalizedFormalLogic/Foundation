import Foundation.Vorspiel.Vorspiel

namespace List

variable {l : List α}

lemma exists_of_not_nil (hl : l ≠ []) : ∃ a, a ∈ l := by
  match l with
  | [] => tauto;
  | a :: l => use a; simp only [mem_cons, true_or];

lemma iff_nil_forall : (l = []) ↔ (∀ a ∈ l, a ∈ []) := by
  constructor;
  . intro h;
    subst h;
    tauto;
  . contrapose!;
    rintro h;
    obtain ⟨a, ha⟩ := exists_of_not_nil h;
    use a;
    tauto;

end List
