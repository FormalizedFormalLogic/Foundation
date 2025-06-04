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

/-- getElem version of `List.nodup_iff_getElem?_ne_getElem?` -/
lemma nodup_iff_get_ne_get : l.Nodup ↔ ∀ i j : Fin l.length, i < j → l[i] ≠ l[j] := by
  apply Iff.trans nodup_iff_getElem?_ne_getElem?;
  constructor;
  . rintro h ⟨i, _⟩ ⟨j, hj⟩ hij;
    have := h i j (by omega) hj;
    simp_all;
  . rintro h i j hij hj;
    rw [getElem?_eq_getElem, getElem?_eq_getElem];
    simpa [Option.some.injEq] using h ⟨i, by omega⟩ ⟨j, by omega⟩ hij;


lemma Nodup.infinite_of_infinite : Infinite {l : List α // l.Nodup} → Infinite α := by
  contrapose!;
  simp only [not_infinite_iff_finite];
  intro _;
  exact List.Nodup.finite;

end List
