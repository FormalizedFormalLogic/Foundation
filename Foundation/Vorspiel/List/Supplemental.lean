import Foundation.Vorspiel.Vorspiel

namespace List

variable {α} {l : List α}

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

lemma ne_get_con_get_con_of_ne
  (h : ∀ i j : Fin l.length, i ≠ j → (l.get i) ≠ (l.get j))
  (hx : x ∉ l)
  : ∀ i j, i ≠ j → (x :: l).get i ≠ (x :: l).get j := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij;
  match i, j with
  | 0, 0 => contradiction;
  | 0, j + 1 =>
    revert hx;
    contrapose!;
    intro h;
    apply List.mem_of_getElem;
    exact h.symm;
  | i + 1, 0 =>
    revert hx;
    contrapose!;
    intro h;
    apply List.mem_of_getElem;
    exact h;
  | i + 1,j + 1 =>
    apply h;
    simpa using hij;

lemma iff_eq_getElem_eq_getElem? {i j : Fin l.length} : l[i] = l[j] ↔ l[i]? = l[j]? := by
  simp_all only [Fin.getElem_fin, Fin.getElem?_fin, Fin.is_lt, getElem?_eq_getElem, Option.some.injEq];

lemma nodup_iff_get_ne_get : l.Nodup ↔ ∀ i j : Fin l.length, i ≠ j → l[i] ≠ l[j] := by
  apply Iff.trans List.nodup_iff_getElem?_ne_getElem?
  constructor
  · rintro h ⟨i, hi⟩ ⟨j, hj⟩ eij;
    wlog hij : i < j;
    . apply this h j hj i hi eij.symm ?_ |>.symm;
      apply lt_of_le_of_ne';
      . exact le_of_not_lt hij;
      . by_contra eij;
        subst eij;
        simp at eij;
    have := h i j hij hj;
    revert this;
    contrapose!;
    apply List.iff_eq_getElem_eq_getElem?.mp;
  · intro h i j hij hjl;
    apply l.iff_eq_getElem_eq_getElem? (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) |>.not.mp;
    apply h;
    simp only [ne_eq, Fin.mk.injEq];
    by_contra eij;
    subst eij;
    simp at hij;

protected lemma Nodup.tail {l : List α} (h : l.Nodup) : l.tail.Nodup := Nodup.sublist (tail_sublist l) h

lemma not_noDup_of_not_tail_noDup {l : List α} : ¬l.tail.Nodup → ¬l.Nodup := by
  contrapose!;
  apply Nodup.tail

end List
