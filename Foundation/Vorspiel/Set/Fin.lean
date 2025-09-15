import Foundation.Vorspiel.Vorspiel

namespace Set


namespace Fin1

protected lemma eq_univ : Set.univ (α := Fin 1) = {0} := by ext x; match x with | 0 => simp

protected lemma eq_powerset : Set.powerset (Set.univ : Set (Fin 1)) = {{0}, ∅} := by
  ext x;
  simp only [Set.powerset_univ, Set.mem_univ, Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff];
  by_cases h : 0 ∈ x;
  . left; ext i; match i with | 0 => simp_all;
  . right; ext i; match i with | 0 => simp_all;

protected lemma all_cases (s : Set (Fin 1)) : s = {0} ∨ s = ∅ := by
  simpa using Set.Fin1.eq_powerset.subset (by simp);

end Fin1


namespace Fin2

protected lemma eq_univ : Set.univ (α := Fin 2) = {0, 1} := by ext x; match x with | 0 | 1 => simp

protected lemma eq_powerset : Set.powerset (Set.univ : Set (Fin 2)) = {{0, 1}, {0}, {1}, ∅} := by
  ext x;
  simp only [Set.powerset_univ, Set.mem_univ, Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff];
  by_cases h0 : 0 ∈ x <;>
  by_cases h1 : 1 ∈ x;
  . left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; right; left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; right; right;
    ext i;
    match i with | 0 | 1 => simp_all;

protected lemma all_cases (s : Set (Fin 2)) : s = {0, 1} ∨ s = {0} ∨ s = {1} ∨ s = ∅ := by
  simpa using Set.Fin2.eq_powerset.subset (by simp);

end Fin2

namespace Fin3

protected lemma eq_univ : Set.univ (α := Fin 3) = {0, 1, 2} := by ext x; match x with | 0 | 1 | 2 => simp

end Fin3

end Set
