module
import Mathlib.Data.ENat.Basic

namespace ENat

open Classical

noncomputable def find (P : ℕ → Prop) : ℕ∞ := if h : ∃ x : ℕ, P x then Nat.find h else ⊤

variable (P : ℕ → Prop)

theorem lt_find (n : ℕ) (h : ∀ m ≤ n, ¬P m) : (n : ℕ∞) < find P := by
  by_cases h : ∃ x : ℕ, P x
  · simpa [find, h]
  · simp [find, h]

theorem exists_of_find_le (n : ℕ) (h : find P ≤ (n : ENat)) : ∃ m ≤ n, P m := by
  by_contra A
  exact IsIrrefl.irrefl _ <| lt_of_le_of_lt h <| lt_find P n (by simpa using A)

lemma find_eq_top_iff : find P = ⊤ ↔ ∀ (n : ℕ), ¬P n := by simp [find]

lemma find_le (n : ℕ) (h : P n) : find P ≤ ↑n := by
  suffices ∃ m ≤ n, P m by simpa [show ∃ x, P x from ⟨n, h⟩, find]
  exact ⟨n, by rfl, h⟩

end ENat
