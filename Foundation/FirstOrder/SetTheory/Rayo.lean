module

public import Foundation.FirstOrder.SetTheory.Z
public import Foundation.FirstOrder.SetTheory.Universe

@[expose] public section
/-!
# Rayo's number
-/

namespace FFL.FirstOrder.SetTheory

noncomputable def definableNumbers (N : ℕ) : Set ℕ :=
  {m | ∃ φ : Semisentence ℒₛₑₜ 1, Encodable.encode φ < N ∧ DefinedFunction₀ (m : Universe.{0}) φ}

/-- Rayo's number (at `N`) is the successor of the largest natural number that cannot be defined by a formula of set-theory smaller than `N`. -/
noncomputable def rayo (N : ℕ) : ℕ := ⨆ n ∈ definableNumbers N, n + 1

noncomputable def rayoNumber : ℕ := rayo (10^100)

variable {N : ℕ}

lemma rayo_gt {φ : Semisentence ℒₛₑₜ 1} {m : ℕ}
    (h : Encodable.encode φ < N) (hm : DefinedFunction₀ (m : Universe.{0}) φ) : m < rayo N := by
  sorry

lemma rayo_monotone {N M : ℕ} (h : N ≤ M) : rayo N ≤ rayo M := by
  sorry

lemma rayo_unbounded (m : ℕ) : ∃ N, m < rayo N := by sorry

end FFL.FirstOrder.SetTheory
