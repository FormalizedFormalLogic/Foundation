module

public import Foundation.Vorspiel.Matrix

@[expose] public section

namespace Nat

open Matrix

def natToVec : ℕ → (n : ℕ) → Option (Fin n → ℕ)
  | 0,     0     => some Matrix.vecEmpty
  | e + 1, n + 1 => Nat.natToVec e.unpair.2 n |>.map (e.unpair.1 :> ·)
  | _,     _     => none

variable {n : ℕ}

@[simp] lemma natToVec_vecToNat (v : Fin n → ℕ) : (vecToNat v).natToVec n = some v := by
  induction n
  · simp [*, Nat.natToVec, vecToNat, Matrix.empty_eq]
  case succ _ ih =>
    suffices v 0 :> v ∘ Fin.succ = v by
      simp only [vecToNat, foldr_succ, natToVec, unpair_pair, Option.map_eq_some_iff]
      use vecTail v
      simpa using ih (vecTail v)
    exact funext (fun i ↦ i.cases (by simp) (by simp))

lemma lt_of_eq_natToVec {e : ℕ} {v : Fin n → ℕ} (h : e.natToVec n = some v) (i : Fin n) : v i < e := by
  induction' n with n ih generalizing e
  · exact i.elim0
  · cases' e with e
    · simp [natToVec] at h
    · simp only [natToVec, Option.map_eq_some_iff] at h
      rcases h with ⟨v, hnv, rfl⟩
      cases' i using Fin.cases with i
      · simp [lt_succ, unpair_left_le]
      · simp only [cons_val_succ]
        exact lt_trans (ih hnv i) (lt_succ.mpr <| unpair_right_le e)

end Nat

end
