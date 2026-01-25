module

public import Mathlib.Data.Nat.Bits
public import Mathlib.Tactic.Cases
public import Vorspiel.Matrix

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

lemma one_le_of_bodd {n : ℕ} (h : n.bodd = true) : 1 ≤ n :=
  by induction n <;> simp at h ⊢

lemma pair_le_pair_of_le {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : a₁.pair b₁ ≤ a₂.pair b₂ := by
  rcases lt_or_eq_of_le ha with (ha | rfl) <;> rcases lt_or_eq_of_le hb with (hb | rfl)
  · exact le_of_lt (lt_trans (Nat.pair_lt_pair_left b₁ ha) (Nat.pair_lt_pair_right a₂ hb))
  · exact le_of_lt (Nat.pair_lt_pair_left b₁ ha)
  · exact le_of_lt (Nat.pair_lt_pair_right a₁ hb)
  · rfl

end Nat

end
