module

public import Mathlib.Data.List.OfFn
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
      simpa using! ih (vecTail v)
    exact funext (fun i ↦ i.cases (by simp) (by simp))

lemma lt_of_eq_natToVec {e : ℕ} {v : Fin n → ℕ} (h : e.natToVec n = some v) (i : Fin n) : v i < e := by
  induction' n with n ih generalizing e
  · exact i.elim0
  · cases' e with e
    · simp [natToVec] at h
    · simp only [natToVec, Option.map_eq_some_iff] at h
      rcases h with ⟨v, hnv, rfl⟩
      cases' i using Fin.cases with i
      · simp [Nat.lt_succ_iff, unpair_left_le]
      · simp only [cons_val_succ]
        exact lt_trans (ih hnv i) (Nat.lt_succ_iff.mpr <| unpair_right_le e)

/-- List form of `Nat.natToVec`: the same decoding, with the length out of the type. -/
def natToList : ℕ → List ℕ
  | 0 => []
  | e + 1 => e.unpair.1 :: natToList e.unpair.2
  decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_right_le e)

lemma natToVec_eq_some_iff {e k : ℕ} {v : Fin k → ℕ} :
    e.natToVec k = some v ↔ natToList e = List.ofFn v := by
  induction k generalizing e with
  | zero =>
    cases e with
    | zero => simp [natToVec, natToList, Matrix.empty_eq]
    | succ e => simp [natToVec, natToList]
  | succ k ih =>
    cases e with
    | zero => simp [natToVec, natToList]
    | succ e =>
      rw [natToVec, natToList, List.ofFn_succ]
      constructor
      · rintro h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨w, hw, rfl⟩ := h
        rw [ih.mp hw]
        simp
      · rintro h
        rw [List.cons.injEq] at h
        obtain ⟨h0, hl⟩ := h
        refine Option.map_eq_some_iff.mpr ⟨fun i ↦ v i.succ, ih.mpr hl, ?_⟩
        exact funext fun i ↦ i.cases (by simp [h0]) (by simp)

/-- `natToVec` succeeds exactly when the length-free decoding has the expected length. -/
lemma natToVec_eq_none_of_length {e k : ℕ} (h : (natToList e).length ≠ k) :
    e.natToVec k = none := by
  rcases hv : e.natToVec k with _ | v
  · rfl
  · exact absurd (by rw [natToVec_eq_some_iff.mp hv]; simp) h

lemma natToVec_isSome_of_length {e k : ℕ} (h : (natToList e).length = k) :
    ∃ v : Fin k → ℕ, e.natToVec k = some v := by
  subst h
  refine ⟨fun i ↦ (natToList e).get i, natToVec_eq_some_iff.mpr ?_⟩
  exact (List.ofFn_get _).symm

end Nat

end
