module

public import Foundation.FirstOrder.Arithmetic.HFS.Vec
public import Mathlib.Data.Nat.BitIndices

@[expose] public section
/-!
# The hereditarily finite sets of the standard model

Every primitive the arithmetized-syntax development is built from is `noncomputable`, and not
incidentally so: `⟪·,·⟫`, `unpair` and `√` branch on a classically decidable comparison or are
introduced by `Classical.choose!`, and `∈`/`insert`/`⊆` go through `Exp.exp`, which is itself a
`Classical.choose!`. For a general model `V` there is nothing to be done about that.

At `V := ℕ` all of them nevertheless *compute*, and this file identifies each one with the
corresponding executable `Nat` operation — `Nat.pair`, `Nat.unpair`, `Nat.sqrt`, `Nat.testBit`,
`2 ^ ·`. `Semiterm.nat_pair_eq` (`IOpen/Basic.lean`) is the prototype; the rest follow it.

The payoff is the `Decidable` instances: for `x s t : ℕ`, `x ∈ s` and `s ⊆ t` become `decide`-able,
which is what any executable procedure over coded objects needs.

Note that `≤` is subtle at `V := ℕ`: a lemma stated for a general `V` carries
`instLE_foundation` (`x ≤ y ↔ x = y ∨ x < y`), whereas `a ≤ b` written at `ℕ` elaborates with
`instLENat`. `nat_le_iff` is the bridge, and is needed whenever a general-`V` lemma is applied
at `ℕ` against a `Nat`-side hypothesis.
-/

namespace LO.FirstOrder.Arithmetic

/-! ### Order and truncated subtraction -/

lemma nat_le_iff {a b : ℕ} : @LE.le ℕ instLE_foundation a b ↔ a ≤ b := by
  show a = b ∨ a < b ↔ a ≤ b
  omega

lemma nat_sub_eq (a b : ℕ) : Arithmetic.sub a b = a - b := by
  rcases Nat.lt_or_ge a b with (h | h)
  · have : Arithmetic.sub a b = 0 := sub_spec_of_lt h
    omega
  · have : a = b + Arithmetic.sub a b := sub_spec_of_ge (nat_le_iff.mpr h)
    omega

/-! ### `√`, `unpair`, `π₁`, `π₂` -/

lemma nat_sqrt_eq (a : ℕ) : √a = Nat.sqrt a :=
  sqrt_eq_of_le_of_lt (nat_le_iff.mpr <| by simpa [sq] using Nat.sqrt_le' a)
    (by simpa [sq] using Nat.lt_succ_sqrt' a)

lemma nat_unpair_eq (a : ℕ) : unpair a = Nat.unpair a := by
  have h : Nat.pair (π₁ a) (π₂ a) = a := by rw [← nat_pair_eq]; exact pair_unpair a
  calc unpair a = (π₁ a, π₂ a)                        := rfl
    _           = Nat.unpair (Nat.pair (π₁ a) (π₂ a)) := by rw [Nat.unpair_pair]
    _           = Nat.unpair a                        := by rw [h]

lemma nat_pi₁_eq (a : ℕ) : π₁ a = (Nat.unpair a).1 := by rw [← nat_unpair_eq]

lemma nat_pi₂_eq (a : ℕ) : π₂ a = (Nat.unpair a).2 := by rw [← nat_unpair_eq]

/-! ### `fstIdx` -/

lemma nat_fstIdx_eq (p : ℕ) : fstIdx p = (Nat.unpair (p - 1)).1 := by
  show π₁ (Arithmetic.sub p 1) = (Nat.unpair (p - 1)).1
  rw [nat_pi₁_eq, nat_sub_eq]

/-! ### Membership -/

lemma nat_mem_iff_testBit {x s : ℕ} : x ∈ s ↔ s.testBit x = true := by
  induction s using Nat.binaryRec generalizing x
  case zero => simp
  case bit b s ih =>
    have h₀ : 2 * s / 2 = s := by omega
    have h₁ : (2 * s + 1) / 2 = s := by omega
    cases b
    · cases' x with x
      · simp only [Nat.bit_false_apply, Nat.testBit_zero, Nat.mul_mod_right, zero_ne_one,
          decide_false, Bool.false_eq_true, iff_false]
        exact zero_not_mem s
      · simp only [Nat.bit_false_apply, Nat.testBit_succ, h₀]
        exact succ_mem_two_mul_iff.trans ih
    · cases' x with x
      · simp only [Nat.bit_true_apply, Nat.testBit_zero, Nat.mul_add_mod_self_left, Nat.mod_succ,
          decide_true, iff_true]
        exact zero_mem_double_add_one s
      · simp only [Nat.bit_true_apply, Nat.testBit_succ, h₁]
        exact succ_mem_two_mul_succ_iff.trans ih

instance (x s : ℕ) : Decidable (x ∈ s) := decidable_of_iff _ nat_mem_iff_testBit.symm

/-! ### `∅`, `{·}`, `insert`, `⊆` -/

lemma nat_emptyset_eq : (∅ : ℕ) = 0 := emptyset_def

lemma nat_singleton_eq (a : ℕ) : ({a} : ℕ) = 2 ^ a := by rw [singleton_def]; exact exp_nat

lemma nat_insert_eq (i a : ℕ) : (insert i a : ℕ) = if a.testBit i then a else a + 2 ^ i := by
  rw [insert_eq, bitInsert, exp_nat]
  simp only [nat_mem_iff_testBit]

lemma nat_subset_iff {a b : ℕ} : a ⊆ b ↔ a.bitIndices.all (b.testBit ·) = true := by
  simp only [List.all_eq_true, Nat.mem_bitIndices, subset_iff]
  exact ⟨fun h i hi ↦ nat_mem_iff_testBit.mp (h _ (nat_mem_iff_testBit.mpr hi)),
    fun h i hi ↦ nat_mem_iff_testBit.mpr (h _ (nat_mem_iff_testBit.mp hi))⟩

instance (a b : ℕ) : Decidable (a ⊆ b) := decidable_of_iff _ nat_subset_iff.symm

/-! ### Coded vectors

A coded vector is the cons list `x ∷ v = ⟪x, v⟫ + 1` with `0` for nil, so `len` is a structural
recursion on the code once `⟪·,·⟫` is `Nat.pair`. -/

/-- `len` at `V := ℕ`. -/
def natLen : ℕ → ℕ
  | 0 => 0
  | v + 1 => natLen (Nat.unpair v).2 + 1
  decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_right_le v)

lemma nat_len_eq (v : ℕ) : len v = natLen v := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    match v with
    | 0 => simp [natLen]
    | w + 1 =>
      have h₁ : len ((w : ℕ) + 1) = len (Nat.unpair w).2 + 1 := by
        rw [succ_eq_adjoin w, len_adjoin, nat_pi₂_eq]
      have h₂ : natLen (w + 1) = natLen (Nat.unpair w).2 + 1 := by simp [natLen]
      rw [h₁, h₂, ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le w))]

/-! ### The payoff -/

example : (3 : ℕ) ∈ (40 : ℕ) := by decide

example : (4 : ℕ) ∉ (40 : ℕ) := by decide

example : (8 : ℕ) ⊆ (40 : ℕ) := by decide

example : ¬((2 : ℕ) ⊆ (40 : ℕ)) := by decide

end LO.FirstOrder.Arithmetic

end
