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

A second thing is needed for any of this to *run*. Core's `Nat.sqrt` is defined by well-founded
recursion, so it does not reduce in the kernel, and neither does `Nat.unpair`, which calls it —
`decide` gets stuck on `Nat.unpair 6`. So this file also carries reducible twins: `natSqrt`,
proved against the *specification* `k * k ≤ n < (k + 1) * (k + 1)` and only then identified with
`Nat.sqrt`, and `natUnpair`/`natPi₁`/`natPi₂`/`natFstIdx` on top of it. Everything an executable
mirror destructures a code with should be the twin, not the `Nat` original.

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

/-! ### Bit length -/

def natBitLenF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | s + 1, n => if n = 0 then 0 else natBitLenF s (n / 2) + 1

def natBitLen (n : ℕ) : ℕ := natBitLenF n n

lemma natBitLenF_spec : ∀ s n, n ≤ s → n < 2 ^ natBitLenF s n := by
  intro s
  induction s with
  | zero =>
    intro n hn
    have hz : n = 0 := by omega
    subst hz
    simp [natBitLenF]
  | succ s ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [natBitLenF]
    · have h2 : n / 2 ≤ s := by omega
      have := ih (n / 2) h2
      rw [natBitLenF, if_neg (by omega), Nat.pow_succ]
      omega

lemma natBitLen_spec (n : ℕ) : n < 2 ^ natBitLen n := natBitLenF_spec n n le_rfl

/-! ### Square root -/

/-- `natSqrtAux b n acc` refines `acc` by the bits `2^(b-1), …, 2^0`, maintaining
`acc * acc ≤ n < (acc + 2 ^ b) * (acc + 2 ^ b)`. -/
def natSqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | b + 1, n, acc =>
    if (acc + 2 ^ b) * (acc + 2 ^ b) ≤ n then natSqrtAux b n (acc + 2 ^ b) else natSqrtAux b n acc

def natSqrt (n : ℕ) : ℕ := natSqrtAux ((natBitLen n + 1) / 2) n 0

lemma natSqrtAux_spec : ∀ b n acc, acc * acc ≤ n → n < (acc + 2 ^ b) * (acc + 2 ^ b) →
    natSqrtAux b n acc * natSqrtAux b n acc ≤ n ∧
      n < (natSqrtAux b n acc + 1) * (natSqrtAux b n acc + 1) := by
  intro b
  induction b with
  | zero => intro n acc h₁ h₂; simpa [natSqrtAux] using ⟨h₁, by simpa using h₂⟩
  | succ b ih =>
    intro n acc h₁ h₂
    rw [natSqrtAux]
    by_cases hc : (acc + 2 ^ b) * (acc + 2 ^ b) ≤ n
    · rw [if_pos hc]
      refine ih n (acc + 2 ^ b) hc ?_
      have : acc + 2 ^ b + 2 ^ b = acc + 2 ^ (b + 1) := by rw [Nat.pow_succ]; omega
      rw [this]; exact h₂
    · rw [if_neg hc]
      exact ih n acc h₁ (by omega)

lemma natSqrt_spec (n : ℕ) :
    natSqrt n * natSqrt n ≤ n ∧ n < (natSqrt n + 1) * (natSqrt n + 1) := by
  refine natSqrtAux_spec _ n 0 (by simp) ?_
  have hb : n < 2 ^ natBitLen n := natBitLen_spec n
  have hle : natBitLen n ≤ (natBitLen n + 1) / 2 + (natBitLen n + 1) / 2 := by omega
  have : (2 : ℕ) ^ natBitLen n ≤ 2 ^ ((natBitLen n + 1) / 2) * 2 ^ ((natBitLen n + 1) / 2) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) hle
  simpa using Nat.lt_of_lt_of_le hb this

lemma natSqrt_eq (n : ℕ) : natSqrt n = Nat.sqrt n := by
  have h := natSqrt_spec n
  have h₁ : natSqrt n ≤ Nat.sqrt n := Nat.le_sqrt.mpr h.1
  have h₂ : Nat.sqrt n < natSqrt n + 1 := Nat.sqrt_lt.mpr h.2
  omega

/-! ### Unpairing -/

def natUnpair (n : ℕ) : ℕ × ℕ :=
  let s := natSqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

lemma natUnpair_eq (n : ℕ) : natUnpair n = Nat.unpair n := by
  simp [natUnpair, Nat.unpair, natSqrt_eq]

/-! ### Reducible twins for the destructuring bridges -/

def natPi₁ (a : ℕ) : ℕ := (natUnpair a).1

def natPi₂ (a : ℕ) : ℕ := (natUnpair a).2

def natFstIdx (p : ℕ) : ℕ := natPi₁ (p - 1)

def natSndIdx (p : ℕ) : ℕ := natPi₂ (p - 1)

lemma natPi₁_eq (a : ℕ) : π₁ a = natPi₁ a := by rw [nat_pi₁_eq, natPi₁, natUnpair_eq]

lemma natPi₂_eq (a : ℕ) : π₂ a = natPi₂ a := by rw [nat_pi₂_eq, natPi₂, natUnpair_eq]

lemma natFstIdx_eq (p : ℕ) : fstIdx p = natFstIdx p := by
  rw [nat_fstIdx_eq, natFstIdx, natPi₁, natUnpair_eq]

lemma natSndIdx_eq (p : ℕ) : sndIdx p = natSndIdx p := by
  show π₂ (Arithmetic.sub p 1) = natSndIdx p
  rw [nat_pi₂_eq, nat_sub_eq, natSndIdx, natPi₂, natUnpair_eq]

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

A coded vector is the cons list `x ∷ v = ⟪x, v⟫ + 1` with `0` for nil, so `len` is a recursion on
the code once `⟪·,·⟫` is `Nat.pair`; it is fuel-indexed, and destructures with `natPi₂`, so that it
reduces. -/

def natLenF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, v + 1 => natLenF s (natPi₂ v) + 1

/-- `len` at `V := ℕ`. -/
def natLen (v : ℕ) : ℕ := natLenF v v

lemma natLenF_eq : ∀ s v, v ≤ s → len v = natLenF s v := by
  intro s
  induction s with
  | zero =>
    intro v hv
    have hz : v = 0 := by omega
    subst hz
    simp [natLenF]
  | succ n ih =>
    intro v hv
    match v with
    | 0 => simp [natLenF]
    | w + 1 =>
      have hle : natPi₂ w ≤ n := by
        rw [← natPi₂_eq, nat_pi₂_eq]
        exact le_trans (Nat.unpair_right_le _) (by omega)
      have h₁ : len ((w : ℕ) + 1) = len (natPi₂ w) + 1 := by
        rw [succ_eq_adjoin w, len_adjoin, natPi₂_eq]
      rw [h₁, natLenF, ih _ hle]

lemma nat_len_eq (v : ℕ) : len v = natLen v := natLenF_eq v v le_rfl

/-- `nth` at `V := ℕ`. Structural in the index, so it reduces. -/
def natNth (v : ℕ) : ℕ → ℕ
  | 0 => natFstIdx v
  | i + 1 => natNth (natSndIdx v) i

lemma nat_nth_eq (v i : ℕ) : v.[i] = natNth v i := by
  induction i generalizing v with
  | zero => rw [nth_zero, natNth, natFstIdx_eq]
  | succ i ih => rw [nth_succ, natNth, ih, natSndIdx_eq]


/-! ### A reducible `insert`

`nat_insert_eq` states what `insert` is at `ℕ`, but as a rewrite rule it is unavailable to
`decide`. Mirrors that *build* sets need the reducible form. -/

/-- `insert` at `V := ℕ`, reducibly. -/
def natInsert (i a : ℕ) : ℕ := if a.testBit i then a else a + 2 ^ i

lemma natInsert_eq (i a : ℕ) : (insert i a : ℕ) = natInsert i a := nat_insert_eq i a

@[simp] lemma mem_natInsert_iff {i j a : ℕ} : i ∈ natInsert j a ↔ i = j ∨ i ∈ a := by
  rw [← natInsert_eq]; exact mem_bitInsert_iff

lemma mem_foldr_natInsert {y : ℕ} {l : List ℕ} :
    y ∈ l.foldr natInsert 0 ↔ y ∈ l := by
  induction l with
  | nil => simp [nat_mem_iff_testBit (x := y) (s := 0)]
  | cons x l ih => simp [ih]

/-! ### The payoff -/

example : (3 : ℕ) ∈ (40 : ℕ) := by decide

example : (4 : ℕ) ∉ (40 : ℕ) := by decide

example : (8 : ℕ) ⊆ (40 : ℕ) := by decide

example : ¬((2 : ℕ) ⊆ (40 : ℕ)) := by decide

example : natSqrt 6 = 2 := by decide

example : natUnpair 6 = (2, 0) := by decide

/-- A ten-digit input: kernel `Nat` is GMP-backed, so this is cheap. -/
example : natUnpair 1234567890 = (29394, 35136) := by decide

example : natLen (Nat.pair 3 (Nat.pair 5 0 + 1) + 1) = 2 := by decide

example : natNth (Nat.pair 3 (Nat.pair 5 0 + 1) + 1) 1 = 5 := by decide

example : natInsert 3 (natInsert 5 0) = 40 := by decide

end LO.FirstOrder.Arithmetic

end
