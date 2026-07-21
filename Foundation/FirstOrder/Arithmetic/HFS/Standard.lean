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

The twins have to be fast as well as reducible, because a derivation code is a nest of `Nat.pair`s
and so grows very quickly: a two-rule derivation over a formula of code `3974` already has a code
of `254337` bits, and destructuring it calls `natSqrt` a handful of times. The obvious schemes are
too slow at that size — halving bit by bit for the bit length, and refining one bit at a time under
a full-width multiplication for the square root, are quadratic or worse in the bit length. So
`natBitLen` doubles instead (logarithmically many comparisons, and a result within a factor of two
of the true length, which is all its specification claims), and `natSqrt` is a fuel-indexed copy of
`Nat.sqrt.iter`, the Newton iteration core already uses (logarithmically many divisions). Measured
compiled on that `254337`-bit code: `natBitLen` `7.8 s → 0 ms`, `natSqrt` `34.8 s → 2.1 s`,
`natFstIdx` `36.5 s → 2.0 s`, and the derivation check it feeds `149 s → 7.2 s`. What remains is
the big divisions themselves.

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

/-- `bitLenUp s n k` doubles `k` until `2 ^ k` overshoots `n`. The result is within a factor of
two of the true bit length, which is all `natBitLen_spec` claims, and it costs logarithmically many
big-number comparisons instead of linearly many halvings. -/
def bitLenUp : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k
  | s + 1, n, k => if n < 2 ^ k then k else bitLenUp s n (2 * k)

def natBitLenF (s n : ℕ) : ℕ := bitLenUp s n 1

def natBitLen (n : ℕ) : ℕ := natBitLenF n n

lemma bitLenUp_spec : ∀ s n k, n < 2 ^ (k * 2 ^ s) → n < 2 ^ bitLenUp s n k := by
  intro s
  induction s with
  | zero => intro n k h; simpa [bitLenUp] using h
  | succ s ih =>
    intro n k h
    rw [bitLenUp]
    by_cases hc : n < 2 ^ k
    · rw [if_pos hc]; exact hc
    · rw [if_neg hc]
      refine ih n (2 * k) ?_
      have e : 2 * k * 2 ^ s = k * 2 ^ (s + 1) := by
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc]
      rw [e]; exact h

lemma natBitLenF_spec : ∀ s n, n ≤ s → n < 2 ^ natBitLenF s n := by
  intro s n hn
  refine bitLenUp_spec s n 1 ?_
  have h1 : s < 2 ^ s := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ s ≤ 2 ^ 2 ^ s :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt Nat.lt_two_pow_self)
  simpa using Nat.lt_of_le_of_lt hn (Nat.lt_of_lt_of_le h1 h2)

lemma natBitLen_spec (n : ℕ) : n < 2 ^ natBitLen n := natBitLenF_spec n n le_rfl

/-! ### Square root -/

/-- `sqrtIterF` is a fuel-indexed structural copy of `Nat.sqrt.iter`, the Newton iteration core
already uses. Each step is one big division and the guess strictly decreases, so fuel equal to the
starting guess always suffices — which is the whole of `sqrtIterF_eq`. Correctness then comes for
free from `Nat.sqrt.iter_sq_le` and `Nat.sqrt.lt_iter_succ_sq`; nothing here re-derives it. -/
def sqrtIterF : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | s + 1, n, g => if (g + n / g) / 2 < g then sqrtIterF s n ((g + n / g) / 2) else g

lemma sqrtIterF_eq : ∀ s n g, g ≤ s → sqrtIterF s n g = Nat.sqrt.iter n g := by
  intro s
  induction s with
  | zero =>
    intro n g hg
    obtain rfl : g = 0 := by omega
    rw [sqrtIterF, Nat.sqrt.iter.eq_def]
    simp
  | succ s ih =>
    intro n g hg
    rw [sqrtIterF, Nat.sqrt.iter.eq_def]
    by_cases h : (g + n / g) / 2 < g
    · rw [if_pos h, dif_pos h]; exact ih n _ (by omega)
    · rw [if_neg h, dif_neg h]

def natSqrt (n : ℕ) : ℕ :=
  let g := 2 ^ ((natBitLen n + 1) / 2)
  sqrtIterF g n g

lemma natSqrt_spec (n : ℕ) :
    natSqrt n * natSqrt n ≤ n ∧ n < (natSqrt n + 1) * (natSqrt n + 1) := by
  rw [natSqrt, sqrtIterF_eq _ _ _ le_rfl]
  refine ⟨Nat.sqrt.iter_sq_le _ _, Nat.sqrt.lt_iter_succ_sq _ _ ?_⟩
  have hb : n < 2 ^ natBitLen n := natBitLen_spec n
  have hle : natBitLen n ≤ (natBitLen n + 1) / 2 + (natBitLen n + 1) / 2 := by omega
  have h : (2 : ℕ) ^ natBitLen n ≤ 2 ^ ((natBitLen n + 1) / 2) * 2 ^ ((natBitLen n + 1) / 2) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by norm_num) hle
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hb h)
    (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))

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

/-! ### `listMax`

Proved **spec-first**, deliberately. `listMax_adjoin` produces `x ⊔ listMax v`, whose `⊔` at `ℕ`
carries `SemilatticeSup.toMax` (via `instDistribLatticeOfLinearOrder`), while a `max` written in a
fresh definition picks up `Nat.instMax`. The two are propositionally equal but not definitionally
so, and no lemma stating `a ⊔ b = max a b` helps: written in one statement, both sides elaborate to
the *same* instance and the lemma is a tautology.

The way past is not to unify them but never to mention both. Upstream's `listMaxss_le_iff`
characterises `listMax` as the *least upper bound* of the entries — an order statement, with no
`max` in it — and that pins it down uniquely (the empty vector included: its least upper bound is
`0`). So the mirror is proved to meet the same specification and agreement follows by antisymmetry.
The only bridge needed is `nat_le_iff`, on `≤`, which this file already has. -/

def listMaxF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, v + 1 => max (natPi₁ v) (listMaxF s (natPi₂ v))

def natListMax (v : ℕ) : ℕ := listMaxF v v

private lemma listMaxF_succ (s v : ℕ) :
    listMaxF (s + 1) (v + 1) = max (Nat.unpair v).1 (listMaxF s (Nat.unpair v).2) := by
  rw [listMaxF]; simp only [natPi₁, natPi₂, natUnpair_eq]

/-- The mirror meets `listMax`'s own specification: it is an upper bound of the entries, and the
least one. Neither half mentions `max` on the `listMax` side, which is the point — the two `Max ℕ`
instances never meet in a single statement. -/
private lemma listMaxF_spec (s : ℕ) : ∀ v ≤ s,
    (∀ i < len v, v.[i] ≤ listMaxF s v) ∧
    (∀ z, (∀ i < len v, v.[i] ≤ z) → listMaxF s v ≤ z) := by
  induction s with
  | zero =>
    intro v hv
    obtain rfl : v = 0 := by omega
    refine ⟨by simp, fun z _ ↦ by simp [listMaxF]⟩
  | succ m ih =>
    intro v hv
    match v with
    | 0 => exact ⟨by simp, fun z _ ↦ by simp [listMaxF]⟩
    | w + 1 =>
      have hadj : (w : ℕ) + 1 = (Nat.unpair w).1 ∷ (Nat.unpair w).2 := by
        rw [succ_eq_adjoin w, nat_pi₁_eq, nat_pi₂_eq]
      have h₂ : (Nat.unpair w).2 ≤ m := le_trans (Nat.unpair_right_le _) (by omega)
      obtain ⟨ihb, ihl⟩ := ih _ h₂
      rw [listMaxF_succ, hadj, len_adjoin]
      constructor
      · intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simp
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          simpa using le_trans (ihb j (by simpa using hi)) (Nat.le_max_right _ _)
      · intro z hz
        refine Nat.max_le.mpr ⟨by simpa using hz 0 (by simp), ihl z fun j hj ↦ ?_⟩
        simpa using hz (j + 1) (by simpa using hj)

theorem nat_listMax_eq (v : ℕ) : listMax v = natListMax v := by
  obtain ⟨hb, hl⟩ := listMaxF_spec v v le_rfl
  refine Nat.le_antisymm ?_ ?_
  · exact nat_le_iff.mp (listMaxss_le_iff.mpr fun i hi ↦ nat_le_iff.mpr (hb i hi))
  · exact hl _ fun i hi ↦ nat_le_iff.mp (nth_le_listMax hi)

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

example : natListMax 0 = 0 := by decide

example : natListMax (Nat.pair 3 (Nat.pair 5 0 + 1) + 1) = 5 := by decide

end LO.FirstOrder.Arithmetic

end
