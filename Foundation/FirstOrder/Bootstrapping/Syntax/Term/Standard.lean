module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic
public import Foundation.FirstOrder.Arithmetic.HFS.Standard

@[expose] public section
/-!
# Executable term-code recognition in the standard model

`IsUTerm` is a `Fixpoint`: `Classical.choose!` all the way down, so nothing about it reduces, at
any `V`. This file gives the `V := ℕ` mirror — a `Bool`-valued recursion on the code — together
with the agreement theorem, and hence `Decidable (IsUTerm L t)` for `t : ℕ` that `decide` can
actually run.

The architecture is the one the derivation checker will reuse, in miniature:

* the mirror is **fuel-indexed** — structural in the fuel, so it reduces in the kernel — and the
  fuel `t` supplied for the code `t` is adequate because every recursive call strictly decreases
  the code (`Nat.unpair_left_le`/`unpair_right_le`, the `Nat` form of `arity_lt_qqFunc` and
  friends). Codes are destructured with `natPi₁`/`natPi₂`, the reducible twins, never with
  `Nat.unpair`, which does not reduce;
* agreement is proved by strong induction on the code against `IsUTerm.case_iff`, never against
  `limSeq` — `case_iff` already packages the fixpoint;
* the negative direction needs the constructors to be *readable off* the code: a code whose tag
  is not `0`, `1` or `2` is no term, which is exactly `Nat.unpair_pair` applied to
  `nat_qqBvar_eq`/`nat_qqFvar_eq`/`nat_qqFunc_eq`.

`Language.DecidableSymbols` supplies the one thing that cannot be computed generically: whether a
code is a function or relation symbol of a given arity. `L.IsFunc k f` unfolds to satisfaction of
a `𝚺₀` formula, which is decidable in the arithmetical sense but carries no Lean `Decidable`
instance, so — as with `Theory.DecidableΔ₁` — it is supplied per language. `ℒₒᵣ` is instantiated
here.
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

/-! ### The language interface -/

class _root_.LO.FirstOrder.Language.DecidableSymbols
    (L : Language) [L.Encodable] [L.LORDefinable] where
  isFuncB : ℕ → ℕ → Bool
  isFuncB_iff (k f : ℕ) : isFuncB k f = true ↔ L.IsFunc (V := ℕ) k f
  isRelB : ℕ → ℕ → Bool
  isRelB_iff (k r : ℕ) : isRelB k r = true ↔ L.IsRel (V := ℕ) k r

export Language.DecidableSymbols (isFuncB isFuncB_iff isRelB isRelB_iff)

instance : Language.DecidableSymbols ℒₒᵣ where
  isFuncB k f := (k == 0 && f == 0) || (k == 0 && f == 1) || (k == 2 && f == 0) || (k == 2 && f == 1)
  isFuncB_iff k f := by rw [isFunc_def, Arithmetic.func_def_LOR]; simp; tauto
  isRelB k r := (k == 2 && r == 0) || (k == 2 && r == 1)
  isRelB_iff k r := by rw [isRel_def, Arithmetic.rel_def_LOR]; simp; tauto

/-! ### The term constructors at `V := ℕ` -/

lemma nat_qqBvar_eq (z : ℕ) : (^#z : ℕ) = Nat.pair 0 z + 1 := by rw [qqBvar, nat_pair_eq]

lemma nat_qqFvar_eq (x : ℕ) : (^&x : ℕ) = Nat.pair 1 x + 1 := by rw [qqFvar, nat_pair_eq]

lemma nat_qqFunc_eq (k f v : ℕ) :
    (^func k f v : ℕ) = Nat.pair 2 (Nat.pair k (Nat.pair f v)) + 1 := by
  simp [qqFunc, nat_pair_eq]

/-! ### The mirror -/

mutual

/-- Fuel-indexed executable mirror of `IsUTerm` at `V := ℕ`. -/
def IsUTerm.checkF (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] :
    ℕ → ℕ → Bool
  | 0, _ => false
  | _ + 1, 0 => false
  | s + 1, e + 1 =>
    if natPi₁ e = 0 then true
    else if natPi₁ e = 1 then true
    else if natPi₁ e = 2 then
      isFuncB L (natPi₁ (natPi₂ e)) (natPi₁ (natPi₂ (natPi₂ e))) &&
        (natPi₁ (natPi₂ e) == natLen (natPi₂ (natPi₂ (natPi₂ e)))) &&
        IsUTerm.checkVecF L s (natPi₂ (natPi₂ (natPi₂ e)))
    else false

/-- Fuel-indexed mirror of "every entry of the coded vector is a term". -/
def IsUTerm.checkVecF (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] :
    ℕ → ℕ → Bool
  | 0, v => v == 0
  | _ + 1, 0 => true
  | s + 1, w + 1 => IsUTerm.checkF L s (natPi₁ w) && IsUTerm.checkVecF L s (natPi₂ w)

end

/-- The fuel `t` is adequate for the code `t`: every recursive call strictly decreases the code. -/
def IsUTerm.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (t : ℕ) : Bool := IsUTerm.checkF L t t

def IsUTerm.checkVec (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (v : ℕ) : Bool := IsUTerm.checkVecF L v v

/-! ### Agreement -/

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]

private lemma IsUTerm.checkF_succ (s e : ℕ) :
    IsUTerm.checkF L (s + 1) (e + 1) =
      (if (Nat.unpair e).1 = 0 then true
      else if (Nat.unpair e).1 = 1 then true
      else if (Nat.unpair e).1 = 2 then
        isFuncB L (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1 &&
          ((Nat.unpair (Nat.unpair e).2).1 ==
            natLen (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2) &&
          IsUTerm.checkVecF L s (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
      else false) := by
  rw [IsUTerm.checkF]; simp only [natPi₁, natPi₂, natUnpair_eq]

private lemma IsUTerm.checkVecF_succ (s w : ℕ) :
    IsUTerm.checkVecF L (s + 1) (w + 1) =
      (IsUTerm.checkF L s (Nat.unpair w).1 && IsUTerm.checkVecF L s (Nat.unpair w).2) := by
  rw [IsUTerm.checkVecF]; simp only [natPi₁, natPi₂, natUnpair_eq]

private lemma IsUTerm.checkF_iff_aux (s : ℕ) :
    (∀ t ≤ s, (IsUTerm.checkF L s t = true ↔ IsUTerm L t)) ∧
    (∀ v ≤ s, (IsUTerm.checkVecF L s v = true ↔ ∀ i < len v, IsUTerm L v.[i])) := by
  induction s with
  | zero =>
    constructor
    · intro t ht
      obtain rfl : t = 0 := by omega
      simp only [IsUTerm.checkF, Bool.false_eq_true, false_iff]
      intro hc
      rcases hc.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
      · rw [nat_qqBvar_eq] at hz; omega
      · rw [nat_qqFvar_eq] at hx; omega
      · rw [nat_qqFunc_eq] at hv; omega
    · intro v hv
      obtain rfl : v = 0 := by omega
      simp [IsUTerm.checkVecF]
  | succ n ih =>
    constructor
    · intro t ht
      match t with
      | 0 =>
        simp only [IsUTerm.checkF, Bool.false_eq_true, false_iff]
        intro hc
        rcases hc.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
        · rw [nat_qqBvar_eq] at hz; omega
        · rw [nat_qqFvar_eq] at hx; omega
        · rw [nat_qqFunc_eq] at hv; omega
      | e + 1 =>
        have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
        rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
            3 ≤ (Nat.unpair e).1 by omega) with h | h | h | h
        · have hb : (e : ℕ) + 1 = ^#((Nat.unpair e).2) := by rw [nat_qqBvar_eq, ← h, he]
          rw [IsUTerm.checkF_succ, if_pos h, hb]; simp
        · have hf : (e : ℕ) + 1 = ^&((Nat.unpair e).2) := by rw [nat_qqFvar_eq, ← h, he]
          rw [IsUTerm.checkF_succ, if_neg (by omega), if_pos h, hf]; simp
        · have e2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
              = (Nat.unpair e).2 := Nat.pair_unpair _
          have e3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
              (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
              = (Nat.unpair (Nat.unpair e).2).2 := Nat.pair_unpair _
          have hfn : (e : ℕ) + 1 =
              ^func (Nat.unpair (Nat.unpair e).2).1
                (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
                (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
            rw [nat_qqFunc_eq, e3, e2, ← h, he]
          have hle : (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 ≤ n :=
            le_trans (le_trans (Nat.unpair_right_le _) <|
              le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
          rw [IsUTerm.checkF_succ, if_neg (by omega), if_neg (by omega), if_pos h, hfn,
            IsUTerm.func_iff]
          simp only [Bool.and_eq_true, beq_iff_eq, isFuncB_iff, IsUTermVec, ih.2 _ hle,
            ← nat_len_eq]
          constructor
          · rintro ⟨⟨hF, hk⟩, hv⟩; exact ⟨hF, hk, fun i hi ↦ hv i (hk ▸ hi)⟩
          · rintro ⟨hF, hk, hv⟩; exact ⟨⟨hF, hk⟩, fun i hi ↦ hv i (hk ▸ hi)⟩
        · rw [IsUTerm.checkF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp only [Bool.false_eq_true, false_iff]
          intro hc
          rcases hc.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
          · rw [nat_qqBvar_eq] at hz
            have he' : e = Nat.pair 0 z := by omega
            rw [he'] at h; simp at h
          · rw [nat_qqFvar_eq] at hx
            have he' : e = Nat.pair 1 x := by omega
            rw [he'] at h; simp at h
          · rw [nat_qqFunc_eq] at hv
            have he' : e = Nat.pair 2 (Nat.pair k (Nat.pair f v)) := by omega
            rw [he'] at h; simp at h
    · intro v hv
      match v with
      | 0 => simp [IsUTerm.checkVecF]
      | w + 1 =>
        have hadj : (w : ℕ) + 1 = (Nat.unpair w).1 ∷ (Nat.unpair w).2 := by
          rw [succ_eq_adjoin w, nat_pi₁_eq, nat_pi₂_eq]
        have h₁ : (Nat.unpair w).1 ≤ n := le_trans (Nat.unpair_left_le _) (by omega)
        have h₂ : (Nat.unpair w).2 ≤ n := le_trans (Nat.unpair_right_le _) (by omega)
        rw [IsUTerm.checkVecF_succ]
        simp only [Bool.and_eq_true, ih.1 _ h₁, ih.2 _ h₂]
        rw [hadj, len_adjoin]
        constructor
        · rintro ⟨ht, hvv⟩ i hi
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · simpa using ht
          · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            simpa using hvv j (by simpa using hi)
        · intro H
          exact ⟨by simpa using H 0 (by simp),
            fun j hj ↦ by simpa using H (j + 1) (by simpa using hj)⟩

theorem IsUTerm.check_iff {t : ℕ} : IsUTerm.check L t = true ↔ IsUTerm L t :=
  (IsUTerm.checkF_iff_aux t).1 t le_rfl

theorem IsUTerm.checkVec_iff {v : ℕ} :
    IsUTerm.checkVec L v = true ↔ ∀ i < len v, IsUTerm L v.[i] :=
  (IsUTerm.checkF_iff_aux v).2 v le_rfl

instance decidableIsUTerm (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (t : ℕ) : Decidable (IsUTerm (V := ℕ) L t) := decidable_of_iff _ IsUTerm.check_iff

/-! ### It runs

The mirror is fuel-indexed and destructures with `natPi₁`/`natPi₂`, so it reduces in the kernel and
`decide` computes it — on bare numerals, not just on codes presented as `Nat.pair` trees.

One wrinkle: the `decide` *tactic* cannot be pointed straight at `IsUTerm …`, because it normalises
the proposition before synthesising `Decidable` and loses the head. Going through the agreement
theorem — `IsUTerm.check_iff.mp (by decide)` — works, and is more informative anyway: it names the
mirror that did the computing. `inferInstance` finds `decidableIsUTerm` without trouble. -/

example : IsUTerm.check ℒₒᵣ 7 = true := by decide

example : Decidable (IsUTerm (V := ℕ) ℒₒᵣ 7) := inferInstance

/-- A bare numeral witness: `7 = ^func 0 0 0`, the constant `0`. -/
example : IsUTerm (V := ℕ) ℒₒᵣ 7 := IsUTerm.check_iff.mp (by decide)

/-- `1 = ^#0`, a bound variable. -/
example : IsUTerm (V := ℕ) ℒₒᵣ 1 := IsUTerm.check_iff.mp (by decide)

/-- `3 = ^&0`, a free variable. -/
example : IsUTerm (V := ℕ) ℒₒᵣ 3 := IsUTerm.check_iff.mp (by decide)

example : ¬IsUTerm (V := ℕ) ℒₒᵣ 0 := fun h ↦ absurd (IsUTerm.check_iff.mpr h) (by decide)

/-- `13` has constructor tag `3`. -/
example : ¬IsUTerm (V := ℕ) ℒₒᵣ 13 := fun h ↦ absurd (IsUTerm.check_iff.mpr h) (by decide)

end LO.FirstOrder.Arithmetic.Bootstrapping

end
