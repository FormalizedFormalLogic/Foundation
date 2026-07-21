module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic
public import Foundation.FirstOrder.Arithmetic.HFS.Standard

@[expose] public section
/-!
# Executable term-code recognition in the standard model

`IsUTerm` is a `Fixpoint`: `Classical.choose!` all the way down, so nothing about it reduces, at
any `V`. This file gives the `V := ℕ` mirror — a `Bool`-valued recursion on the code — together
with the agreement theorem, and hence `Decidable (IsUTerm L t)` for `t : ℕ`.

The architecture is the one the derivation checker will reuse, in miniature:

* the mirror recurses on the *code*, with termination from the constructor bounds
  (`Nat.unpair_left_le`/`unpair_right_le`, the `Nat` form of `arity_lt_qqFunc` and friends);
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

/-- Executable mirror of `IsUTerm` at `V := ℕ`. -/
def IsUTerm.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (t : ℕ) : Bool :=
  match t with
  | 0 => false
  | e + 1 =>
    if (Nat.unpair e).1 = 0 then true
    else if (Nat.unpair e).1 = 1 then true
    else if (Nat.unpair e).1 = 2 then
      isFuncB L (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1 &&
        ((Nat.unpair (Nat.unpair e).2).1 ==
          natLen (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2) &&
        IsUTerm.checkVec L (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
    else false
termination_by t
decreasing_by
  exact Nat.lt_succ_of_le <| le_trans (Nat.unpair_right_le _) <|
    le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)

/-- Executable mirror of "every entry of the coded vector is a term". -/
def IsUTerm.checkVec (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (v : ℕ) : Bool :=
  match v with
  | 0 => true
  | w + 1 => IsUTerm.check L (Nat.unpair w).1 && IsUTerm.checkVec L (Nat.unpair w).2
termination_by v
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.unpair_left_le _)
  · exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

end

/-! ### Agreement -/

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]

@[simp] lemma IsUTerm.check_zero : IsUTerm.check L 0 = false := by simp [IsUTerm.check]

lemma IsUTerm.check_succ (e : ℕ) :
    IsUTerm.check L (e + 1) =
      (if (Nat.unpair e).1 = 0 then true
      else if (Nat.unpair e).1 = 1 then true
      else if (Nat.unpair e).1 = 2 then
        isFuncB L (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1 &&
          ((Nat.unpair (Nat.unpair e).2).1 ==
            natLen (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2) &&
          IsUTerm.checkVec L (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
      else false) := by
  rw [IsUTerm.check]

@[simp] lemma IsUTerm.checkVec_zero : IsUTerm.checkVec L 0 = true := by simp [IsUTerm.checkVec]

lemma IsUTerm.checkVec_succ (w : ℕ) :
    IsUTerm.checkVec L (w + 1) =
      (IsUTerm.check L (Nat.unpair w).1 && IsUTerm.checkVec L (Nat.unpair w).2) := by
  rw [IsUTerm.checkVec]

private lemma IsUTerm.check_and_checkVec (n : ℕ) :
    (IsUTerm.check L n = true ↔ IsUTerm L n) ∧
    (IsUTerm.checkVec L n = true ↔ ∀ i < len n, IsUTerm L n.[i]) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    constructor
    · match n with
      | 0 =>
        rw [IsUTerm.check_zero]
        simp only [Bool.false_eq_true, false_iff]
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
          rw [IsUTerm.check_succ, if_pos h, hb]
          simp
        · have hf : (e : ℕ) + 1 = ^&((Nat.unpair e).2) := by rw [nat_qqFvar_eq, ← h, he]
          rw [IsUTerm.check_succ, if_neg (by omega), if_pos h, hf]
          simp
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
          have hlt : (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 < e + 1 :=
            Nat.lt_succ_of_le <| le_trans (Nat.unpair_right_le _) <|
              le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
          rw [IsUTerm.check_succ, if_neg (by omega), if_neg (by omega), if_pos h, hfn,
            IsUTerm.func_iff]
          simp only [Bool.and_eq_true, beq_iff_eq, isFuncB_iff, IsUTermVec, (ih _ hlt).2,
            ← nat_len_eq]
          constructor
          · rintro ⟨⟨hF, hk⟩, hv⟩; exact ⟨hF, hk, fun i hi ↦ hv i (hk ▸ hi)⟩
          · rintro ⟨hF, hk, hv⟩; exact ⟨⟨hF, hk⟩, fun i hi ↦ hv i (hk ▸ hi)⟩
        · rw [IsUTerm.check_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
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
    · match n with
      | 0 => simp
      | w + 1 =>
        have hadj : (w : ℕ) + 1 = (Nat.unpair w).1 ∷ (Nat.unpair w).2 := by
          rw [succ_eq_adjoin w, nat_pi₁_eq, nat_pi₂_eq]
        have h₁ : (Nat.unpair w).1 < w + 1 := Nat.lt_succ_of_le (Nat.unpair_left_le _)
        have h₂ : (Nat.unpair w).2 < w + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le _)
        rw [IsUTerm.checkVec_succ]
        simp only [Bool.and_eq_true, (ih _ h₁).1, (ih _ h₂).2]
        rw [hadj, len_adjoin]
        constructor
        · rintro ⟨ht, hv⟩ i hi
          rcases Nat.eq_zero_or_pos i with rfl | hpos
          · simpa using ht
          · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            simpa using hv j (by simpa using hi)
        · intro H
          exact ⟨by simpa using H 0 (by simp),
            fun j hj ↦ by simpa using H (j + 1) (by simpa using hj)⟩

theorem IsUTerm.check_iff {t : ℕ} : IsUTerm.check L t = true ↔ IsUTerm L t :=
  (IsUTerm.check_and_checkVec t).1

theorem IsUTerm.checkVec_iff {v : ℕ} :
    IsUTerm.checkVec L v = true ↔ ∀ i < len v, IsUTerm L v.[i] :=
  (IsUTerm.check_and_checkVec v).2

instance decidableIsUTerm (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (t : ℕ) : Decidable (IsUTerm (V := ℕ) L t) := decidable_of_iff _ IsUTerm.check_iff

/-! ### It runs

`IsUTerm.check` is defined by well-founded recursion on the code, so it does **not** reduce
definitionally: `rfl`, `decide` and `Decidable.decide` all get stuck on it (the kernel cannot
unfold `WellFounded.fix`). Evaluation goes through the equation lemmas and `simp` instead. The
`Decidable` instance below is still a genuine decision procedure — it just is not one the kernel
can run. Turning `check` into a fuel-indexed structural recursion would restore `decide`, at the
cost of a fuel-monotonicity argument in the agreement proof; that decision belongs with the
derivation checker, which faces the same choice. -/

example : Decidable (IsUTerm (V := ℕ) ℒₒᵣ 1) := inferInstance

/-- The code of `^#0`, a bound variable. -/
example : IsUTerm (V := ℕ) ℒₒᵣ (Nat.pair 0 0 + 1) :=
  IsUTerm.check_iff.mp (by simp [IsUTerm.check_succ])

/-- The code of `^&0`, a free variable. -/
example : IsUTerm (V := ℕ) ℒₒᵣ (Nat.pair 1 0 + 1) :=
  IsUTerm.check_iff.mp (by simp [IsUTerm.check_succ])

/-- The code of `^func 0 0 0`, i.e. of the constant `0`. -/
example : IsUTerm (V := ℕ) ℒₒᵣ (Nat.pair 2 (Nat.pair 0 (Nat.pair 0 0)) + 1) :=
  IsUTerm.check_iff.mp <| by
    simp [IsUTerm.check_succ, natLen, natLenF, show isFuncB ℒₒᵣ 0 0 = true from by decide]

example : ¬IsUTerm (V := ℕ) ℒₒᵣ 0 := fun h ↦ by simpa using IsUTerm.check_iff.mpr h

end LO.FirstOrder.Arithmetic.Bootstrapping

end
