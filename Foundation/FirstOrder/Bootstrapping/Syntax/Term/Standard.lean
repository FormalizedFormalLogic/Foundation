module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic
public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Functions
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

/-! ### `IsSemiterm`

The same mirror with the bound `n` threaded through as an ordinary parameter. It does not shift —
terms bind nothing — so the recursion is unchanged apart from the `^#z` branch, which now checks
`z < n`. `bv` never appears. -/

mutual

/-- Fuel-indexed executable mirror of `IsSemiterm` at `V := ℕ`. The bound `n` is an ordinary
parameter; it does not shift, since terms bind nothing. -/
def IsSemiterm.checkF (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] :
    ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | _ + 1, _, 0 => false
  | s + 1, n, e + 1 =>
    if natPi₁ e = 0 then decide (natPi₂ e < n)
    else if natPi₁ e = 1 then true
    else if natPi₁ e = 2 then
      isFuncB L (natPi₁ (natPi₂ e)) (natPi₁ (natPi₂ (natPi₂ e))) &&
        (natPi₁ (natPi₂ e) == natLen (natPi₂ (natPi₂ (natPi₂ e)))) &&
        IsSemiterm.checkVecF L s n (natPi₂ (natPi₂ (natPi₂ e)))
    else false

def IsSemiterm.checkVecF (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] :
    ℕ → ℕ → ℕ → Bool
  | 0, _, v => v == 0
  | _ + 1, _, 0 => true
  | s + 1, n, w + 1 =>
    IsSemiterm.checkF L s n (natPi₁ w) && IsSemiterm.checkVecF L s n (natPi₂ w)

end

def IsSemiterm.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (n t : ℕ) : Bool := IsSemiterm.checkF L t n t

def IsSemiterm.checkVec (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (n v : ℕ) : Bool := IsSemiterm.checkVecF L v n v

private lemma IsSemiterm.checkF_succ (s n e : ℕ) :
    IsSemiterm.checkF L (s + 1) n (e + 1) =
      (if (Nat.unpair e).1 = 0 then decide ((Nat.unpair e).2 < n)
      else if (Nat.unpair e).1 = 1 then true
      else if (Nat.unpair e).1 = 2 then
        isFuncB L (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1 &&
          ((Nat.unpair (Nat.unpair e).2).1 ==
            natLen (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2) &&
          IsSemiterm.checkVecF L s n (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
      else false) := by
  rw [IsSemiterm.checkF]; simp only [natPi₁, natPi₂, natUnpair_eq]

private lemma IsSemiterm.checkVecF_succ (s n w : ℕ) :
    IsSemiterm.checkVecF L (s + 1) n (w + 1) =
      (IsSemiterm.checkF L s n (Nat.unpair w).1 && IsSemiterm.checkVecF L s n (Nat.unpair w).2) := by
  rw [IsSemiterm.checkVecF]; simp only [natPi₁, natPi₂, natUnpair_eq]

omit [L.DecidableSymbols] in
/-- Tags of semiterm codes, once, for the negative branches. -/
private lemma IsSemiterm.tag_le {n e : ℕ} (h : IsSemiterm L n (e + 1)) : (Nat.unpair e).1 ≤ 2 := by
  rcases h.case with (⟨z, _, hv⟩ | ⟨x, hv⟩ | ⟨k, f, v, _, _, hv⟩)
  · rw [nat_qqBvar_eq] at hv
    obtain rfl : e = Nat.pair 0 z := by omega
    simp
  · rw [nat_qqFvar_eq] at hv
    obtain rfl : e = Nat.pair 1 x := by omega
    simp
  · rw [nat_qqFunc_eq] at hv
    obtain rfl : e = Nat.pair 2 (Nat.pair k (Nat.pair f v)) := by omega
    simp

private lemma IsSemiterm.checkF_iff_aux (s : ℕ) : ∀ n,
    (∀ t ≤ s, (IsSemiterm.checkF L s n t = true ↔ IsSemiterm L n t)) ∧
    (∀ v ≤ s, (IsSemiterm.checkVecF L s n v = true ↔ ∀ i < len v, IsSemiterm L n v.[i])) := by
  induction s with
  | zero =>
    intro n
    constructor
    · intro t ht
      obtain rfl : t = 0 := by omega
      simp only [IsSemiterm.checkF, Bool.false_eq_true, false_iff]
      intro hc
      rcases hc.case with (⟨z, _, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
      · rw [nat_qqBvar_eq] at hz; omega
      · rw [nat_qqFvar_eq] at hx; omega
      · rw [nat_qqFunc_eq] at hv; omega
    · intro v hv
      obtain rfl : v = 0 := by omega
      simp [IsSemiterm.checkVecF]
  | succ m ih =>
    intro n
    constructor
    · intro t ht
      match t with
      | 0 =>
        simp only [IsSemiterm.checkF, Bool.false_eq_true, false_iff]
        intro hc
        rcases hc.case with (⟨z, _, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
        · rw [nat_qqBvar_eq] at hz; omega
        · rw [nat_qqFvar_eq] at hx; omega
        · rw [nat_qqFunc_eq] at hv; omega
      | e + 1 =>
        have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
        rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
            3 ≤ (Nat.unpair e).1 by omega) with h | h | h | h
        · have hb : (e : ℕ) + 1 = ^#((Nat.unpair e).2) := by rw [nat_qqBvar_eq, ← h, he]
          rw [IsSemiterm.checkF_succ, if_pos h, hb]
          simp
        · have hf : (e : ℕ) + 1 = ^&((Nat.unpair e).2) := by rw [nat_qqFvar_eq, ← h, he]
          rw [IsSemiterm.checkF_succ, if_neg (by omega), if_pos h, hf]
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
          have hle : (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 ≤ m :=
            le_trans (le_trans (Nat.unpair_right_le _) <|
              le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
          rw [IsSemiterm.checkF_succ, if_neg (by omega), if_neg (by omega), if_pos h, hfn,
            IsSemiterm.func]
          simp only [Bool.and_eq_true, beq_iff_eq, isFuncB_iff, IsSemitermVec.iff,
            (ih n).2 _ hle, ← nat_len_eq]
          constructor
          · rintro ⟨⟨hF, hk⟩, hv⟩; exact ⟨hF, hk.symm, fun i hi ↦ hv i (hk ▸ hi)⟩
          · rintro ⟨hF, hk, hv⟩; exact ⟨⟨hF, hk.symm⟩, fun i hi ↦ hv i (hk ▸ hi)⟩
        · rw [IsSemiterm.checkF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp only [Bool.false_eq_true, false_iff]
          intro hc
          have := IsSemiterm.tag_le hc
          omega
    · intro v hv
      match v with
      | 0 => simp [IsSemiterm.checkVecF]
      | w + 1 =>
        have hadj : (w : ℕ) + 1 = (Nat.unpair w).1 ∷ (Nat.unpair w).2 := by
          rw [succ_eq_adjoin w, nat_pi₁_eq, nat_pi₂_eq]
        have h₁ : (Nat.unpair w).1 ≤ m := le_trans (Nat.unpair_left_le _) (by omega)
        have h₂ : (Nat.unpair w).2 ≤ m := le_trans (Nat.unpair_right_le _) (by omega)
        rw [IsSemiterm.checkVecF_succ]
        simp only [Bool.and_eq_true, (ih n).1 _ h₁, (ih n).2 _ h₂]
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

theorem IsSemiterm.check_iff {n t : ℕ} : IsSemiterm.check L n t = true ↔ IsSemiterm L n t :=
  (IsSemiterm.checkF_iff_aux t n).1 t le_rfl

theorem IsSemiterm.checkVec_iff {n v : ℕ} :
    IsSemiterm.checkVec L n v = true ↔ ∀ i < len v, IsSemiterm L n v.[i] :=
  (IsSemiterm.checkF_iff_aux v n).2 v le_rfl

instance decidableIsSemiterm (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (n t : ℕ) : Decidable (IsSemiterm (V := ℕ) L n t) := decidable_of_iff _ IsSemiterm.check_iff

/-! ### Function mirrors: `termShift` and `termSubst`

Pattern A at term level, following `neg` (`Formula/Standard.lean`): the mirror returns a code,
agreement is an equation, the induction carries `IsUTerm`/`IsUTermVec` and propagates it with the
`C1` constructor lemmas, and totality comes from `Language.TermRec.Construction.result_prop_not`
composed with the `C1` recogniser.

What is new here is the **vector companion**. `termShiftVec`/`termSubstVec` are mutually recursive
with the scalar, so the adequacy-indexed induction proves both at once — exactly as
`IsUTerm.checkF`/`checkVecF` do — and the vector half is stated over *well-formed* vectors,

    IsUTermVec L k v → termShiftVec.check L v = termShiftVec L k v

which is the shape `shift` and `subst` consume: they only ever apply it under the well-formedness
they have already established for the enclosing formula. There is no off-domain equation for the
vector companion upstream, and none is needed. -/

/-! ### `termShift` -/

mutual

def termShiftF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, e + 1 =>
    if natPi₁ e = 0 then Nat.pair 0 (natPi₂ e) + 1
    else if natPi₁ e = 1 then Nat.pair 1 (natPi₂ e + 1) + 1
    else if natPi₁ e = 2 then
      Nat.pair 2 (Nat.pair (natPi₁ (natPi₂ e))
        (Nat.pair (natPi₁ (natPi₂ (natPi₂ e)))
          (termShiftVecF s (natPi₂ (natPi₂ (natPi₂ e)))))) + 1
    else 0

def termShiftVecF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, w + 1 => Nat.pair (termShiftF s (natPi₁ w)) (termShiftVecF s (natPi₂ w)) + 1

end

def termShift.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (t : ℕ) : ℕ := if IsUTerm.check L t then termShiftF t t else 0

def termShiftVec.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (v : ℕ) : ℕ := termShiftVecF v v

private lemma termShiftF_succ (s e : ℕ) :
    termShiftF (s + 1) (e + 1) =
      (if (Nat.unpair e).1 = 0 then Nat.pair 0 (Nat.unpair e).2 + 1
      else if (Nat.unpair e).1 = 1 then Nat.pair 1 ((Nat.unpair e).2 + 1) + 1
      else if (Nat.unpair e).1 = 2 then
        Nat.pair 2 (Nat.pair (Nat.unpair (Nat.unpair e).2).1
          (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (termShiftVecF s (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2))) + 1
      else 0) := by
  rw [termShiftF]; simp only [natPi₁, natPi₂, natUnpair_eq]

private lemma termShiftVecF_succ (s w : ℕ) :
    termShiftVecF (s + 1) (w + 1) =
      Nat.pair (termShiftF s (Nat.unpair w).1) (termShiftVecF s (Nat.unpair w).2) + 1 := by
  rw [termShiftVecF]; simp only [natPi₁, natPi₂, natUnpair_eq]

omit [L.DecidableSymbols] in
private lemma termShiftF_eq_aux (s : ℕ) :
    (∀ t ≤ s, IsUTerm L t → termShiftF s t = termShift L t) ∧
    (∀ v ≤ s, ∀ k, IsUTermVec L k v → termShiftVecF s v = termShiftVec L k v) := by
  induction s with
  | zero =>
    constructor
    · intro t ht h
      obtain rfl : t = 0 := by omega
      rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
      · rw [nat_qqBvar_eq] at hz; omega
      · rw [nat_qqFvar_eq] at hx; omega
      · rw [nat_qqFunc_eq] at hv; omega
    · intro v hv k h
      obtain rfl : v = 0 := by omega
      obtain rfl : k = 0 := by simpa using h.lh
      simp [termShiftVecF]
  | succ m ih =>
    constructor
    · intro t ht h
      match t with
      | 0 =>
        rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
        · rw [nat_qqBvar_eq] at hz; omega
        · rw [nat_qqFvar_eq] at hx; omega
        · rw [nat_qqFunc_eq] at hv; omega
      | e + 1 =>
        have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
        have e2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
            = (Nat.unpair e).2 := Nat.pair_unpair _
        have e3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
            = (Nat.unpair (Nat.unpair e).2).2 := Nat.pair_unpair _
        have hle : (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 ≤ m :=
          le_trans (le_trans (Nat.unpair_right_le _) <|
            le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
        rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
            3 ≤ (Nat.unpair e).1 by omega) with h' | h' | h' | h'
        · have hs : (e : ℕ) + 1 = ^#((Nat.unpair e).2) := by rw [nat_qqBvar_eq, ← h', he]
          rw [termShiftF_succ, if_pos h', hs, termShift_bvar, nat_qqBvar_eq]
        · have hs : (e : ℕ) + 1 = ^&((Nat.unpair e).2) := by rw [nat_qqFvar_eq, ← h', he]
          rw [termShiftF_succ, if_neg (by omega), if_pos h', hs, termShift_fvar, nat_qqFvar_eq]
        · have hs : (e : ℕ) + 1 =
              ^func (Nat.unpair (Nat.unpair e).2).1
                (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
                (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
            rw [nat_qqFunc_eq, e3, e2, ← h', he]
          rw [hs] at h
          obtain ⟨hkf, hv⟩ := IsUTerm.func_iff.mp h
          rw [termShiftF_succ, if_neg (by omega), if_neg (by omega), if_pos h', hs,
            termShift_func hkf hv, nat_qqFunc_eq, ih.2 _ hle _ hv]
        · rw [termShiftF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exfalso
          rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
          · rw [nat_qqBvar_eq] at hz
            obtain rfl : e = Nat.pair 0 z := by omega
            simp at h'
          · rw [nat_qqFvar_eq] at hx
            obtain rfl : e = Nat.pair 1 x := by omega
            simp at h'
          · rw [nat_qqFunc_eq] at hv
            obtain rfl : e = Nat.pair 2 (Nat.pair k (Nat.pair f v)) := by omega
            simp at h'
    · intro v hv k h
      match v with
      | 0 =>
        obtain rfl : k = 0 := by simpa using h.lh
        simp [termShiftVecF]
      | w + 1 =>
        have hadj : (w : ℕ) + 1 = (Nat.unpair w).1 ∷ (Nat.unpair w).2 := by
          rw [succ_eq_adjoin w, nat_pi₁_eq, nat_pi₂_eq]
        have h₁ : (Nat.unpair w).1 ≤ m := le_trans (Nat.unpair_left_le _) (by omega)
        have h₂ : (Nat.unpair w).2 ≤ m := le_trans (Nat.unpair_right_le _) (by omega)
        rw [hadj] at h
        obtain ⟨hk, hrest⟩ : k = len (Nat.unpair w).2 + 1 ∧ True := by
          refine ⟨?_, trivial⟩
          have := h.lh
          simpa [hadj, len_adjoin] using this
        subst hk
        have ht : IsUTerm L (Nat.unpair w).1 := by
          simpa using h.nth (i := 0) (by simp)
        have hts : IsUTermVec L (len (Nat.unpair w).2) (Nat.unpair w).2 :=
          ⟨rfl, fun i hi ↦ by simpa using h.nth (i := i + 1) (by simpa using hi)⟩
        rw [termShiftVecF_succ, hadj, termShiftVec_cons ht hts, ih.1 _ h₁ ht, ih.2 _ h₂ _ hts,
          adjoin_def, nat_pair_eq]

theorem termShiftVec.check_eq {k v : ℕ} (h : IsUTermVec L k v) :
    termShiftVec.check L v = termShiftVec L k v :=
  (termShiftF_eq_aux v).2 v le_rfl k h

theorem termShift.check_eq (t : ℕ) : termShift.check L t = termShift L t := by
  rw [termShift.check]
  by_cases h : IsUTerm.check L t = true
  · rw [if_pos h]
    exact (termShiftF_eq_aux t).1 t le_rfl (IsUTerm.check_iff.mp h)
  · rw [if_neg h]
    exact (TermShift.construction.result_prop_not (L := L) (param := ![])
      (fun hc ↦ h (IsUTerm.check_iff.mpr hc))).symm


/-! ### `termSubst` -/

mutual

def termSubstF (w : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, e + 1 =>
    if natPi₁ e = 0 then natNth w (natPi₂ e)
    else if natPi₁ e = 1 then Nat.pair 1 (natPi₂ e) + 1
    else if natPi₁ e = 2 then
      Nat.pair 2 (Nat.pair (natPi₁ (natPi₂ e))
        (Nat.pair (natPi₁ (natPi₂ (natPi₂ e)))
          (termSubstVecF w s (natPi₂ (natPi₂ (natPi₂ e)))))) + 1
    else 0

def termSubstVecF (w : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, u + 1 => Nat.pair (termSubstF w s (natPi₁ u)) (termSubstVecF w s (natPi₂ u)) + 1

end

def termSubst.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (w t : ℕ) : ℕ := if IsUTerm.check L t then termSubstF w t t else 0

def termSubstVec.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (w v : ℕ) : ℕ := termSubstVecF w v v

private lemma termSubstF_succ (w s e : ℕ) :
    termSubstF w (s + 1) (e + 1) =
      (if (Nat.unpair e).1 = 0 then natNth w (Nat.unpair e).2
      else if (Nat.unpair e).1 = 1 then Nat.pair 1 (Nat.unpair e).2 + 1
      else if (Nat.unpair e).1 = 2 then
        Nat.pair 2 (Nat.pair (Nat.unpair (Nat.unpair e).2).1
          (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (termSubstVecF w s (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2))) + 1
      else 0) := by
  rw [termSubstF]; simp only [natPi₁, natPi₂, natUnpair_eq]

private lemma termSubstVecF_succ (w s u : ℕ) :
    termSubstVecF w (s + 1) (u + 1) =
      Nat.pair (termSubstF w s (Nat.unpair u).1) (termSubstVecF w s (Nat.unpair u).2) + 1 := by
  rw [termSubstVecF]; simp only [natPi₁, natPi₂, natUnpair_eq]

omit [L.DecidableSymbols] in
private lemma termSubstF_eq_aux (w : ℕ) (s : ℕ) :
    (∀ t ≤ s, IsUTerm L t → termSubstF w s t = termSubst L w t) ∧
    (∀ v ≤ s, ∀ k, IsUTermVec L k v → termSubstVecF w s v = termSubstVec L k w v) := by
  induction s with
  | zero =>
    constructor
    · intro t ht h
      obtain rfl : t = 0 := by omega
      rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
      · rw [nat_qqBvar_eq] at hz; omega
      · rw [nat_qqFvar_eq] at hx; omega
      · rw [nat_qqFunc_eq] at hv; omega
    · intro v hv k h
      obtain rfl : v = 0 := by omega
      obtain rfl : k = 0 := by simpa using h.lh
      simp [termSubstVecF]
  | succ m ih =>
    constructor
    · intro t ht h
      match t with
      | 0 =>
        rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
        · rw [nat_qqBvar_eq] at hz; omega
        · rw [nat_qqFvar_eq] at hx; omega
        · rw [nat_qqFunc_eq] at hv; omega
      | e + 1 =>
        have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
        have e2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
            = (Nat.unpair e).2 := Nat.pair_unpair _
        have e3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
            = (Nat.unpair (Nat.unpair e).2).2 := Nat.pair_unpair _
        have hle : (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 ≤ m :=
          le_trans (le_trans (Nat.unpair_right_le _) <|
            le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
        rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
            3 ≤ (Nat.unpair e).1 by omega) with h' | h' | h' | h'
        · have hs : (e : ℕ) + 1 = ^#((Nat.unpair e).2) := by rw [nat_qqBvar_eq, ← h', he]
          rw [termSubstF_succ, if_pos h', hs, termSubst_bvar, nat_nth_eq]
        · have hs : (e : ℕ) + 1 = ^&((Nat.unpair e).2) := by rw [nat_qqFvar_eq, ← h', he]
          rw [termSubstF_succ, if_neg (by omega), if_pos h', hs, termSubst_fvar, nat_qqFvar_eq]
        · have hs : (e : ℕ) + 1 =
              ^func (Nat.unpair (Nat.unpair e).2).1
                (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
                (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
            rw [nat_qqFunc_eq, e3, e2, ← h', he]
          rw [hs] at h
          obtain ⟨hkf, hv⟩ := IsUTerm.func_iff.mp h
          rw [termSubstF_succ, if_neg (by omega), if_neg (by omega), if_pos h', hs,
            termSubst_func hkf hv, nat_qqFunc_eq, ih.2 _ hle _ hv]
        · rw [termSubstF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exfalso
          rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
          · rw [nat_qqBvar_eq] at hz
            obtain rfl : e = Nat.pair 0 z := by omega
            simp at h'
          · rw [nat_qqFvar_eq] at hx
            obtain rfl : e = Nat.pair 1 x := by omega
            simp at h'
          · rw [nat_qqFunc_eq] at hv
            obtain rfl : e = Nat.pair 2 (Nat.pair k (Nat.pair f v)) := by omega
            simp at h'
    · intro v hv k h
      match v with
      | 0 =>
        obtain rfl : k = 0 := by simpa using h.lh
        simp [termSubstVecF]
      | u + 1 =>
        have hadj : (u : ℕ) + 1 = (Nat.unpair u).1 ∷ (Nat.unpair u).2 := by
          rw [succ_eq_adjoin u, nat_pi₁_eq, nat_pi₂_eq]
        have h₁ : (Nat.unpair u).1 ≤ m := le_trans (Nat.unpair_left_le _) (by omega)
        have h₂ : (Nat.unpair u).2 ≤ m := le_trans (Nat.unpair_right_le _) (by omega)
        rw [hadj] at h
        obtain rfl : k = len (Nat.unpair u).2 + 1 := by
          have := h.lh; simpa [len_adjoin] using this
        have ht : IsUTerm L (Nat.unpair u).1 := by simpa using h.nth (i := 0) (by simp)
        have hts : IsUTermVec L (len (Nat.unpair u).2) (Nat.unpair u).2 :=
          ⟨rfl, fun i hi ↦ by simpa using h.nth (i := i + 1) (by simpa using hi)⟩
        rw [termSubstVecF_succ, hadj, termSubstVec_cons ht hts, ih.1 _ h₁ ht, ih.2 _ h₂ _ hts,
          adjoin_def, nat_pair_eq]

theorem termSubstVec.check_eq {k w v : ℕ} (h : IsUTermVec L k v) :
    termSubstVec.check L w v = termSubstVec L k w v :=
  (termSubstF_eq_aux w v).2 v le_rfl k h

theorem termSubst.check_eq (w t : ℕ) : termSubst.check L w t = termSubst L w t := by
  rw [termSubst.check]
  by_cases h : IsUTerm.check L t = true
  · rw [if_pos h]
    exact (termSubstF_eq_aux w t).1 t le_rfl (IsUTerm.check_iff.mp h)
  · rw [if_neg h]
    exact (TermSubst.construction.result_prop_not (L := L) (param := ![w])
      (fun hc ↦ h (IsUTerm.check_iff.mpr hc))).symm

/-! ### Function mirrors: `termBShift` and `qVec`

`termBShift` is the `termShift` template again — third instance — differing only in the leaves
(`^#z ↦ ^#(z+1)`, `^&x ↦ ^&x`). `qVec w = ^#0 ∷ termBShiftVec L (len w) w` is a composite on top of
it, and is what `subst` shifts its parameter by under `^∀`/`^∃`.

Note the hypothesis on `qVec.check_eq`: it needs the vector `w` to be *well-formed*, because
`termBShiftVec.check` only agrees there. A consumer that changes its parameter by `qVec` must
therefore carry the parameter's well-formedness as an invariant of its own recursion. -/

mutual

def termBShiftF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, e + 1 =>
    if natPi₁ e = 0 then Nat.pair 0 (natPi₂ e + 1) + 1
    else if natPi₁ e = 1 then Nat.pair 1 (natPi₂ e) + 1
    else if natPi₁ e = 2 then
      Nat.pair 2 (Nat.pair (natPi₁ (natPi₂ e))
        (Nat.pair (natPi₁ (natPi₂ (natPi₂ e)))
          (termBShiftVecF s (natPi₂ (natPi₂ (natPi₂ e)))))) + 1
    else 0

def termBShiftVecF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, w + 1 => Nat.pair (termBShiftF s (natPi₁ w)) (termBShiftVecF s (natPi₂ w)) + 1

end

def termBShift.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (t : ℕ) : ℕ := if IsUTerm.check L t then termBShiftF t t else 0

def termBShiftVec.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (v : ℕ) : ℕ := termBShiftVecF v v

private lemma termBShiftF_succ (s e : ℕ) :
    termBShiftF (s + 1) (e + 1) =
      (if (Nat.unpair e).1 = 0 then Nat.pair 0 ((Nat.unpair e).2 + 1) + 1
      else if (Nat.unpair e).1 = 1 then Nat.pair 1 (Nat.unpair e).2 + 1
      else if (Nat.unpair e).1 = 2 then
        Nat.pair 2 (Nat.pair (Nat.unpair (Nat.unpair e).2).1
          (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (termBShiftVecF s (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2))) + 1
      else 0) := by
  rw [termBShiftF]; simp only [natPi₁, natPi₂, natUnpair_eq]

private lemma termBShiftVecF_succ (s w : ℕ) :
    termBShiftVecF (s + 1) (w + 1) =
      Nat.pair (termBShiftF s (Nat.unpair w).1) (termBShiftVecF s (Nat.unpair w).2) + 1 := by
  rw [termBShiftVecF]; simp only [natPi₁, natPi₂, natUnpair_eq]

omit [L.DecidableSymbols] in
private lemma termBShiftF_eq_aux (s : ℕ) :
    (∀ t ≤ s, IsUTerm L t → termBShiftF s t = termBShift L t) ∧
    (∀ v ≤ s, ∀ k, IsUTermVec L k v → termBShiftVecF s v = termBShiftVec L k v) := by
  induction s with
  | zero =>
    constructor
    · intro t ht h
      obtain rfl : t = 0 := by omega
      rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
      · rw [nat_qqBvar_eq] at hz; omega
      · rw [nat_qqFvar_eq] at hx; omega
      · rw [nat_qqFunc_eq] at hv; omega
    · intro v hv k h
      obtain rfl : v = 0 := by omega
      obtain rfl : k = 0 := by simpa using h.lh
      simp [termBShiftVecF]
  | succ m ih =>
    constructor
    · intro t ht h
      match t with
      | 0 =>
        rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
        · rw [nat_qqBvar_eq] at hz; omega
        · rw [nat_qqFvar_eq] at hx; omega
        · rw [nat_qqFunc_eq] at hv; omega
      | e + 1 =>
        have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
        have e2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
            = (Nat.unpair e).2 := Nat.pair_unpair _
        have e3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
            = (Nat.unpair (Nat.unpair e).2).2 := Nat.pair_unpair _
        have hle : (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 ≤ m :=
          le_trans (le_trans (Nat.unpair_right_le _) <|
            le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
        rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
            3 ≤ (Nat.unpair e).1 by omega) with h' | h' | h' | h'
        · have hs : (e : ℕ) + 1 = ^#((Nat.unpair e).2) := by rw [nat_qqBvar_eq, ← h', he]
          rw [termBShiftF_succ, if_pos h', hs, termBShift_bvar, nat_qqBvar_eq]
        · have hs : (e : ℕ) + 1 = ^&((Nat.unpair e).2) := by rw [nat_qqFvar_eq, ← h', he]
          rw [termBShiftF_succ, if_neg (by omega), if_pos h', hs, termBShift_fvar, nat_qqFvar_eq]
        · have hs : (e : ℕ) + 1 =
              ^func (Nat.unpair (Nat.unpair e).2).1
                (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
                (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
            rw [nat_qqFunc_eq, e3, e2, ← h', he]
          rw [hs] at h
          obtain ⟨hkf, hv⟩ := IsUTerm.func_iff.mp h
          rw [termBShiftF_succ, if_neg (by omega), if_neg (by omega), if_pos h', hs,
            termBShift_func hkf hv, nat_qqFunc_eq, ih.2 _ hle _ hv]
        · rw [termBShiftF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exfalso
          rcases h.case with (⟨z, hz⟩ | ⟨x, hx⟩ | ⟨k, f, v, _, _, hv⟩)
          · rw [nat_qqBvar_eq] at hz
            obtain rfl : e = Nat.pair 0 z := by omega
            simp at h'
          · rw [nat_qqFvar_eq] at hx
            obtain rfl : e = Nat.pair 1 x := by omega
            simp at h'
          · rw [nat_qqFunc_eq] at hv
            obtain rfl : e = Nat.pair 2 (Nat.pair k (Nat.pair f v)) := by omega
            simp at h'
    · intro v hv k h
      match v with
      | 0 =>
        obtain rfl : k = 0 := by simpa using h.lh
        simp [termBShiftVecF]
      | w + 1 =>
        have hadj : (w : ℕ) + 1 = (Nat.unpair w).1 ∷ (Nat.unpair w).2 := by
          rw [succ_eq_adjoin w, nat_pi₁_eq, nat_pi₂_eq]
        have h₁ : (Nat.unpair w).1 ≤ m := le_trans (Nat.unpair_left_le _) (by omega)
        have h₂ : (Nat.unpair w).2 ≤ m := le_trans (Nat.unpair_right_le _) (by omega)
        rw [hadj] at h
        obtain ⟨hk, hrest⟩ : k = len (Nat.unpair w).2 + 1 ∧ True := by
          refine ⟨?_, trivial⟩
          have := h.lh
          simpa [hadj, len_adjoin] using this
        subst hk
        have ht : IsUTerm L (Nat.unpair w).1 := by
          simpa using h.nth (i := 0) (by simp)
        have hts : IsUTermVec L (len (Nat.unpair w).2) (Nat.unpair w).2 :=
          ⟨rfl, fun i hi ↦ by simpa using h.nth (i := i + 1) (by simpa using hi)⟩
        rw [termBShiftVecF_succ, hadj, termBShiftVec_cons ht hts, ih.1 _ h₁ ht, ih.2 _ h₂ _ hts,
          adjoin_def, nat_pair_eq]

theorem termBShiftVec.check_eq {k v : ℕ} (h : IsUTermVec L k v) :
    termBShiftVec.check L v = termBShiftVec L k v :=
  (termBShiftF_eq_aux v).2 v le_rfl k h

theorem termBShift.check_eq (t : ℕ) : termBShift.check L t = termBShift L t := by
  rw [termBShift.check]
  by_cases h : IsUTerm.check L t = true
  · rw [if_pos h]
    exact (termBShiftF_eq_aux t).1 t le_rfl (IsUTerm.check_iff.mp h)
  · rw [if_neg h]
    exact (TermBShift.construction.result_prop_not (L := L) (param := ![])
      (fun hc ↦ h (IsUTerm.check_iff.mpr hc))).symm



/-! ### `qVec` -/

def qVec.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] (w : ℕ) : ℕ :=
  Nat.pair 1 (termBShiftVec.check L w) + 1

theorem qVec.check_eq {w : ℕ} (h : IsUTermVec L (len w) w) : qVec.check L w = qVec L w := by
  rw [qVec.check, qVec, termBShiftVec.check_eq h, adjoin_def, nat_pair_eq]
  congr 1
  rw [nat_qqBvar_eq]
  simp [Nat.pair]

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

/-- `1 = ^#0` is a term at `n = 1` but not at `n = 0`. -/
example : IsSemiterm (V := ℕ) ℒₒᵣ 1 1 := IsSemiterm.check_iff.mp (by decide)

example : ¬IsSemiterm (V := ℕ) ℒₒᵣ 0 1 :=
  fun h ↦ absurd (IsSemiterm.check_iff.mpr h) (by decide)

/-- `3 = ^&0`, and shifting gives `4 = ^&1`. -/
example : termShift (V := ℕ) ℒₒᵣ 3 = 4 := by rw [← termShift.check_eq]; decide

example : termShift (V := ℕ) ℒₒᵣ 0 = 0 := by rw [← termShift.check_eq]; decide

/-- Substituting `?[^&0]` into `^#0` yields `^&0`. -/
example : termSubst (V := ℕ) ℒₒᵣ 13 1 = 3 := by rw [← termSubst.check_eq]; decide

/-- `1 = ^#0`, and bound-shifting gives `2 = ^#1`. -/
example : termBShift (V := ℕ) ℒₒᵣ 1 = 2 := by rw [← termBShift.check_eq]; decide

example : termBShift (V := ℕ) ℒₒᵣ 0 = 0 := by rw [← termBShift.check_eq]; decide

end LO.FirstOrder.Arithmetic.Bootstrapping

end
