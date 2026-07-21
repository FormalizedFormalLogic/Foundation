module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Standard
public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic
public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Functions

@[expose] public section
/-!
# Executable formula-code recognition in the standard model

The term mirror (`Syntax/Term/Standard.lean`), scaled up. `IsUFormula` is a `Fixpoint` with eight
constructors instead of three; the mirror is fuel-indexed, destructures with `natPi₁`/`natPi₂`, and
agreement is proved by the same adequacy-indexed induction against `IsUFormula.case_iff`.

Two things differ from the term case:

* the `^rel`/`^nrel` branches consume the *term* mirror rather than recursing — `IsUTerm.checkVec`
  is a separate recursion, already proved, so `isUTermVec_iff_check` is all that is needed;
* the negative direction is factored. Six of the nine branches would otherwise each repeat the
  eight-way `case_iff` enumeration, so `IsUFormula.tag_spec` does it once: a code that is a formula
  has tag `≤ 7`, and tags `2`/`3` (`^⊤`/`^⊥`) force the payload to be `0`. The branches then need
  only `omega`.
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

/-! ### The formula constructors at `V := ℕ` -/

lemma nat_qqRel_eq (k r v : ℕ) :
    (^rel k r v : ℕ) = Nat.pair 0 (Nat.pair k (Nat.pair r v)) + 1 := by
  simp [qqRel, nat_pair_eq]

lemma nat_qqNRel_eq (k r v : ℕ) :
    (^nrel k r v : ℕ) = Nat.pair 1 (Nat.pair k (Nat.pair r v)) + 1 := by
  simp [qqNRel, nat_pair_eq]

lemma nat_qqVerum_eq : (^⊤ : ℕ) = Nat.pair 2 0 + 1 := by simp [qqVerum, nat_pair_eq]

lemma nat_qqFalsum_eq : (^⊥ : ℕ) = Nat.pair 3 0 + 1 := by simp [qqFalsum, nat_pair_eq]

lemma nat_qqAnd_eq (p q : ℕ) : (p ^⋏ q : ℕ) = Nat.pair 4 (Nat.pair p q) + 1 := by
  simp [qqAnd, nat_pair_eq]

lemma nat_qqOr_eq (p q : ℕ) : (p ^⋎ q : ℕ) = Nat.pair 5 (Nat.pair p q) + 1 := by
  simp [qqOr, nat_pair_eq]

lemma nat_qqAll_eq (p : ℕ) : (^∀ p : ℕ) = Nat.pair 6 p + 1 := by simp [qqAll, nat_pair_eq]

lemma nat_qqExs_eq (p : ℕ) : (^∃ p : ℕ) = Nat.pair 7 p + 1 := by simp [qqExs, nat_pair_eq]

/-! ### The mirror -/

/-- Fuel-indexed executable mirror of `IsUFormula` at `V := ℕ`. -/
def IsUFormula.checkF (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] :
    ℕ → ℕ → Bool
  | 0, _ => false
  | _ + 1, 0 => false
  | s + 1, e + 1 =>
    if natPi₁ e = 0 ∨ natPi₁ e = 1 then
      isRelB L (natPi₁ (natPi₂ e)) (natPi₁ (natPi₂ (natPi₂ e))) &&
        (natPi₁ (natPi₂ e) == natLen (natPi₂ (natPi₂ (natPi₂ e)))) &&
        IsUTerm.checkVec L (natPi₂ (natPi₂ (natPi₂ e)))
    else if natPi₁ e = 2 ∨ natPi₁ e = 3 then natPi₂ e == 0
    else if natPi₁ e = 4 ∨ natPi₁ e = 5 then
      IsUFormula.checkF L s (natPi₁ (natPi₂ e)) && IsUFormula.checkF L s (natPi₂ (natPi₂ e))
    else if natPi₁ e = 6 ∨ natPi₁ e = 7 then IsUFormula.checkF L s (natPi₂ e)
    else false

def IsUFormula.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (p : ℕ) : Bool := IsUFormula.checkF L p p

/-! ### Agreement -/

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]

private lemma IsUFormula.checkF_succ (s e : ℕ) :
    IsUFormula.checkF L (s + 1) (e + 1) =
      (if (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 then
        isRelB L (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1 &&
          ((Nat.unpair (Nat.unpair e).2).1 ==
            natLen (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2) &&
          IsUTerm.checkVec L (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
      else if (Nat.unpair e).1 = 2 ∨ (Nat.unpair e).1 = 3 then (Nat.unpair e).2 == 0
      else if (Nat.unpair e).1 = 4 ∨ (Nat.unpair e).1 = 5 then
        IsUFormula.checkF L s (Nat.unpair (Nat.unpair e).2).1 &&
          IsUFormula.checkF L s (Nat.unpair (Nat.unpair e).2).2
      else if (Nat.unpair e).1 = 6 ∨ (Nat.unpair e).1 = 7 then
        IsUFormula.checkF L s (Nat.unpair e).2
      else false) := by
  rw [IsUFormula.checkF]; simp only [natPi₁, natPi₂, natUnpair_eq]

/-- The vector side condition, in the shape `IsUFormula.rel`/`nrel` want. -/
private lemma isUTermVec_iff_check (k v : ℕ) :
    (k = natLen v ∧ IsUTerm.checkVec L v = true) ↔ IsUTermVec L k v := by
  rw [IsUTerm.checkVec_iff, IsUTermVec, ← nat_len_eq]
  constructor
  · rintro ⟨hk, hv⟩; exact ⟨hk, fun i hi ↦ hv i (hk ▸ hi)⟩
  · rintro ⟨hk, hv⟩; exact ⟨hk, fun i hi ↦ hv i (hk ▸ hi)⟩

omit [L.DecidableSymbols] in
/-- Read the constructor tag off a code that is a formula. Proved once, by the eight-way
`case_iff` enumeration, so that the negative branches below need only `omega`. The `IsSemiformula`
mirror reuses it through `IsSemiformula.isUFormula`. -/
private lemma IsUFormula.tag_spec {e : ℕ} (h : IsUFormula L (e + 1)) :
    (Nat.unpair e).1 ≤ 7 ∧ ((Nat.unpair e).1 = 2 ∨ (Nat.unpair e).1 = 3 → (Nat.unpair e).2 = 0) := by
  rcases h.case with (⟨k, r, v, _, _, hv⟩ | ⟨k, r, v, _, _, hv⟩ | hv | hv |
    ⟨p₁, p₂, _, _, hv⟩ | ⟨p₁, p₂, _, _, hv⟩ | ⟨p₁, _, hv⟩ | ⟨p₁, _, hv⟩)
  · rw [nat_qqRel_eq] at hv
    obtain rfl : e = Nat.pair 0 (Nat.pair k (Nat.pair r v)) := by omega
    simp
  · rw [nat_qqNRel_eq] at hv
    obtain rfl : e = Nat.pair 1 (Nat.pair k (Nat.pair r v)) := by omega
    simp
  · rw [nat_qqVerum_eq] at hv
    obtain rfl : e = Nat.pair 2 0 := by omega
    simp
  · rw [nat_qqFalsum_eq] at hv
    obtain rfl : e = Nat.pair 3 0 := by omega
    simp
  · rw [nat_qqAnd_eq] at hv
    obtain rfl : e = Nat.pair 4 (Nat.pair p₁ p₂) := by omega
    simp
  · rw [nat_qqOr_eq] at hv
    obtain rfl : e = Nat.pair 5 (Nat.pair p₁ p₂) := by omega
    simp
  · rw [nat_qqAll_eq] at hv
    obtain rfl : e = Nat.pair 6 p₁ := by omega
    simp
  · rw [nat_qqExs_eq] at hv
    obtain rfl : e = Nat.pair 7 p₁ := by omega
    simp

private lemma IsUFormula.checkF_iff_aux (s : ℕ) :
    ∀ p ≤ s, (IsUFormula.checkF L s p = true ↔ IsUFormula L p) := by
  induction s with
  | zero =>
    intro p hp
    obtain rfl : p = 0 := by omega
    simp [IsUFormula.checkF]
  | succ n ih =>
    intro p hp
    match p with
    | 0 => simp [IsUFormula.checkF]
    | e + 1 =>
      have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
      have e2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
          = (Nat.unpair e).2 := Nat.pair_unpair _
      have e3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
          = (Nat.unpair (Nat.unpair e).2).2 := Nat.pair_unpair _
      have hl₁ : (Nat.unpair (Nat.unpair e).2).1 ≤ n :=
        le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) (by omega)
      have hl₂ : (Nat.unpair (Nat.unpair e).2).2 ≤ n :=
        le_trans (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
      have hl₃ : (Nat.unpair e).2 ≤ n := le_trans (Nat.unpair_right_le _) (by omega)
      rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
          (Nat.unpair e).1 = 3 ∨ (Nat.unpair e).1 = 4 ∨ (Nat.unpair e).1 = 5 ∨
          (Nat.unpair e).1 = 6 ∨ (Nat.unpair e).1 = 7 ∨ 8 ≤ (Nat.unpair e).1 by omega)
        with h | h | h | h | h | h | h | h | h
      · have hs : (e : ℕ) + 1 = ^rel (Nat.unpair (Nat.unpair e).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_qqRel_eq, e3, e2, ← h, he]
        rw [IsUFormula.checkF_succ, if_pos (Or.inl h), hs, IsUFormula.rel]
        simp only [Bool.and_eq_true, beq_iff_eq, isRelB_iff]
        rw [and_assoc, isUTermVec_iff_check]
      · have hs : (e : ℕ) + 1 = ^nrel (Nat.unpair (Nat.unpair e).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_qqNRel_eq, e3, e2, ← h, he]
        rw [IsUFormula.checkF_succ, if_pos (Or.inr h), hs, IsUFormula.nrel]
        simp only [Bool.and_eq_true, beq_iff_eq, isRelB_iff]
        rw [and_assoc, isUTermVec_iff_check]
      · rw [IsUFormula.checkF_succ, if_neg (by omega), if_pos (Or.inl h)]
        simp only [beq_iff_eq]
        constructor
        · intro hz
          have hv : (e : ℕ) + 1 = ^⊤ := by rw [nat_qqVerum_eq, ← h, ← hz, he]
          rw [hv]; simp
        · intro hc; exact (IsUFormula.tag_spec hc).2 (Or.inl h)
      · rw [IsUFormula.checkF_succ, if_neg (by omega), if_pos (Or.inr h)]
        simp only [beq_iff_eq]
        constructor
        · intro hz
          have hv : (e : ℕ) + 1 = ^⊥ := by rw [nat_qqFalsum_eq, ← h, ← hz, he]
          rw [hv]; simp
        · intro hc; exact (IsUFormula.tag_spec hc).2 (Or.inr h)
      · have hs : (e : ℕ) + 1 =
            (Nat.unpair (Nat.unpair e).2).1 ^⋏ (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_qqAnd_eq, e2, ← h, he]
        rw [IsUFormula.checkF_succ, if_neg (by omega), if_neg (by omega), if_pos (Or.inl h), hs,
          IsUFormula.and]
        simp only [Bool.and_eq_true, ih _ hl₁, ih _ hl₂]
      · have hs : (e : ℕ) + 1 =
            (Nat.unpair (Nat.unpair e).2).1 ^⋎ (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_qqOr_eq, e2, ← h, he]
        rw [IsUFormula.checkF_succ, if_neg (by omega), if_neg (by omega), if_pos (Or.inr h), hs,
          IsUFormula.or]
        simp only [Bool.and_eq_true, ih _ hl₁, ih _ hl₂]
      · have hs : (e : ℕ) + 1 = ^∀ (Nat.unpair e).2 := by rw [nat_qqAll_eq, ← h, he]
        rw [IsUFormula.checkF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (Or.inl h), hs, IsUFormula.all]
        exact ih _ hl₃
      · have hs : (e : ℕ) + 1 = ^∃ (Nat.unpair e).2 := by rw [nat_qqExs_eq, ← h, he]
        rw [IsUFormula.checkF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (Or.inr h), hs, IsUFormula.ex]
        exact ih _ hl₃
      · rw [IsUFormula.checkF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
        simp only [Bool.false_eq_true, false_iff]
        intro hc
        have := (IsUFormula.tag_spec hc).1
        omega

theorem IsUFormula.check_iff {p : ℕ} : IsUFormula.check L p = true ↔ IsUFormula L p :=
  IsUFormula.checkF_iff_aux p p le_rfl

instance decidableIsUFormula (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (p : ℕ) : Decidable (IsUFormula (V := ℕ) L p) := decidable_of_iff _ IsUFormula.check_iff

/-! ### `IsSemiformula` -/

/-- Fuel-indexed executable mirror of `IsSemiformula` at `V := ℕ`. The bound `n` is an ordinary
parameter, shifting to `n + 1` under `^∀`/`^∃`. `bv` never appears. -/
def IsSemiformula.checkF (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] :
    ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | _ + 1, _, 0 => false
  | s + 1, n, e + 1 =>
    if natPi₁ e = 0 ∨ natPi₁ e = 1 then
      isRelB L (natPi₁ (natPi₂ e)) (natPi₁ (natPi₂ (natPi₂ e))) &&
        (natPi₁ (natPi₂ e) == natLen (natPi₂ (natPi₂ (natPi₂ e)))) &&
        IsSemiterm.checkVec L n (natPi₂ (natPi₂ (natPi₂ e)))
    else if natPi₁ e = 2 ∨ natPi₁ e = 3 then natPi₂ e == 0
    else if natPi₁ e = 4 ∨ natPi₁ e = 5 then
      IsSemiformula.checkF L s n (natPi₁ (natPi₂ e)) &&
        IsSemiformula.checkF L s n (natPi₂ (natPi₂ e))
    else if natPi₁ e = 6 ∨ natPi₁ e = 7 then IsSemiformula.checkF L s (n + 1) (natPi₂ e)
    else false

def IsSemiformula.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (n p : ℕ) : Bool := IsSemiformula.checkF L p n p

private lemma IsSemiformula.checkF_succ (s n e : ℕ) :
    IsSemiformula.checkF L (s + 1) n (e + 1) =
      (if (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 then
        isRelB L (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1 &&
          ((Nat.unpair (Nat.unpair e).2).1 ==
            natLen (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2) &&
          IsSemiterm.checkVec L n (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
      else if (Nat.unpair e).1 = 2 ∨ (Nat.unpair e).1 = 3 then (Nat.unpair e).2 == 0
      else if (Nat.unpair e).1 = 4 ∨ (Nat.unpair e).1 = 5 then
        IsSemiformula.checkF L s n (Nat.unpair (Nat.unpair e).2).1 &&
          IsSemiformula.checkF L s n (Nat.unpair (Nat.unpair e).2).2
      else if (Nat.unpair e).1 = 6 ∨ (Nat.unpair e).1 = 7 then
        IsSemiformula.checkF L s (n + 1) (Nat.unpair e).2
      else false) := by
  rw [IsSemiformula.checkF]; simp only [natPi₁, natPi₂, natUnpair_eq]

private lemma isSemitermVec_iff_check (k n v : ℕ) :
    (k = natLen v ∧ IsSemiterm.checkVec L n v = true) ↔ IsSemitermVec L k n v := by
  rw [IsSemiterm.checkVec_iff, IsSemitermVec.iff, ← nat_len_eq]
  constructor
  · rintro ⟨hk, hv⟩; exact ⟨hk.symm, fun i hi ↦ hv i (hk ▸ hi)⟩
  · rintro ⟨hk, hv⟩; exact ⟨hk.symm, fun i hi ↦ hv i (hk.symm ▸ hi)⟩

private lemma IsSemiformula.checkF_iff_aux (s : ℕ) :
    ∀ n, ∀ p ≤ s, (IsSemiformula.checkF L s n p = true ↔ IsSemiformula L n p) := by
  induction s with
  | zero =>
    intro n p hp
    obtain rfl : p = 0 := by omega
    simp only [IsSemiformula.checkF, Bool.false_eq_true, false_iff]
    intro hc; simpa using hc.isUFormula
  | succ m ih =>
    intro n p hp
    match p with
    | 0 =>
      simp only [IsSemiformula.checkF, Bool.false_eq_true, false_iff]
      intro hc; simpa using hc.isUFormula
    | e + 1 =>
      have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
      have e2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
          = (Nat.unpair e).2 := Nat.pair_unpair _
      have e3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
          = (Nat.unpair (Nat.unpair e).2).2 := Nat.pair_unpair _
      have hl₁ : (Nat.unpair (Nat.unpair e).2).1 ≤ m :=
        le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) (by omega)
      have hl₂ : (Nat.unpair (Nat.unpair e).2).2 ≤ m :=
        le_trans (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
      have hl₃ : (Nat.unpair e).2 ≤ m := le_trans (Nat.unpair_right_le _) (by omega)
      rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
          (Nat.unpair e).1 = 3 ∨ (Nat.unpair e).1 = 4 ∨ (Nat.unpair e).1 = 5 ∨
          (Nat.unpair e).1 = 6 ∨ (Nat.unpair e).1 = 7 ∨ 8 ≤ (Nat.unpair e).1 by omega)
        with h | h | h | h | h | h | h | h | h
      · have hs : (e : ℕ) + 1 = ^rel (Nat.unpair (Nat.unpair e).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_qqRel_eq, e3, e2, ← h, he]
        rw [IsSemiformula.checkF_succ, if_pos (Or.inl h), hs, IsSemiformula.rel]
        simp only [Bool.and_eq_true, beq_iff_eq, isRelB_iff]
        rw [and_assoc, isSemitermVec_iff_check]
      · have hs : (e : ℕ) + 1 = ^nrel (Nat.unpair (Nat.unpair e).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_qqNRel_eq, e3, e2, ← h, he]
        rw [IsSemiformula.checkF_succ, if_pos (Or.inr h), hs, IsSemiformula.nrel]
        simp only [Bool.and_eq_true, beq_iff_eq, isRelB_iff]
        rw [and_assoc, isSemitermVec_iff_check]
      · rw [IsSemiformula.checkF_succ, if_neg (by omega), if_pos (Or.inl h)]
        simp only [beq_iff_eq]
        constructor
        · intro hz
          have hv : (e : ℕ) + 1 = ^⊤ := by rw [nat_qqVerum_eq, ← h, ← hz, he]
          rw [hv]; simp
        · intro hc; exact (IsUFormula.tag_spec hc.isUFormula).2 (Or.inl h)
      · rw [IsSemiformula.checkF_succ, if_neg (by omega), if_pos (Or.inr h)]
        simp only [beq_iff_eq]
        constructor
        · intro hz
          have hv : (e : ℕ) + 1 = ^⊥ := by rw [nat_qqFalsum_eq, ← h, ← hz, he]
          rw [hv]; simp
        · intro hc; exact (IsUFormula.tag_spec hc.isUFormula).2 (Or.inr h)
      · have hs : (e : ℕ) + 1 =
            (Nat.unpair (Nat.unpair e).2).1 ^⋏ (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_qqAnd_eq, e2, ← h, he]
        rw [IsSemiformula.checkF_succ, if_neg (by omega), if_neg (by omega), if_pos (Or.inl h), hs,
          IsSemiformula.and]
        simp only [Bool.and_eq_true, ih n _ hl₁, ih n _ hl₂]
      · have hs : (e : ℕ) + 1 =
            (Nat.unpair (Nat.unpair e).2).1 ^⋎ (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_qqOr_eq, e2, ← h, he]
        rw [IsSemiformula.checkF_succ, if_neg (by omega), if_neg (by omega), if_pos (Or.inr h), hs,
          IsSemiformula.or]
        simp only [Bool.and_eq_true, ih n _ hl₁, ih n _ hl₂]
      · have hs : (e : ℕ) + 1 = ^∀ (Nat.unpair e).2 := by rw [nat_qqAll_eq, ← h, he]
        rw [IsSemiformula.checkF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (Or.inl h), hs, IsSemiformula.all]
        exact ih (n + 1) _ hl₃
      · have hs : (e : ℕ) + 1 = ^∃ (Nat.unpair e).2 := by rw [nat_qqExs_eq, ← h, he]
        rw [IsSemiformula.checkF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (Or.inr h), hs, IsSemiformula.exs]
        exact ih (n + 1) _ hl₃
      · rw [IsSemiformula.checkF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega)]
        simp only [Bool.false_eq_true, false_iff]
        intro hc
        have := (IsUFormula.tag_spec hc.isUFormula).1
        omega

theorem IsSemiformula.check_iff {n p : ℕ} :
    IsSemiformula.check L n p = true ↔ IsSemiformula L n p :=
  IsSemiformula.checkF_iff_aux p n p le_rfl

instance decidableIsSemiformula (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (n p : ℕ) : Decidable (IsSemiformula (V := ℕ) L n p) :=
  decidable_of_iff _ IsSemiformula.check_iff

/-! ### Function mirrors: `neg`

`neg` is not a predicate but a `UformulaRec1.Construction`, so the mirror returns a *code* and
agreement is an equation. Three things change from the `C1` pattern, and they are the template for
the rest of the function family:

* `case_iff` is replaced by the function's own case equations (`neg_rel` … `neg_ex`). Those are
  guarded by well-formedness, so the induction carries `IsUFormula L p` as a hypothesis and
  propagates it to subformulas with `IsUFormula.and`/`all`/… — the `C1` constructor lemmas;
* adequacy-indexing carries over unchanged: `∀ p ≤ s, IsUFormula L p → negF s p = neg L p`;
* totality is separate. `neg` is `0` off the well-formed codes (`neg_not_uformula`), so the total
  mirror guards the recursion with the `C1` recogniser, and the two regimes are discharged
  independently. This is why `C1` had to come first.

`negF` itself needs no language data: every branch just flips the constructor tag. -/

/-- Fuel-indexed mirror of `neg` on *well-formed* codes. Purely structural on the code: every
branch flips the constructor tag, so no language data is needed. -/
def negF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, e + 1 =>
    if natPi₁ e = 0 then Nat.pair 1 (natPi₂ e) + 1
    else if natPi₁ e = 1 then Nat.pair 0 (natPi₂ e) + 1
    else if natPi₁ e = 2 then Nat.pair 3 0 + 1
    else if natPi₁ e = 3 then Nat.pair 2 0 + 1
    else if natPi₁ e = 4 then
      Nat.pair 5 (Nat.pair (negF s (natPi₁ (natPi₂ e))) (negF s (natPi₂ (natPi₂ e)))) + 1
    else if natPi₁ e = 5 then
      Nat.pair 4 (Nat.pair (negF s (natPi₁ (natPi₂ e))) (negF s (natPi₂ (natPi₂ e)))) + 1
    else if natPi₁ e = 6 then Nat.pair 7 (negF s (natPi₂ e)) + 1
    else if natPi₁ e = 7 then Nat.pair 6 (negF s (natPi₂ e)) + 1
    else 0

/-- The total mirror: guarded by the `C1` recogniser, matching `neg_not_uformula`. -/
def neg.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] (p : ℕ) : ℕ :=
  if IsUFormula.check L p then negF p p else 0

private lemma negF_succ (s e : ℕ) :
    negF (s + 1) (e + 1) =
      (if (Nat.unpair e).1 = 0 then Nat.pair 1 (Nat.unpair e).2 + 1
      else if (Nat.unpair e).1 = 1 then Nat.pair 0 (Nat.unpair e).2 + 1
      else if (Nat.unpair e).1 = 2 then Nat.pair 3 0 + 1
      else if (Nat.unpair e).1 = 3 then Nat.pair 2 0 + 1
      else if (Nat.unpair e).1 = 4 then
        Nat.pair 5 (Nat.pair (negF s (Nat.unpair (Nat.unpair e).2).1)
          (negF s (Nat.unpair (Nat.unpair e).2).2)) + 1
      else if (Nat.unpair e).1 = 5 then
        Nat.pair 4 (Nat.pair (negF s (Nat.unpair (Nat.unpair e).2).1)
          (negF s (Nat.unpair (Nat.unpair e).2).2)) + 1
      else if (Nat.unpair e).1 = 6 then Nat.pair 7 (negF s (Nat.unpair e).2) + 1
      else if (Nat.unpair e).1 = 7 then Nat.pair 6 (negF s (Nat.unpair e).2) + 1
      else 0) := by
  rw [negF]; simp only [natPi₁, natPi₂, natUnpair_eq]

omit [L.DecidableSymbols] in
private lemma negF_eq_aux (s : ℕ) : ∀ p ≤ s, IsUFormula L p → negF s p = neg L p := by
  induction s with
  | zero =>
    intro p hp h
    obtain rfl : p = 0 := by omega
    simp at h
  | succ m ih =>
    intro p hp h
    match p with
    | 0 => simp at h
    | e + 1 =>
      have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
      have e2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
          = (Nat.unpair e).2 := Nat.pair_unpair _
      have e3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
          = (Nat.unpair (Nat.unpair e).2).2 := Nat.pair_unpair _
      have hl₁ : (Nat.unpair (Nat.unpair e).2).1 ≤ m :=
        le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) (by omega)
      have hl₂ : (Nat.unpair (Nat.unpair e).2).2 ≤ m :=
        le_trans (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
      have hl₃ : (Nat.unpair e).2 ≤ m := le_trans (Nat.unpair_right_le _) (by omega)
      rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
          (Nat.unpair e).1 = 3 ∨ (Nat.unpair e).1 = 4 ∨ (Nat.unpair e).1 = 5 ∨
          (Nat.unpair e).1 = 6 ∨ (Nat.unpair e).1 = 7 ∨ 8 ≤ (Nat.unpair e).1 by omega)
        with h' | h' | h' | h' | h' | h' | h' | h' | h'
      · have hs : (e : ℕ) + 1 = ^rel (Nat.unpair (Nat.unpair e).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_qqRel_eq, e3, e2, ← h', he]
        rw [hs] at h
        obtain ⟨hR, hv⟩ := IsUFormula.rel.mp h
        rw [negF_succ, if_pos h', hs, neg_rel hR hv, nat_qqNRel_eq, e3, e2]
      · have hs : (e : ℕ) + 1 = ^nrel (Nat.unpair (Nat.unpair e).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_qqNRel_eq, e3, e2, ← h', he]
        rw [hs] at h
        obtain ⟨hR, hv⟩ := IsUFormula.nrel.mp h
        rw [negF_succ, if_neg (by omega), if_pos h', hs, neg_nrel hR hv, nat_qqRel_eq, e3, e2]
      · have hz : (Nat.unpair e).2 = 0 := (IsUFormula.tag_spec h).2 (Or.inl h')
        have hs : (e : ℕ) + 1 = (^⊤ : ℕ) := by rw [nat_qqVerum_eq, ← h', ← hz, he]
        rw [negF_succ, if_neg (by omega), if_neg (by omega), if_pos h', hs, neg_verum,
          nat_qqFalsum_eq]
      · have hz : (Nat.unpair e).2 = 0 := (IsUFormula.tag_spec h).2 (Or.inr h')
        have hs : (e : ℕ) + 1 = (^⊥ : ℕ) := by rw [nat_qqFalsum_eq, ← h', ← hz, he]
        rw [negF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h', hs,
          neg_falsum, nat_qqVerum_eq]
      · have hs : (e : ℕ) + 1 =
            (Nat.unpair (Nat.unpair e).2).1 ^⋏ (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_qqAnd_eq, e2, ← h', he]
        rw [hs] at h
        obtain ⟨hp₁, hp₂⟩ := IsUFormula.and.mp h
        rw [negF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos h', hs, neg_and hp₁ hp₂, nat_qqOr_eq, ih _ hl₁ hp₁, ih _ hl₂ hp₂]
      · have hs : (e : ℕ) + 1 =
            (Nat.unpair (Nat.unpair e).2).1 ^⋎ (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_qqOr_eq, e2, ← h', he]
        rw [hs] at h
        obtain ⟨hp₁, hp₂⟩ := IsUFormula.or.mp h
        rw [negF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_pos h', hs, neg_or hp₁ hp₂, nat_qqAnd_eq, ih _ hl₁ hp₁,
          ih _ hl₂ hp₂]
      · have hs : (e : ℕ) + 1 = ^∀ (Nat.unpair e).2 := by rw [nat_qqAll_eq, ← h', he]
        rw [hs] at h
        have hp₁ := IsUFormula.all.mp h
        rw [negF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_pos h', hs, neg_all hp₁, nat_qqExs_eq,
          ih _ hl₃ hp₁]
      · have hs : (e : ℕ) + 1 = ^∃ (Nat.unpair e).2 := by rw [nat_qqExs_eq, ← h', he]
        rw [hs] at h
        have hp₁ := IsUFormula.ex.mp h
        rw [negF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h', hs, neg_ex hp₁,
          nat_qqAll_eq, ih _ hl₃ hp₁]
      · have := (IsUFormula.tag_spec h).1; omega

theorem neg.check_eq (p : ℕ) : neg.check L p = neg L p := by
  rw [neg.check]
  by_cases h : IsUFormula.check L p = true
  · rw [if_pos h]
    exact negF_eq_aux p p le_rfl (IsUFormula.check_iff.mp h)
  · rw [if_neg h]
    exact (neg_not_uformula fun hc ↦ h (IsUFormula.check_iff.mpr hc)).symm

/-! ### Function mirrors: `shift`

`neg` again, with two differences: the `^rel`/`^nrel` branches call the term-level
`termShiftVec.check` (which is why the term layer had to land first), and the constructor tag is
*preserved* rather than flipped, so those two branches share a single arm. -/

def shiftF (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, e + 1 =>
    if natPi₁ e = 0 ∨ natPi₁ e = 1 then
      Nat.pair (natPi₁ e) (Nat.pair (natPi₁ (natPi₂ e))
        (Nat.pair (natPi₁ (natPi₂ (natPi₂ e)))
          (termShiftVec.check L (natPi₂ (natPi₂ (natPi₂ e)))))) + 1
    else if natPi₁ e = 2 ∨ natPi₁ e = 3 then Nat.pair (natPi₁ e) 0 + 1
    else if natPi₁ e = 4 ∨ natPi₁ e = 5 then
      Nat.pair (natPi₁ e) (Nat.pair (shiftF L s (natPi₁ (natPi₂ e)))
        (shiftF L s (natPi₂ (natPi₂ e)))) + 1
    else if natPi₁ e = 6 ∨ natPi₁ e = 7 then
      Nat.pair (natPi₁ e) (shiftF L s (natPi₂ e)) + 1
    else 0

/-- The total mirror: guarded by the `C1` recogniser, matching `shift_not_uformula`. -/
def shift.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols] (p : ℕ) : ℕ :=
  if IsUFormula.check L p then shiftF L p p else 0

private lemma shiftF_succ (s e : ℕ) :
    shiftF L (s + 1) (e + 1) =
      (if (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 then
        Nat.pair (Nat.unpair e).1 (Nat.pair (Nat.unpair (Nat.unpair e).2).1
          (Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (termShiftVec.check L (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2))) + 1
      else if (Nat.unpair e).1 = 2 ∨ (Nat.unpair e).1 = 3 then Nat.pair (Nat.unpair e).1 0 + 1
      else if (Nat.unpair e).1 = 4 ∨ (Nat.unpair e).1 = 5 then
        Nat.pair (Nat.unpair e).1 (Nat.pair (shiftF L s (Nat.unpair (Nat.unpair e).2).1)
          (shiftF L s (Nat.unpair (Nat.unpair e).2).2)) + 1
      else if (Nat.unpair e).1 = 6 ∨ (Nat.unpair e).1 = 7 then
        Nat.pair (Nat.unpair e).1 (shiftF L s (Nat.unpair e).2) + 1
      else 0) := by
  rw [shiftF]; simp only [natPi₁, natPi₂, natUnpair_eq]

private lemma shiftF_eq_aux (s : ℕ) : ∀ p ≤ s, IsUFormula L p → shiftF L s p = shift L p := by
  induction s with
  | zero =>
    intro p hp h
    obtain rfl : p = 0 := by omega
    simp at h
  | succ m ih =>
    intro p hp h
    match p with
    | 0 => simp at h
    | e + 1 =>
      have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
      have e2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
          = (Nat.unpair e).2 := Nat.pair_unpair _
      have e3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2
          = (Nat.unpair (Nat.unpair e).2).2 := Nat.pair_unpair _
      have hl₁ : (Nat.unpair (Nat.unpair e).2).1 ≤ m :=
        le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) (by omega)
      have hl₂ : (Nat.unpair (Nat.unpair e).2).2 ≤ m :=
        le_trans (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) (by omega)
      have hl₃ : (Nat.unpair e).2 ≤ m := le_trans (Nat.unpair_right_le _) (by omega)
      rcases (show (Nat.unpair e).1 = 0 ∨ (Nat.unpair e).1 = 1 ∨ (Nat.unpair e).1 = 2 ∨
          (Nat.unpair e).1 = 3 ∨ (Nat.unpair e).1 = 4 ∨ (Nat.unpair e).1 = 5 ∨
          (Nat.unpair e).1 = 6 ∨ (Nat.unpair e).1 = 7 ∨ 8 ≤ (Nat.unpair e).1 by omega)
        with h' | h' | h' | h' | h' | h' | h' | h' | h'
      · have hs : (e : ℕ) + 1 = ^rel (Nat.unpair (Nat.unpair e).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_qqRel_eq, e3, e2, ← h', he]
        rw [hs] at h
        obtain ⟨hR, hv⟩ := IsUFormula.rel.mp h
        rw [shiftF_succ, if_pos (Or.inl h'), hs, shift_rel hR hv, nat_qqRel_eq, h',
          termShiftVec.check_eq hv]
      · have hs : (e : ℕ) + 1 = ^nrel (Nat.unpair (Nat.unpair e).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_qqNRel_eq, e3, e2, ← h', he]
        rw [hs] at h
        obtain ⟨hR, hv⟩ := IsUFormula.nrel.mp h
        rw [shiftF_succ, if_pos (Or.inr h'), hs, shift_nrel hR hv, nat_qqNRel_eq, h',
          termShiftVec.check_eq hv]
      · have hz : (Nat.unpair e).2 = 0 := (IsUFormula.tag_spec h).2 (Or.inl h')
        have hs : (e : ℕ) + 1 = (^⊤ : ℕ) := by rw [nat_qqVerum_eq, ← h', ← hz, he]
        rw [shiftF_succ, if_neg (by omega), if_pos (Or.inl h'), hs, shift_verum, nat_qqVerum_eq, h']
      · have hz : (Nat.unpair e).2 = 0 := (IsUFormula.tag_spec h).2 (Or.inr h')
        have hs : (e : ℕ) + 1 = (^⊥ : ℕ) := by rw [nat_qqFalsum_eq, ← h', ← hz, he]
        rw [shiftF_succ, if_neg (by omega), if_pos (Or.inr h'), hs, shift_falsum, nat_qqFalsum_eq,
          h']
      · have hs : (e : ℕ) + 1 =
            (Nat.unpair (Nat.unpair e).2).1 ^⋏ (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_qqAnd_eq, e2, ← h', he]
        rw [hs] at h
        obtain ⟨hp₁, hp₂⟩ := IsUFormula.and.mp h
        rw [shiftF_succ, if_neg (by omega), if_neg (by omega), if_pos (Or.inl h'), hs,
          shift_and hp₁ hp₂, nat_qqAnd_eq, h', ih _ hl₁ hp₁, ih _ hl₂ hp₂]
      · have hs : (e : ℕ) + 1 =
            (Nat.unpair (Nat.unpair e).2).1 ^⋎ (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_qqOr_eq, e2, ← h', he]
        rw [hs] at h
        obtain ⟨hp₁, hp₂⟩ := IsUFormula.or.mp h
        rw [shiftF_succ, if_neg (by omega), if_neg (by omega), if_pos (Or.inr h'), hs,
          shift_or hp₁ hp₂, nat_qqOr_eq, h', ih _ hl₁ hp₁, ih _ hl₂ hp₂]
      · have hs : (e : ℕ) + 1 = ^∀ (Nat.unpair e).2 := by rw [nat_qqAll_eq, ← h', he]
        rw [hs] at h
        have hp₁ := IsUFormula.all.mp h
        rw [shiftF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (Or.inl h'), hs, shift_all hp₁, nat_qqAll_eq, h', ih _ hl₃ hp₁]
      · have hs : (e : ℕ) + 1 = ^∃ (Nat.unpair e).2 := by rw [nat_qqExs_eq, ← h', he]
        rw [hs] at h
        have hp₁ := IsUFormula.ex.mp h
        rw [shiftF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (Or.inr h'), hs, shift_exs hp₁, nat_qqExs_eq, h', ih _ hl₃ hp₁]
      · rw [shiftF_succ, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        have := (IsUFormula.tag_spec h).1; omega

theorem shift.check_eq (p : ℕ) : shift.check L p = shift L p := by
  rw [shift.check]
  by_cases h : IsUFormula.check L p = true
  · rw [if_pos h]
    exact shiftF_eq_aux p p le_rfl (IsUFormula.check_iff.mp h)
  · rw [if_neg h]
    exact (shift_not_uformula fun hc ↦ h (IsUFormula.check_iff.mpr hc)).symm

/-! ### It runs

`7 = ^⊤`; `3974 = ^⊤ ^⋏ ^⊤`; `73` has constructor tag `8`. Inputs are bare numerals — see
`Syntax/Term/Standard.lean` for why the `decide` tactic is reached through `check_iff`. -/

example : IsUFormula.check ℒₒᵣ 7 = true := by decide

example : IsUFormula (V := ℕ) ℒₒᵣ 7 := IsUFormula.check_iff.mp (by decide)

example : IsUFormula (V := ℕ) ℒₒᵣ 3974 := IsUFormula.check_iff.mp (by decide)

example : ¬IsUFormula (V := ℕ) ℒₒᵣ 0 := fun h ↦ absurd (IsUFormula.check_iff.mpr h) (by decide)

example : ¬IsUFormula (V := ℕ) ℒₒᵣ 73 := fun h ↦ absurd (IsUFormula.check_iff.mpr h) (by decide)

example : IsSemiformula (V := ℕ) ℒₒᵣ 0 7 := IsSemiformula.check_iff.mp (by decide)

example : ¬IsSemiformula (V := ℕ) ℒₒᵣ 0 73 :=
  fun h ↦ absurd (IsSemiformula.check_iff.mpr h) (by decide)

example : neg.check ℒₒᵣ 7 = 13 := by decide

/-- `7 = ^⊤`, `13 = ^⊥`. -/
example : neg (V := ℕ) ℒₒᵣ 7 = 13 := by rw [← neg.check_eq]; decide

/-- Off the well-formed codes `neg` is `0`, and the mirror agrees there too. -/
example : neg (V := ℕ) ℒₒᵣ 73 = 0 := by rw [← neg.check_eq]; decide

/-- `^⊤` is closed, so shifting fixes it. -/
example : shift (V := ℕ) ℒₒᵣ 7 = 7 := by rw [← shift.check_eq]; decide

example : shift (V := ℕ) ℒₒᵣ 73 = 0 := by rw [← shift.check_eq]; decide

end LO.FirstOrder.Arithmetic.Bootstrapping

end
