module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Standard
public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
public import Foundation.FirstOrder.Bootstrapping.Syntax.DecidableTheory

@[expose] public section
/-!
# Executable recognition of coded formula sets

`IsFormulaSet L s` is `∀ p ∈ s, IsFormula L p`, a bounded quantification over the coded set rather
than a `Fixpoint`, so no recursion is needed: the mirror folds `IsSemiformula.check L 0` over the
members. `Nat.bitIndices` enumerates them, and `nat_mem_iff_testBit` (`HFS/Standard.lean`) is the
bridge from `∈` at `V := ℕ`.

**Inputs must be numerals.** A set *literal* such as `({p, q} : ℕ)` is built from `insert` and
`singleton`, which go through `Exp.exp`, a `Classical.choose!`; it does not reduce, so `decide`
gets stuck on the literal rather than on the recogniser. `nat_singleton_eq`/`nat_insert_eq` rewrite
such a literal to a numeral, but as rewrite rules they are unavailable to `decide`. Feed the
recogniser codes, not sets built with set notation — `{p}` becomes `2 ^ p`, and a union becomes a
sum of distinct powers of two.
-/

namespace LO.FirstOrder.Arithmetic.Bootstrapping

open LO.FirstOrder.Theory

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
variable {T : Theory L} [T.Δ₁] [T.DecidableΔ₁]

/-- Executable mirror of `IsFormulaSet` at `V := ℕ`. -/
def IsFormulaSet.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (s : ℕ) : Bool := s.bitIndices.all fun p ↦ IsSemiformula.check L 0 p

theorem IsFormulaSet.check_iff {s : ℕ} : IsFormulaSet.check L s = true ↔ IsFormulaSet L s := by
  simp only [IsFormulaSet.check, List.all_eq_true, Nat.mem_bitIndices, IsFormulaSet]
  constructor
  · intro h p hp
    exact IsSemiformula.check_iff.mp (h p (nat_mem_iff_testBit.mp hp))
  · intro h p hp
    exact IsSemiformula.check_iff.mpr (h p (nat_mem_iff_testBit.mpr hp))

instance decidableIsFormulaSet (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (s : ℕ) : Decidable (IsFormulaSet (V := ℕ) L s) := decidable_of_iff _ IsFormulaSet.check_iff

/-! ### Function mirror: `setShift`

Pattern C — no recursion at all. `setShift` is `Classical.choose!` from a replacement axiom,
characterised by `mem_setShift_iff : y ∈ setShift L s ↔ ∃ x ∈ s, y = shift L x`, so the mirror maps
`shift.check` over `Nat.bitIndices` and rebuilds the set with `natInsert`, and agreement is set
extensionality (`mem_ext`) rather than an induction on codes. Structurally this is
`IsFormulaSet.check` above, with a fold that builds instead of one that tests.

This is the mirror the derivation checker calls: `Derivation.Phi`'s `shiftRule` side condition is
`s = setShift L (fstIdx d)`, so `setShift.check` is what decides it. Its input and output are bare
code numerals, per the constraint recorded above. -/

/-- Executable mirror of `setShift` at `V := ℕ`. -/
def setShift.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (s : ℕ) : ℕ := (s.bitIndices.map (shift.check L)).foldr natInsert 0

theorem setShift.check_eq (s : ℕ) : setShift.check L s = setShift L s := by
  refine mem_ext fun y ↦ ?_
  rw [setShift.check, mem_foldr_natInsert, mem_setShift_iff]
  simp only [List.mem_map, Nat.mem_bitIndices]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, nat_mem_iff_testBit.mpr hx, shift.check_eq (L := L) x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, nat_mem_iff_testBit.mp hx, shift.check_eq (L := L) x⟩

/-! ### The derivation constructors at `V := ℕ`

Note the shape: unlike term and formula codes, whose tag is the *first* component, a derivation
code is `⟪s, tag, …⟫ + 1` — the sequent comes first and the tag second. -/

lemma nat_axL_eq (s p : ℕ) : (axL s p : ℕ) = Nat.pair s (Nat.pair 0 p) + 1 := by
  simp [axL, nat_pair_eq]

lemma nat_verumIntro_eq (s : ℕ) : (verumIntro s : ℕ) = Nat.pair s (Nat.pair 1 0) + 1 := by
  simp [verumIntro, nat_pair_eq]

lemma nat_andIntro_eq (s p q dp dq : ℕ) :
    (andIntro s p q dp dq : ℕ)
      = Nat.pair s (Nat.pair 2 (Nat.pair p (Nat.pair q (Nat.pair dp dq)))) + 1 := by
  simp [andIntro, nat_pair_eq]

lemma nat_orIntro_eq (s p q d : ℕ) :
    (orIntro s p q d : ℕ) = Nat.pair s (Nat.pair 3 (Nat.pair p (Nat.pair q d))) + 1 := by
  simp [orIntro, nat_pair_eq]

lemma nat_allIntro_eq (s p d : ℕ) :
    (allIntro s p d : ℕ) = Nat.pair s (Nat.pair 4 (Nat.pair p d)) + 1 := by
  simp [allIntro, nat_pair_eq]

lemma nat_exsIntro_eq (s p t d : ℕ) :
    (exsIntro s p t d : ℕ) = Nat.pair s (Nat.pair 5 (Nat.pair p (Nat.pair t d))) + 1 := by
  simp [exsIntro, nat_pair_eq]

lemma nat_wkRule_eq (s d : ℕ) : (wkRule s d : ℕ) = Nat.pair s (Nat.pair 6 d) + 1 := by
  simp [wkRule, nat_pair_eq]

lemma nat_shiftRule_eq (s d : ℕ) : (shiftRule s d : ℕ) = Nat.pair s (Nat.pair 7 d) + 1 := by
  simp [shiftRule, nat_pair_eq]

lemma nat_cutRule_eq (s p d₁ d₂ : ℕ) :
    (cutRule s p d₁ d₂ : ℕ) = Nat.pair s (Nat.pair 8 (Nat.pair p (Nat.pair d₁ d₂))) + 1 := by
  simp [cutRule, nat_pair_eq]

lemma nat_axm_eq (s p : ℕ) : (axm s p : ℕ) = Nat.pair s (Nat.pair 9 p) + 1 := by
  simp [axm, nat_pair_eq]

/-! ### The checker -/

/-- Fuel-indexed executable mirror of `Derivation`, dispatching on the ten `Phi` disjuncts. -/
def Derivation.checkF (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (T : Theory L) [T.Δ₁] [T.DecidableΔ₁] : ℕ → ℕ → Bool
  | 0, _ => false
  | _ + 1, 0 => false
  | fuel + 1, e + 1 =>
    IsFormulaSet.check L (natPi₁ e) &&
      (if natPi₁ (natPi₂ e) = 0 then
        decide (natPi₂ (natPi₂ e) ∈ natPi₁ e) &&
          decide (neg.check L (natPi₂ (natPi₂ e)) ∈ natPi₁ e)
      else if natPi₁ (natPi₂ e) = 1 then
        (natPi₂ (natPi₂ e) == 0) && decide ((Nat.pair 2 0 + 1 : ℕ) ∈ natPi₁ e)
      else if natPi₁ (natPi₂ e) = 2 then
        decide ((Nat.pair 4 (Nat.pair (natPi₁ (natPi₂ (natPi₂ e)))
            (natPi₁ (natPi₂ (natPi₂ (natPi₂ e))))) + 1 : ℕ) ∈ natPi₁ e) &&
          (natFstIdx (natPi₁ (natPi₂ (natPi₂ (natPi₂ (natPi₂ e))))) ==
            natInsert (natPi₁ (natPi₂ (natPi₂ e))) (natPi₁ e)) &&
          Derivation.checkF L T fuel (natPi₁ (natPi₂ (natPi₂ (natPi₂ (natPi₂ e))))) &&
          (natFstIdx (natPi₂ (natPi₂ (natPi₂ (natPi₂ (natPi₂ e))))) ==
            natInsert (natPi₁ (natPi₂ (natPi₂ (natPi₂ e)))) (natPi₁ e)) &&
          Derivation.checkF L T fuel (natPi₂ (natPi₂ (natPi₂ (natPi₂ (natPi₂ e)))))
      else if natPi₁ (natPi₂ e) = 3 then
        decide ((Nat.pair 5 (Nat.pair (natPi₁ (natPi₂ (natPi₂ e)))
            (natPi₁ (natPi₂ (natPi₂ (natPi₂ e))))) + 1 : ℕ) ∈ natPi₁ e) &&
          (natFstIdx (natPi₂ (natPi₂ (natPi₂ (natPi₂ e)))) ==
            natInsert (natPi₁ (natPi₂ (natPi₂ e)))
              (natInsert (natPi₁ (natPi₂ (natPi₂ (natPi₂ e)))) (natPi₁ e))) &&
          Derivation.checkF L T fuel (natPi₂ (natPi₂ (natPi₂ (natPi₂ e))))
      else if natPi₁ (natPi₂ e) = 4 then
        decide ((Nat.pair 6 (natPi₁ (natPi₂ (natPi₂ e))) + 1 : ℕ) ∈ natPi₁ e) &&
          (natFstIdx (natPi₂ (natPi₂ (natPi₂ e))) ==
            natInsert (free.check L (natPi₁ (natPi₂ (natPi₂ e))))
              (setShift.check L (natPi₁ e))) &&
          Derivation.checkF L T fuel (natPi₂ (natPi₂ (natPi₂ e)))
      else if natPi₁ (natPi₂ e) = 5 then
        decide ((Nat.pair 7 (natPi₁ (natPi₂ (natPi₂ e))) + 1 : ℕ) ∈ natPi₁ e) &&
          IsSemiterm.check L 0 (natPi₁ (natPi₂ (natPi₂ (natPi₂ e)))) &&
          (natFstIdx (natPi₂ (natPi₂ (natPi₂ (natPi₂ e)))) ==
            natInsert (substs1.check L (natPi₁ (natPi₂ (natPi₂ (natPi₂ e))))
              (natPi₁ (natPi₂ (natPi₂ e)))) (natPi₁ e)) &&
          Derivation.checkF L T fuel (natPi₂ (natPi₂ (natPi₂ (natPi₂ e))))
      else if natPi₁ (natPi₂ e) = 6 then
        decide (natFstIdx (natPi₂ (natPi₂ e)) ⊆ natPi₁ e) &&
          Derivation.checkF L T fuel (natPi₂ (natPi₂ e))
      else if natPi₁ (natPi₂ e) = 7 then
        (natPi₁ e == setShift.check L (natFstIdx (natPi₂ (natPi₂ e)))) &&
          Derivation.checkF L T fuel (natPi₂ (natPi₂ e))
      else if natPi₁ (natPi₂ e) = 8 then
        (natFstIdx (natPi₁ (natPi₂ (natPi₂ (natPi₂ e)))) ==
            natInsert (natPi₁ (natPi₂ (natPi₂ e))) (natPi₁ e)) &&
          Derivation.checkF L T fuel (natPi₁ (natPi₂ (natPi₂ (natPi₂ e)))) &&
          (natFstIdx (natPi₂ (natPi₂ (natPi₂ (natPi₂ e)))) ==
            natInsert (neg.check L (natPi₁ (natPi₂ (natPi₂ e)))) (natPi₁ e)) &&
          Derivation.checkF L T fuel (natPi₂ (natPi₂ (natPi₂ (natPi₂ e))))
      else if natPi₁ (natPi₂ e) = 9 then
        decide (natPi₂ (natPi₂ e) ∈ natPi₁ e) &&
          DecidableΔ₁.decide (T := T) (natPi₂ (natPi₂ e))
      else false)

def Derivation.check (L : Language) [L.Encodable] [L.LORDefinable] [L.DecidableSymbols]
    (T : Theory L) [T.Δ₁] [T.DecidableΔ₁] (d : ℕ) : Bool := Derivation.checkF L T d d

/-! ### Agreement

The adequacy-indexed induction against `Derivation.case_iff`, eleven branches. Three things carry
it:

* the `IsFormulaSet` conjunct factors out with `and_congr_right`, which hands every branch the
  well-formedness hypothesis structurally rather than by plumbing;
* after `rw [hs]` the `C3` disjointness set collapses the nine wrong disjuncts to `False ∧ …`, so
  most branches are two to six lines. This needs *both* orientations of each `_ne_`;
* negative branches rebuild `Derivation T (e + 1)` from the disjunction and `hfs` via
  `case_iff.mpr`, so `tag_spec` applies inside the backward direction.

`exsIntro` is the only branch that is not uniform, and for the reason predicted when the interface
was tabulated: `substs1.check_eq` is the single conditional agreement in the whole checker. `simp`
reduces that branch to an implication carrying `IsSemiterm L 0 t` in its antecedent, so
`intro _ ht _; rw [substs1.check_eq ht.isUTerm]` finishes it — the hypothesis `Phi` supplies is
exactly the one the mirror wants. -/

/-- `fstIdx` of a successor code is the first projection. -/
private lemma nat_fstIdx_succ (e : ℕ) : fstIdx ((e : ℕ) + 1) = (Nat.unpair e).1 := by
  rw [natFstIdx_eq, natFstIdx, natPi₁, natUnpair_eq]; simp

omit [L.DecidableSymbols] [T.DecidableΔ₁] in
/-- Read the constructor tag off a code that is a derivation. Proved once, by the ten-way
`case_iff` enumeration, so the negative branches need only `omega`. -/
private lemma Derivation.tag_spec {e : ℕ} (h : Derivation T (e + 1)) :
    (Nat.unpair (Nat.unpair e).2).1 ≤ 9 ∧
      ((Nat.unpair (Nat.unpair e).2).1 = 1 → (Nat.unpair (Nat.unpair e).2).2 = 0) := by
  rcases h.case.2 with (⟨s, p, hv, _⟩ | ⟨s, hv, _⟩ | ⟨s, p, q, dp, dq, hv, _⟩ |
    ⟨s, p, q, dpq, hv, _⟩ | ⟨s, p, dp, hv, _⟩ | ⟨s, p, t, dp, hv, _⟩ |
    ⟨s, d', hv, _⟩ | ⟨s, d', hv, _⟩ | ⟨s, p, d₁, d₂, hv, _⟩ | ⟨s, p, hv, _⟩)
  · rw [nat_axL_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 0 p) := by omega
    simp
  · rw [nat_verumIntro_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 1 0) := by omega
    simp
  · rw [nat_andIntro_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 2 (Nat.pair p (Nat.pair q (Nat.pair dp dq)))) := by omega
    simp
  · rw [nat_orIntro_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 3 (Nat.pair p (Nat.pair q dpq))) := by omega
    simp
  · rw [nat_allIntro_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 4 (Nat.pair p dp)) := by omega
    simp
  · rw [nat_exsIntro_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 5 (Nat.pair p (Nat.pair t dp))) := by omega
    simp
  · rw [nat_wkRule_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 6 d') := by omega
    simp
  · rw [nat_shiftRule_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 7 d') := by omega
    simp
  · rw [nat_cutRule_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 8 (Nat.pair p (Nat.pair d₁ d₂))) := by omega
    simp
  · rw [nat_axm_eq] at hv
    obtain rfl : e = Nat.pair s (Nat.pair 9 p) := by omega
    simp


private lemma Derivation.checkF_iff_aux (n : ℕ) :
    ∀ d ≤ n, (Derivation.checkF L T n d = true ↔ Derivation T d) := by
  induction n with
  | zero =>
    intro d hd
    obtain rfl : d = 0 := by omega
    simp only [Derivation.checkF, Bool.false_eq_true, false_iff]
    intro hc
    rcases hc.case.2 with (⟨s, p, hv, _⟩ | ⟨s, hv, _⟩ | ⟨s, p, q, dp, dq, hv, _⟩ |
      ⟨s, p, q, dpq, hv, _⟩ | ⟨s, p, dp, hv, _⟩ | ⟨s, p, t, dp, hv, _⟩ |
      ⟨s, d', hv, _⟩ | ⟨s, d', hv, _⟩ | ⟨s, p, d₁, d₂, hv, _⟩ | ⟨s, p, hv, _⟩) <;>
    · first
      | (rw [nat_axL_eq] at hv; omega) | (rw [nat_verumIntro_eq] at hv; omega)
      | (rw [nat_andIntro_eq] at hv; omega) | (rw [nat_orIntro_eq] at hv; omega)
      | (rw [nat_allIntro_eq] at hv; omega) | (rw [nat_exsIntro_eq] at hv; omega)
      | (rw [nat_wkRule_eq] at hv; omega) | (rw [nat_shiftRule_eq] at hv; omega)
      | (rw [nat_cutRule_eq] at hv; omega) | (rw [nat_axm_eq] at hv; omega)
  | succ m ih =>
    intro d hd
    match d with
    | 0 =>
      simp only [Derivation.checkF, Bool.false_eq_true, false_iff]
      intro hc
      rcases hc.case.2 with (⟨s, p, hv, _⟩ | ⟨s, hv, _⟩ | ⟨s, p, q, dp, dq, hv, _⟩ |
        ⟨s, p, q, dpq, hv, _⟩ | ⟨s, p, dp, hv, _⟩ | ⟨s, p, t, dp, hv, _⟩ |
        ⟨s, d', hv, _⟩ | ⟨s, d', hv, _⟩ | ⟨s, p, d₁, d₂, hv, _⟩ | ⟨s, p, hv, _⟩) <;>
      · first
        | (rw [nat_axL_eq] at hv; omega) | (rw [nat_verumIntro_eq] at hv; omega)
        | (rw [nat_andIntro_eq] at hv; omega) | (rw [nat_orIntro_eq] at hv; omega)
        | (rw [nat_allIntro_eq] at hv; omega) | (rw [nat_exsIntro_eq] at hv; omega)
        | (rw [nat_wkRule_eq] at hv; omega) | (rw [nat_shiftRule_eq] at hv; omega)
        | (rw [nat_cutRule_eq] at hv; omega) | (rw [nat_axm_eq] at hv; omega)
    | e + 1 =>
      have he : Nat.pair (Nat.unpair e).1 (Nat.unpair e).2 = e := Nat.pair_unpair e
      have he2 : Nat.pair (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2
          = (Nat.unpair e).2 := Nat.pair_unpair _
      have he3 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 = (Nat.unpair (Nat.unpair e).2).2 :=
        Nat.pair_unpair _
      have he4 : Nat.pair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2
          = (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := Nat.pair_unpair _
      have he5 : Nat.pair
          (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2).2
          = (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2 := Nat.pair_unpair _
      have hle : ∀ x, x ≤ (Nat.unpair (Nat.unpair e).2).2 → x ≤ m := fun x hx ↦
        le_trans hx (le_trans (Nat.unpair_right_le _)
          (le_trans (Nat.unpair_right_le _) (by omega)))
      rw [Derivation.case_iff, nat_fstIdx_succ, Derivation.checkF]
      simp only [natPi₁, natPi₂, natUnpair_eq, Bool.and_eq_true, IsFormulaSet.check_iff]
      refine and_congr_right fun hfs ↦ ?_
      rcases (show (Nat.unpair (Nat.unpair e).2).1 = 0 ∨ (Nat.unpair (Nat.unpair e).2).1 = 1 ∨
          (Nat.unpair (Nat.unpair e).2).1 = 2 ∨ (Nat.unpair (Nat.unpair e).2).1 = 3 ∨
          (Nat.unpair (Nat.unpair e).2).1 = 4 ∨ (Nat.unpair (Nat.unpair e).2).1 = 5 ∨
          (Nat.unpair (Nat.unpair e).2).1 = 6 ∨ (Nat.unpair (Nat.unpair e).2).1 = 7 ∨
          (Nat.unpair (Nat.unpair e).2).1 = 8 ∨ (Nat.unpair (Nat.unpair e).2).1 = 9 ∨
          10 ≤ (Nat.unpair (Nat.unpair e).2).1 by omega)
        with h | h | h | h | h | h | h | h | h | h | h
      · -- axL
        have hs : (e : ℕ) + 1 = Bootstrapping.axL (Nat.unpair e).1 (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_axL_eq, ← h, he2, he]
        rw [if_pos h, hs]
        simp [neg.check_eq]
      · -- verumIntro
        by_cases hz : (Nat.unpair (Nat.unpair e).2).2 = 0
        · have hs : (e : ℕ) + 1 = Bootstrapping.verumIntro (Nat.unpair e).1 := by
            rw [nat_verumIntro_eq, ← h, ← hz, he2, he]
          rw [if_neg (by omega), if_pos h, hs]
          simp [hz, nat_qqVerum_eq]
        · rw [if_neg (by omega), if_pos h]
          refine iff_of_false (by simp [hz]) fun hdisj ↦ hz ?_
          exact (Derivation.tag_spec
            (Derivation.case_iff.mpr ⟨by rwa [nat_fstIdx_succ], hdisj⟩)).2 h
      · -- andIntro
        have hs : (e : ℕ) + 1 = Bootstrapping.andIntro (Nat.unpair e).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2).2 := by
          rw [nat_andIntro_eq, he5, he4, he3, ← h, he2, he]
        rw [if_neg (by omega), if_neg (by omega), if_pos h, hs]
        simp [DerivationOf, ← natFstIdx_eq, ← natInsert_eq, nat_qqAnd_eq,
          ih _ (hle _ (le_trans (Nat.unpair_left_le _)
            (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)))),
          ih _ (hle _ (le_trans (Nat.unpair_right_le _)
            (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)))), and_assoc]
      · -- orIntro
        have hs : (e : ℕ) + 1 = Bootstrapping.orIntro (Nat.unpair e).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2 := by
          rw [nat_orIntro_eq, he4, he3, ← h, he2, he]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h, hs]
        simp [DerivationOf, ← natFstIdx_eq, ← natInsert_eq, nat_qqOr_eq,
          ih _ (hle _ (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))), and_assoc]
      · -- allIntro
        have hs : (e : ℕ) + 1 = Bootstrapping.allIntro (Nat.unpair e).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2 := by
          rw [nat_allIntro_eq, he3, ← h, he2, he]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos h, hs]
        simp [DerivationOf, ← natFstIdx_eq, ← natInsert_eq, nat_qqAll_eq, free.check_eq,
          setShift.check_eq, ih _ (hle _ (Nat.unpair_right_le _)), and_assoc]
      · -- exsIntro
        have hs : (e : ℕ) + 1 = Bootstrapping.exsIntro (Nat.unpair e).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2 := by
          rw [nat_exsIntro_eq, he4, he3, ← h, he2, he]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_pos h, hs]
        have hdp : (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2 ≤ m :=
          hle _ (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))
        simp only [← natFstIdx_eq, ← natInsert_eq, Bool.and_eq_true, decide_eq_true_eq,
          IsSemiterm.check_iff, beq_iff_eq, and_assoc, ih _ hdp, exsIntro_ne_axL, false_and,
          exists_const, exsIntro_ne_verumIntro, exsIntro_ne_andIntro, DerivationOf,
          exsIntro_ne_orIntro, exsIntro_ne_allIntro, exsIntro_inj, nat_qqExs_eq, exists_and_left,
          ↓existsAndEq, true_and, exists_eq_left', exsIntro_ne_wkRule, exsIntro_ne_shiftRule,
          exsIntro_ne_cutRule, exsIntro_ne_axm, or_self, or_false, false_or, and_congr_right_iff,
          and_congr_left_iff]
        intro _ ht _
        rw [substs1.check_eq ht.isUTerm]
      · -- wkRule
        have hs : (e : ℕ) + 1 = Bootstrapping.wkRule (Nat.unpair e).1
            (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_wkRule_eq, ← h, he2, he]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_pos h, hs]
        simp [← natFstIdx_eq, ih _ (hle _ le_rfl)]
      · -- shiftRule
        have hs : (e : ℕ) + 1 = Bootstrapping.shiftRule (Nat.unpair e).1
            (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_shiftRule_eq, ← h, he2, he]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h, hs]
        simp [← natFstIdx_eq, setShift.check_eq, ih _ (hle _ le_rfl)]
      · -- cutRule
        have hs : (e : ℕ) + 1 = Bootstrapping.cutRule (Nat.unpair e).1
            (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).1
            (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair e).2).2).2).2 := by
          rw [nat_cutRule_eq, he4, he3, ← h, he2, he]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_pos h, hs]
        simp [DerivationOf, ← natFstIdx_eq, ← natInsert_eq, neg.check_eq,
          ih _ (hle _ (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _))),
          ih _ (hle _ (le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _))), and_assoc]
      · -- axm
        have hs : (e : ℕ) + 1 = Bootstrapping.axm (Nat.unpair e).1
            (Nat.unpair (Nat.unpair e).2).2 := by
          rw [nat_axm_eq, ← h, he2, he]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_pos h, hs]
        simp [DecidableΔ₁.decide_iff]
      · -- tag ≥ 10
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        simp only [Bool.false_eq_true, false_iff]
        intro hdisj
        have := (Derivation.tag_spec
          (Derivation.case_iff.mpr ⟨by rwa [nat_fstIdx_succ], hdisj⟩)).1
        omega

theorem Derivation.check_iff {d : ℕ} : Derivation.check L T d = true ↔ Derivation T d :=
  Derivation.checkF_iff_aux d d le_rfl

/-! ### It runs -/

/-- `0 = ∅`. -/
example : IsFormulaSet (V := ℕ) ℒₒᵣ 0 := IsFormulaSet.check_iff.mp (by decide)

/-- `128 = 2 ^ 7 = {^⊤}`. -/
example : IsFormulaSet (V := ℕ) ℒₒᵣ 128 := IsFormulaSet.check_iff.mp (by decide)

/-- `1 = 2 ^ 0 = {0}`, and `0` is no formula. -/
example : ¬IsFormulaSet (V := ℕ) ℒₒᵣ 1 :=
  fun h ↦ absurd (IsFormulaSet.check_iff.mpr h) (by decide)

/-- `384 = 2 ^ 7 + 2 ^ 8 = {^⊤, 8}`, and `8` is no formula. -/
example : ¬IsFormulaSet (V := ℕ) ℒₒᵣ 384 :=
  fun h ↦ absurd (IsFormulaSet.check_iff.mpr h) (by decide)

example : setShift.check ℒₒᵣ 0 = 0 := by decide

/-- `128 = {^⊤}`, and `^⊤` is closed, so shifting the set fixes it. -/
example : setShift (V := ℕ) ℒₒᵣ 128 = 128 := by rw [← setShift.check_eq]; decide

example : Derivation.check ℒₒᵣ (∅ : Theory ℒₒᵣ) 0 = false := by decide

end LO.FirstOrder.Arithmetic.Bootstrapping

end
