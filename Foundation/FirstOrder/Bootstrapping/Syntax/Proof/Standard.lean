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
