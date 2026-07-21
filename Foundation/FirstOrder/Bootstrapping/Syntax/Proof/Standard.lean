module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Standard
public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

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

end LO.FirstOrder.Arithmetic.Bootstrapping

end
