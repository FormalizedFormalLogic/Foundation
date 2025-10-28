import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
import Foundation.FirstOrder.Arithmetic.Definability
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Prime.Lemmas
import Foundation.Vorspiel.ExistsUnique

/-!
# Functions and relations defined in $\mathsf{PA^-}$

This file provides functions and relations defined in $\mathsf{PA^-}

-/

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗣𝗔⁻]

variable {a b c : V}

/-! ### (Modified) Subtraction -/

section sub

lemma sub_existsUnique (a b : V) : ∃! c, (a ≥ b → a = b + c) ∧ (a < b → c = 0) := by
  have : b ≤ a ∨ a < b := le_or_gt b a
  rcases this with (hxy | hxy)
  · have : ∃ c, a = b + c := exists_add_of_le hxy
    rcases this with ⟨c, rfl⟩
    simp [hxy]
  · simp [hxy]

noncomputable def sub (a b : V) : V := Classical.choose! (sub_existsUnique a b)

noncomputable scoped instance : Sub V := ⟨sub⟩

lemma sub_spec_of_ge (h : a ≥ b) : a = b + (a - b) := (Classical.choose!_spec (sub_existsUnique a b)).1 h

lemma sub_spec_of_lt (h : a < b) : a - b = 0 := (Classical.choose!_spec (sub_existsUnique a b)).2 h

lemma sub_eq_iff : c = a - b ↔ ((a ≥ b → a = b + c) ∧ (a < b → c = 0)) := Classical.choose!_eq_iff_right (sub_existsUnique a b)

@[simp] lemma sub_le_self (a b : V) : a - b ≤ a := by
  have : b ≤ a ∨ a < b := le_or_gt b a
  rcases this with (hxy | hxy) <;> simp
  · simpa [← sub_spec_of_ge hxy] using show a - b ≤ b + (a - b) from le_add_self
  · simp [sub_spec_of_lt hxy]

open FirstOrder.Arithmetic.HierarchySymbol.Definable

def _root_.LO.FirstOrder.Arithmetic.subDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “z x y. (x ≥ y → x = y + z) ∧ (x < y → z = 0)”

instance sub_defined : 𝚺₀-Function₂ ((· - ·) : V → V → V) via subDef := .mk <| by intro v; simp [FirstOrder.Arithmetic.subDef, sub_eq_iff]

instance sub_definable (ℌ : HierarchySymbol) : ℌ.DefinableFunction₂ ((· - ·) : V → V → V) := sub_defined.to_definable₀

instance sub_polybounded : Bounded₂ ((· - ·) : V → V → V) := ⟨#0, λ _ ↦ by simp⟩

@[simp] lemma sub_self (a : V) : a - a = 0 :=
  add_eq_left.mp (sub_spec_of_ge (a := a) (b := a) (by rfl)).symm

lemma sub_spec_of_le (h : a ≤ b) : a - b = 0 := by
  rcases lt_or_eq_of_le h with (lt | rfl) <;> simp [sub_spec_of_lt, *]

lemma sub_add_self_of_le (h : b ≤ a) : a - b + b = a := by symm; rw [add_comm]; exact sub_spec_of_ge h

lemma add_tsub_self_of_le (h : b ≤ a) : b + (a - b) = a := by symm; exact sub_spec_of_ge h

@[simp] lemma add_sub_self : (a + b) - b = a := by
  symm; simpa [add_comm b] using sub_spec_of_ge (show b ≤ a + b from le_add_self)

@[simp] lemma add_sub_self' : (b + a) - b = a := by simp [add_comm]

@[simp] lemma zero_sub (a : V) : 0 - a = 0 := sub_spec_of_le (by simp)

@[simp] lemma sub_zero (a : V) : a - 0 = a := by
  simpa using sub_add_self_of_le (show 0 ≤ a from zero_le a)

lemma sub_remove_left (e : a = b + c) : a - c = b := by simp [e]

lemma sub_sub : a - b - c = a - (b + c) := by
  by_cases ha : b + c ≤ a
  · exact sub_remove_left <| sub_remove_left <| by
      simp [add_assoc, show c + b = b + c from add_comm _ _, sub_add_self_of_le, ha]
  · suffices a - b - c = 0 by simpa [sub_spec_of_lt (show a < b + c from not_le.mp ha)]
    by_cases hc : c ≤ a - b
    · by_cases hb : b ≤ a
      · have : a < a := calc
          a < b + c       := not_le.mp ha
          _ ≤ b + (a - b) := by simp [hc]
          _ = a           := add_tsub_self_of_le hb
        simp at this
      · simp [show a - b = 0 from sub_spec_of_lt (not_le.mp hb)]
    · exact sub_spec_of_lt (not_le.mp hc)

@[simp] lemma pos_sub_iff_lt : 0 < a - b ↔ b < a :=
  ⟨by contrapose; simpa using sub_spec_of_le,
   by intro h; by_contra hs
      have : a = b := by
        simpa [show a - b = 0 by simpa using hs] using sub_spec_of_ge (show b ≤ a from LT.lt.le h)
      simp [this] at h⟩

@[simp] lemma sub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b :=
  not_iff_not.mp (by simp [←pos_iff_ne_zero])

instance : OrderedSub V where
  tsub_le_iff_right := by
    intro a b c
    by_cases h : b ≤ a
    · calc
        a - b ≤ c ↔ (a - b) + b ≤ c + b := by simp
        _         ↔ a ≤ c + b           := by rw [sub_add_self_of_le h]
    · suffices a ≤ c + b by simpa [sub_spec_of_lt (show a < b from by simpa using h)]
      exact le_trans (le_of_lt <| show a < b from by simpa using h) (by simp)

lemma pred_lt_self_of_pos (h : 0 < a) : a - 1 < a := by
  rcases zero_or_succ a with (rfl | ⟨a, rfl⟩)
  · simp_all
  · simp

protected lemma tsub_lt_iff_left (h : b ≤ a) : a - b < c ↔ a < c + b := AddLECancellable.tsub_lt_iff_right (add_le_cancel b) h

lemma sub_mul (h : b ≤ a) : (a - b) * c = a * c - b * c := by
  have : a = (a - b) + b := (tsub_eq_iff_eq_add_of_le h).mp rfl
  calc
    (a - b) * c = (a - b) * c + b * c - b * c := by simp
    _           = (a - b + b) * c - b * c     := by simp [add_mul]
    _           = a * c - b * c               := by simp [sub_add_self_of_le h]

lemma mul_sub (h : b ≤ a) : c * (a - b) = c * a - c * b := by simp [mul_comm c, sub_mul, h]

lemma add_sub_of_le (h : c ≤ b) (a : V) : a + b - c = a + (b - c) := add_tsub_assoc_of_le h a

lemma sub_succ_add_succ {x y : V} (h : y < x) (z) : x - (y + 1) + (z + 1) = x - y + z := calc
  x - (y + 1) + (z + 1) = x - (y + 1) + 1 + z := by simp [add_assoc, add_comm]
  _                     = x - y - 1 + 1 + z   := by simp [sub_sub]
  _                     = x - y + z           := by
    simp [show x - y - 1 + 1 = x - y from sub_add_self_of_le <| one_le_of_zero_lt _ <| pos_sub_iff_lt.mpr h]

lemma le_sub_one_of_lt {a b : V} (h : a < b) : a ≤ b - 1 := by
  have : 1 ≤ b := one_le_of_zero_lt _ (pos_of_gt h)
  simp [le_iff_lt_succ, sub_add_self_of_le this, h]

instance : AddCancelCommMonoid V where
 add_left_cancel x y z e := by simpa using congr_arg (· - x) e

end sub

/-! ### Divisibility -/

section Dvd

lemma le_mul_self_of_pos_left (hy : 0 < b) : a ≤ b * a := by
  have : 1 * a ≤ b * a := mul_le_mul_of_nonneg_right (one_le_of_zero_lt b hy) (by simp)
  simpa using this

lemma le_mul_self_of_pos_right (hy : 0 < b) : a ≤ a * b := by
  simpa [mul_comm a b] using le_mul_self_of_pos_left hy

open Classical

lemma dvd_iff_bounded {a b : V} : a ∣ b ↔ ∃ c ≤ b, b = a * c := by
  by_cases hx : a = 0
  · simp [hx, show ∃ x, x ≤ b from ⟨0, by simp⟩]
  · constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, le_mul_self_of_pos_left (pos_iff_ne_zero.mpr hx), rfl⟩
    · rintro ⟨c, hz, rfl⟩; exact dvd_mul_right a c

def _root_.LO.FirstOrder.Arithmetic.dvd : 𝚺₀.Semisentence 2 :=
  .mkSigma “x y. ∃ z <⁺ y, y = x * z”

instance dvd_defined : 𝚺₀-Relation (fun a b : V ↦ a ∣ b) via dvd := .mk fun v ↦ by simp [dvd_iff_bounded, dvd]

instance dvd_definable (ℌ : HierarchySymbol) : ℌ.DefinableRel ((· ∣ ·) : V → V → Prop) := dvd_defined.to_definable₀

section

syntax:45 first_order_term:45 " ∣ " first_order_term:0 : first_order_formula

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ∣ $u:first_order_term]) => `(⤫formula(lit)[ $binders* | $fbinders* | !dvd.val $t $u])

end

end Dvd

lemma le_of_dvd (h : 0 < b) : a ∣ b → a ≤ b := by
  rintro ⟨c, rfl⟩
  exact le_mul_self_of_pos_right
    (pos_iff_ne_zero.mpr (show c ≠ 0 from by rintro rfl; simp at h))

lemma not_dvd_of_lt (pos : 0 < b) : b < a → ¬a ∣ b := by
  intro hb h; exact not_le.mpr hb (le_of_dvd pos h)

lemma dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  intro hx hy
  rcases show a = 0 ∨ 0 < a from eq_zero_or_pos a with (rfl | ltx)
  · simp [show b = 0 from by simpa using hx]
  · rcases show b = 0 ∨ 0 < b from eq_zero_or_pos b with (rfl | lty)
    · simp [show a = 0 from by simpa using hy]
    · exact le_antisymm (le_of_dvd lty hx) (le_of_dvd ltx hy)

lemma dvd_one_iff : a ∣ 1 ↔ a = 1 := ⟨by { intro hx; exact dvd_antisymm hx (by simp) }, by rintro rfl; simp⟩

theorem units_eq_one (u : Vˣ) : u = 1 :=
  Units.ext <| dvd_one_iff.mp ⟨u.inv, u.val_inv.symm⟩

@[simp] lemma unit_iff_eq_one {a : V} : IsUnit a ↔ a = 1 :=
  ⟨by rintro ⟨u, rfl⟩; simp [units_eq_one u], by rintro rfl; simp⟩

/-! ### Prime number -/

section Prime

instance : CancelCommMonoidWithZero V where

open Classical in
lemma eq_one_or_eq_of_dvd_of_prime {p a : V} (pp : Prime p) (hxp : a ∣ p) : a = 1 ∨ a = p := by
  have : p ∣ a ∨ a ∣ 1 := Prime.left_dvd_or_dvd_right_of_dvd_mul pp (show a ∣ p * 1 from by simpa using hxp)
  rcases this with (hx | hx)
  · right; exact dvd_antisymm hxp hx
  · left; exact dvd_one_iff.mp hx

def IsPrime (a : V) : Prop := 1 < a ∧ ∀ b ≤ a, b ∣ a → b = 1 ∨ b = a
-- TODO: prove IsPrime a ↔ Prime a

def _root_.LO.FirstOrder.Arithmetic.isPrime : 𝚺₀.Semisentence 1 :=
  .mkSigma “x. 1 < x ∧ ∀ y <⁺ x, !dvd.val y x → y = 1 ∨ y = x”

instance isPrime_defined : 𝚺₀-Predicate (λ a : V ↦ IsPrime a) via isPrime := .mk fun v ↦ by
  simp [Semiformula.eval_substs, Matrix.comp_vecCons', Matrix.constant_eq_singleton, IsPrime, isPrime]

end Prime

/-! ### Minimum -/

section min

def min.dfn : 𝚺₀.Semisentence 3 :=
  .mkSigma “z x y. (x ≤ y → z = x) ∧ (x ≥ y → z = y)”

set_option linter.flexible false in
instance min_defined : 𝚺₀-Function₂[V] min via min.dfn := .mk fun v ↦ by
  simp [min.dfn]; grind

instance min_definable (ℌ) : ℌ-Function₂[V] min := min_defined.to_definable₀

instance min_polybounded : Bounded₂ (min : V → V → V) := ⟨#0, λ _ ↦ by simp⟩

end min

/-! ### Maximum -/

section max

def max.dfn : 𝚺₀.Semisentence 3 :=
  .mkSigma “z x y. (x ≥ y → z = x) ∧ (x ≤ y → z = y)”

set_option linter.flexible false in
instance max_defined : 𝚺₀-Function₂[V] max via max.dfn := .mk fun v ↦ by simp [max.dfn]; grind

instance max_definable (Γ) : Γ-Function₂[V] max := max_defined.to_definable₀

instance max_polybounded : Bounded₂ (max : V → V → V) := ⟨‘#0 + #1’, λ v ↦ by simp⟩

end max

end LO.FirstOrder.Arithmetic
