import Foundation.FirstOrder.Arithmetic.Basic
import Foundation.FirstOrder.R0.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Order.Sub.Basic

/-!
# Theory $\mathsf{PA^-}$

-/

namespace LO

open FirstOrder

namespace PeanoMinus.Axiom

abbrev       addZero : SyntacticFormula ℒₒᵣ := “x | x + 0 = x”
abbrev      addAssoc : SyntacticFormula ℒₒᵣ := “x y z | (x + y) + z = x + (y + z)”
abbrev       addComm : SyntacticFormula ℒₒᵣ := “x y | x + y = y + x”
abbrev     addEqOfLt : SyntacticFormula ℒₒᵣ := “x y | x < y → ∃ z, x + z = y”
abbrev        zeroLe : SyntacticFormula ℒₒᵣ := “x | 0 ≤ x”
abbrev     zeroLtOne : SyntacticFormula ℒₒᵣ := “0 < 1”
abbrev oneLeOfZeroLt : SyntacticFormula ℒₒᵣ := “x | 0 < x → 1 ≤ x”
abbrev      addLtAdd : SyntacticFormula ℒₒᵣ := “x y z | x < y → x + z < y + z”
abbrev       mulZero : SyntacticFormula ℒₒᵣ := “x | x * 0 = 0”
abbrev        mulOne : SyntacticFormula ℒₒᵣ := “x | x * 1 = x”
abbrev      mulAssoc : SyntacticFormula ℒₒᵣ := “x y z | (x * y) * z = x * (y * z)”
abbrev       mulComm : SyntacticFormula ℒₒᵣ := “x y | x * y = y * x”
abbrev      mulLtMul : SyntacticFormula ℒₒᵣ := “x y z | x < y ∧ 0 < z → x * z < y * z”
abbrev         distr : SyntacticFormula ℒₒᵣ := “x y z | x * (y + z) = x * y + x * z”
abbrev      ltIrrefl : SyntacticFormula ℒₒᵣ := “x | x ≮ x”
abbrev       ltTrans : SyntacticFormula ℒₒᵣ := “x y z | x < y ∧ y < z → x < z”
abbrev         ltTri : SyntacticFormula ℒₒᵣ := “x y | x < y ∨ x = y ∨ x > y”

end PeanoMinus.Axiom

inductive PeanoMinus : ArithmeticTheory
  | equal         : ∀ φ ∈ 𝐄𝐐, PeanoMinus φ
  | addZero       : PeanoMinus PeanoMinus.Axiom.addZero
  | addAssoc      : PeanoMinus PeanoMinus.Axiom.addAssoc
  | addComm       : PeanoMinus PeanoMinus.Axiom.addComm
  | addEqOfLt     : PeanoMinus PeanoMinus.Axiom.addEqOfLt
  | zeroLe        : PeanoMinus PeanoMinus.Axiom.zeroLe
  | zeroLtOne     : PeanoMinus PeanoMinus.Axiom.zeroLtOne
  | oneLeOfZeroLt : PeanoMinus PeanoMinus.Axiom.oneLeOfZeroLt
  | addLtAdd      : PeanoMinus PeanoMinus.Axiom.addLtAdd
  | mulZero       : PeanoMinus PeanoMinus.Axiom.mulZero
  | mulOne        : PeanoMinus PeanoMinus.Axiom.mulOne
  | mulAssoc      : PeanoMinus PeanoMinus.Axiom.mulAssoc
  | mulComm       : PeanoMinus PeanoMinus.Axiom.mulComm
  | mulLtMul      : PeanoMinus PeanoMinus.Axiom.mulLtMul
  | distr         : PeanoMinus PeanoMinus.Axiom.distr
  | ltIrrefl      : PeanoMinus PeanoMinus.Axiom.ltIrrefl
  | ltTrans       : PeanoMinus PeanoMinus.Axiom.ltTrans
  | ltTri         : PeanoMinus PeanoMinus.Axiom.ltTri

notation "𝐏𝐀⁻" => PeanoMinus

namespace PeanoMinus

open FirstOrder Arithmetic Language

@[simp] lemma finite : Set.Finite 𝐏𝐀⁻ := by
  have : 𝐏𝐀⁻ =
    𝐄𝐐 ∪
    { Axiom.addZero,
      Axiom.addAssoc,
      Axiom.addComm,
      Axiom.addEqOfLt,
      Axiom.zeroLe,
      Axiom.zeroLtOne,
      Axiom.oneLeOfZeroLt,
      Axiom.addLtAdd,
      Axiom.mulZero,
      Axiom.mulOne,
      Axiom.mulAssoc,
      Axiom.mulComm,
      Axiom.mulLtMul,
      Axiom.distr,
      Axiom.ltIrrefl,
      Axiom.ltTrans,
      Axiom.ltTri } := by
    ext φ; constructor
    · rintro ⟨⟩
      case equal => left; assumption
      case addZero => tauto
      case addAssoc => tauto
      case addComm => tauto
      case addEqOfLt => tauto
      case zeroLe => tauto
      case zeroLtOne => tauto
      case oneLeOfZeroLt => tauto
      case addLtAdd => tauto
      case mulZero => tauto
      case mulOne => tauto
      case mulAssoc => tauto
      case mulComm => tauto
      case mulLtMul => tauto
      case distr => tauto
      case ltIrrefl => tauto
      case ltTrans => tauto
      case ltTri => tauto
    · rintro (h | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact equal _ h
      · exact addZero
      · exact addAssoc
      · exact addComm
      · exact addEqOfLt
      · exact zeroLe
      · exact zeroLtOne
      · exact oneLeOfZeroLt
      · exact addLtAdd
      · exact mulZero
      · exact mulOne
      · exact mulAssoc
      · exact mulComm
      · exact mulLtMul
      · exact distr
      · exact ltIrrefl
      · exact ltTrans
      · exact ltTri
  rw [this]; simp only [Set.finite_union, FirstOrder.Theory.EqAxiom.finite, true_and]
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.Finite.insert
  apply Set.finite_singleton

set_option linter.flexible false in
@[simp] instance : ℕ ⊧ₘ* 𝐏𝐀⁻ := ⟨by
  intro σ h
  rcases h <;> simp [models_def]
  case addAssoc => intro f; exact add_assoc _ _ _
  case addComm  => intro f; exact add_comm _ _
  case mulAssoc => intro f; exact mul_assoc _ _ _
  case mulComm  => intro f; exact mul_comm _ _
  case addEqOfLt => intro f h; exact ⟨f 1 - f 0, Nat.add_sub_of_le (le_of_lt h)⟩
  case oneLeOfZeroLt => intro n hn; exact hn
  case mulLtMul => rintro f h hl; exact (mul_lt_mul_right hl).mpr h
  case distr => intro f; exact Nat.mul_add _ _ _
  case ltTrans => intro f; exact Nat.lt_trans
  case ltTri => intro f; exact Nat.lt_trichotomy _ _
  case equal h =>
    have : ℕ ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h⟩

instance : 𝐄𝐐 ⪯ 𝐏𝐀⁻ := Entailment.WeakerThan.ofSubset <| fun φ hp ↦ PeanoMinus.equal φ hp

variable {M : Type*} [ORingStruc M]

scoped instance : LE M := ⟨fun x y => x = y ∨ x < y⟩

lemma le_def {x y : M} : x ≤ y ↔ x = y ∨ x < y := iff_of_eq rfl

variable [M ⊧ₘ* 𝐏𝐀⁻]

protected lemma add_zero (x : M) : x + 0 = x := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.addZero (fun _ ↦ x)

protected lemma add_assoc (x y z : M) : (x + y) + z = x + (y + z) := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.addAssoc (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma add_comm (x y : M) : x + y = y + x := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.addComm (x :>ₙ fun _ ↦ y)

lemma add_eq_of_lt (x y : M) : x < y → ∃ z, x + z = y := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.addEqOfLt (x :>ₙ fun _ ↦ y)

@[simp] protected lemma zero_le (x : M) : 0 ≤ x := by
  simpa [models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M PeanoMinus.zeroLe (fun _ ↦ x)

lemma zero_lt_one : (0 : M) < 1 := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.zeroLtOne

lemma one_le_of_zero_lt (x : M) : 0 < x → 1 ≤ x := by
  simpa [models_iff, Structure.le_iff_of_eq_of_lt] using ModelsTheory.models M PeanoMinus.oneLeOfZeroLt (fun _ ↦ x)

lemma add_lt_add (x y z : M) : x < y → x + z < y + z := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.addLtAdd (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma mul_zero (x : M) : x * 0 = 0 := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.mulZero (fun _ ↦ x)

protected lemma mul_one (x : M) : x * 1 = x := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.mulOne (fun _ ↦ x)

protected lemma mul_assoc (x y z : M) : (x * y) * z = x * (y * z) := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.mulAssoc (x :>ₙ y :>ₙ fun _ ↦ z)

protected lemma mul_comm (x y : M) : x * y = y * x := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.mulComm (x :>ₙ fun _ ↦ y)

lemma mul_lt_mul (x y z : M) : x < y → 0 < z → x * z < y * z := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.mulLtMul (x :>ₙ y :>ₙ fun _ ↦ z)

lemma mul_add_distr (x y z : M) : x * (y + z) = x * y + x * z := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.distr (x :>ₙ y :>ₙ fun _ ↦ z)

lemma lt_irrefl (x : M) : ¬x < x := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.ltIrrefl (fun _ ↦ x)

protected lemma lt_trans (x y z : M) : x < y → y < z → x < z := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.ltTrans (x :>ₙ y :>ₙ fun _ ↦ z)

lemma lt_tri (x y : M) : x < y ∨ x = y ∨ y < x := by
  simpa [models_iff] using ModelsTheory.models M PeanoMinus.ltTri (x :>ₙ fun _ ↦ y)

scoped instance : AddCommMonoid M where
  add_assoc := PeanoMinus.add_assoc
  zero_add  := fun x ↦ PeanoMinus.add_comm x 0 ▸ PeanoMinus.add_zero x
  add_zero  := PeanoMinus.add_zero
  add_comm  := PeanoMinus.add_comm
  nsmul := nsmulRec

scoped instance : CommMonoid M where
  mul_assoc := PeanoMinus.mul_assoc
  one_mul   := fun x ↦ PeanoMinus.mul_comm x 1 ▸ PeanoMinus.mul_one x
  mul_one   := PeanoMinus.mul_one
  mul_comm  := PeanoMinus.mul_comm

noncomputable scoped instance : LinearOrder M where
  le_refl := fun x ↦ Or.inl (by simp)
  le_trans := by
    rintro x y z (rfl | hx) (rfl | hy)
    · simp [le_def]
    · simp [le_def, *]
    · simp [le_def, *]
    · exact Or.inr (PeanoMinus.lt_trans _ _ _ hx hy)
  le_antisymm := by
    rintro x y (rfl | hx) <;> try simp
    rintro (rfl | hy) <;> try simp
    exact False.elim <| PeanoMinus.lt_irrefl _ <| PeanoMinus.lt_trans _ _ _ hx hy
  le_total := by
    intro x y
    rcases PeanoMinus.lt_tri x y with (h | rfl | h) <;> simp [*, le_def]
  lt_iff_le_not_ge := fun x y ↦
    ⟨ fun h => ⟨Or.inr h, by
      simp only [le_def]; rintro (rfl | h')
      · exact lt_irrefl y h
      · exact lt_irrefl _ (PeanoMinus.lt_trans _ _ _ h h') ⟩,
     by simp only [le_def, not_or, and_imp]
        rintro (rfl | h) <;> simp [*] ⟩
  toDecidableLE := fun _ _ => Classical.dec _

protected lemma zero_mul : ∀ x : M, 0 * x = 0 := fun x => by simpa [mul_comm] using PeanoMinus.mul_zero x

scoped instance : CommSemiring M where
  left_distrib := PeanoMinus.mul_add_distr
  right_distrib := fun x y z ↦ by simp [mul_comm _ z, mul_add_distr]
  zero_mul := PeanoMinus.zero_mul
  mul_zero := PeanoMinus.mul_zero

scoped instance : IsStrictOrderedRing M where
  add_le_add_left := by
    rintro x y (rfl | h) z
    · simp [add_comm z]
    · simp only [add_comm z]; exact Or.inr (add_lt_add x y z h)
  le_of_add_le_add_left := by
    rintro x y z h
    have : y ≤ z ∨ z < y := le_or_gt y z
    rcases this with (hyz | hyz)
    · exact hyz
    · have : x + z < x + y := by simpa [add_comm] using add_lt_add z y x hyz
      exact False.elim (lt_iff_not_ge.mp this h)
  zero_le_one := Or.inr zero_lt_one
  exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩
  mul_lt_mul_of_pos_left := by
    rintro x y z h hz; { simpa [mul_comm z] using mul_lt_mul x y z h hz }
  mul_lt_mul_of_pos_right := by
    rintro x y z h hz; { simpa using mul_lt_mul x y z h hz }

scoped instance : CanonicallyOrderedAdd M where
  exists_add_of_le := by
    rintro x y (rfl | h)
    · exact ⟨0, by simp⟩
    · simpa [eq_comm] using add_eq_of_lt x y h
  le_self_add := by intro x y; simp

scoped instance : IsOrderedAddMonoid M where
  add_le_add_left _ _ h z := (add_le_add_iff_left z).mpr h

lemma numeral_eq_natCast : (n : ℕ) → (ORingStruc.numeral n : M) = n
  |     0 => rfl
  |     1 => by simp
  | n + 2 => by simp [ORingStruc.numeral, numeral_eq_natCast (n + 1), add_assoc, one_add_one_eq_two]

lemma not_neg (x : M) : ¬x < 0 := by simp

lemma eq_succ_of_pos {x : M} (h : 0 < x) : ∃ y, x = y + 1 := by
  rcases le_iff_exists_add.mp (one_le_of_zero_lt x h) with ⟨y, rfl⟩
  exact ⟨y, add_comm 1 y⟩

lemma le_iff_lt_succ {x y : M} : x ≤ y ↔ x < y + 1 :=
  ⟨by intro h; exact lt_of_le_of_lt h (lt_add_one y),
   fun h => by
    rcases lt_iff_exists_add.mp h with ⟨z, hz, h⟩
    rcases eq_succ_of_pos hz with ⟨z', rfl⟩
    have : y = x + z' := by simpa [←add_assoc] using h
    simp [this]⟩

lemma eq_nat_of_lt_nat : ∀ {n : ℕ} {x : M}, x < n → ∃ m : ℕ, x = m
  |     0, x, hx => by simp [not_neg] at hx
  | n + 1, x, hx => by
    have : x ≤ n := by simpa [le_iff_lt_succ] using hx
    rcases this with (rfl | hx)
    · exact ⟨n, rfl⟩
    · exact eq_nat_of_lt_nat hx

lemma eq_nat_of_le_nat {n : ℕ} {x : M} : x ≤ n → ∃ m : ℕ, x = m := fun h ↦ by
  have : x < ↑(n + 1) := by simpa [←le_iff_lt_succ] using h
  exact eq_nat_of_lt_nat this

instance : M ⊧ₘ* 𝐑₀ := modelsTheory_iff.mpr <| by
  intro φ h
  rcases h
  case equal h =>
    have : M ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h
  case Ω₁ n m =>
    simp [models_iff, numeral_eq_natCast]
  case Ω₂ n m =>
    simp [models_iff, numeral_eq_natCast]
  case Ω₃ n m h =>
    simp [models_iff, numeral_eq_natCast, h]
  case Ω₄ n =>
    suffices ∀ x : M, x < ↑n ↔ ∃ i < n, x = ↑i by simpa [models_iff, numeral_eq_natCast]
    intro x
    constructor
    · intro hx; rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩; exact ⟨x, by simpa using hx, by simp⟩
    · rintro ⟨i, hi, rfl⟩; simp [hi]

variable {a b c : M}

instance : Nonempty M := ⟨0⟩

@[simp] lemma numeral_two_eq_two : (ORingStruc.numeral 2 : M) = 2 := by simp [numeral_eq_natCast]

@[simp] lemma numeral_three_eq_three : (ORingStruc.numeral 3 : M) = 3 := by simp [numeral_eq_natCast]

@[simp] lemma numeral_four_eq_four : (ORingStruc.numeral 4 : M) = 4 := by simp [numeral_eq_natCast]

lemma lt_succ_iff_le {x y : M} : x < y + 1 ↔ x ≤ y := Iff.symm le_iff_lt_succ

lemma lt_iff_succ_le : a < b ↔ a + 1 ≤ b := by simp [le_iff_lt_succ]

lemma succ_le_iff_lt : a + 1 ≤ b ↔ a < b := by simp [le_iff_lt_succ]

lemma pos_iff_one_le : 0 < a ↔ 1 ≤ a := by simp [lt_iff_succ_le]

lemma one_lt_iff_two_le : 1 < a ↔ 2 ≤ a := by simp [lt_iff_succ_le, one_add_one_eq_two]

@[simp] lemma not_nonpos (a : M) : ¬a < 0 := by simp

lemma lt_two_iff_le_one : a < 2 ↔ a ≤ 1 := by
  simp [lt_iff_succ_le,
    show a + 1 ≤ 2 ↔ a ≤ 1 from by
      rw [show (2 : M) = 1 + 1 from one_add_one_eq_two.symm]; exact add_le_add_iff_right 1]

@[simp] lemma lt_one_iff_eq_zero : a < 1 ↔ a = 0 := ⟨by
  intro hx
  have : a ≤ 0 := by exact le_iff_lt_succ.mpr (show a < 0 + 1 from by simpa using hx)
  exact nonpos_iff_eq_zero.mp this,
  by rintro rfl; exact zero_lt_one⟩

lemma le_one_iff_eq_zero_or_one : a ≤ 1 ↔ a = 0 ∨ a = 1 :=
  ⟨by intro h; rcases h with (rfl | ltx)
      · simp
      · simp [show a = 0 from by simpa using ltx],
   by rintro (rfl | rfl) <;> simp⟩

lemma le_two_iff_eq_zero_or_one_or_two : a ≤ 2 ↔ a = 0 ∨ a = 1 ∨ a = 2 :=
  ⟨by intro h; rcases h with (rfl | lt)
      · simp
      · rcases lt_two_iff_le_one.mp lt with (rfl | lt)
        · simp
        · simp [show a = 0 from by simpa using lt],
   by rintro (rfl | rfl | rfl) <;> simp⟩

lemma le_three_iff_eq_zero_or_one_or_two_or_three : a ≤ 3 ↔ a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 :=
  ⟨by intro h; rcases h with (rfl | lt)
      · simp
      · have : a ≤ 2 := by simpa [←le_iff_lt_succ, ←two_add_one_eq_three] using lt
        rcases this with (rfl| lt)
        · simp
        · rcases lt_two_iff_le_one.mp lt with (rfl | lt)
          · simp
          · simp [show a = 0 from by simpa using lt],
   by rintro (rfl | rfl | rfl | rfl) <;> simp [←two_add_one_eq_three]⟩

lemma two_mul_two_eq_four : 2 * 2 = (4 : M) := by
  rw [←one_add_one_eq_two, mul_add, add_mul, mul_one, ←add_assoc,
    one_add_one_eq_two, two_add_one_eq_three, three_add_one_eq_four]

lemma two_pow_two_eq_four : 2 ^ 2 = (4 : M) := by
  simp [sq, two_mul_two_eq_four]

lemma two_pos : (0 : M) < 2 := by exact _root_.two_pos

@[simp] lemma le_mul_self (a : M) : a ≤ a * a := by
  have : 0 ≤ a := by exact zero_le a
  rcases this with (rfl | pos) <;> simp [*, ←pos_iff_one_le]

@[simp] lemma le_sq (a : M) : a ≤ a ^ 2 := by simp [sq]

@[simp] lemma sq_le_sq : a ^ 2 ≤ b ^ 2 ↔ a ≤ b := by simpa [sq] using Iff.symm <| mul_self_le_mul_self_iff (by simp) (by simp)

@[simp] lemma sq_lt_sq : a ^ 2 < b ^ 2 ↔ a < b := by simpa [sq] using Iff.symm <| mul_self_lt_mul_self_iff (by simp) (by simp)

lemma le_mul_of_pos_right (h : 0 < b) : a ≤ a * b := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp h)

lemma le_mul_of_pos_left (h : 0 < b) : a ≤ b * a := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp h)

@[simp] lemma le_two_mul_left : a ≤ 2 * a := le_mul_of_pos_left (by simp)

lemma lt_mul_of_pos_of_one_lt_right (pos : 0 < a) (h : 1 < b) : a < a * b := _root_.lt_mul_of_one_lt_right pos h

lemma lt_mul_of_pos_of_one_lt_left (pos : 0 < a) (h : 1 < b) : a < b * a := _root_.lt_mul_of_one_lt_left pos h

lemma mul_le_mul_left (h : b ≤ c) : a * b ≤ a * c := mul_le_mul_of_nonneg_left h (by simp)

lemma mul_le_mul_right (h : b ≤ c) : b * a ≤ c * a := mul_le_mul_of_nonneg_right h (by simp)

theorem lt_of_mul_lt_mul_left (h : a * b < a * c) : b < c := lt_of_mul_lt_mul_of_nonneg_left h (by simp)

theorem lt_of_mul_lt_mul_right (h : b * a < c * a) : b < c := lt_of_mul_lt_mul_of_nonneg_right h (by simp)

lemma pow_three (x : M) : x^3 = x * x * x := by rw [← two_add_one_eq_three, pow_add, sq]; simp

lemma pow_four (x : M) : x^4 = x * x * x * x := by rw [← three_add_one_eq_four, pow_add, pow_three]; simp

lemma pow_four_eq_sq_sq (x : M) : x^4 = (x^2)^2 := by simp [pow_four, sq, mul_assoc]

scoped instance : CovariantClass M M (· * ·) (· ≤ ·) := ⟨by intro; exact mul_le_mul_left⟩

scoped instance : CovariantClass M M (· + ·) (· ≤ ·) := ⟨by intro; simp⟩

scoped instance : CovariantClass M M (Function.swap (· * ·)) (· ≤ ·) := ⟨by intro; exact mul_le_mul_right⟩

@[simp] lemma one_lt_mul_self_iff {a : M} : 1 < a * a ↔ 1 < a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_le_one' h h).mtr, fun h ↦ one_lt_mul'' h h⟩

@[simp] lemma opos_lt_sq_pos_iff {a : M} : 0 < a^2 ↔ 0 < a := by simp [sq, pos_iff_ne_zero]

@[simp] lemma one_lt_sq_iff {a : M} : 1 < a^2 ↔ 1 < a := by simp [sq]

@[simp] lemma mul_self_eq_one_iff {a : M} : a * a = 1 ↔ a = 1 :=
  not_iff_not.mp (by simp [ne_iff_lt_or_gt])

@[simp] lemma sq_eq_one_iff {a : M} : a^2 = 1 ↔ a = 1 := by simp [sq]

lemma lt_square_of_lt {a : M} (pos : 1 < a) : a < a^2 := by
  rw [sq]; apply lt_mul_self pos

lemma two_mul_le_sq {i : M} (h : 2 ≤ i) : 2 * i ≤ i ^ 2 := by simpa [sq] using mul_le_mul_right h

lemma two_mul_le_sq_add_one (i : M) : 2 * i ≤ i ^ 2 + 1 := by
  rcases zero_le i with (rfl | pos)
  · simp
  · rcases pos_iff_one_le.mp pos with (rfl | lt)
    · simp [one_add_one_eq_two]
    · exact le_trans (two_mul_le_sq (one_lt_iff_two_le.mp lt)) (by simp)

lemma two_mul_lt_sq {i : M} (h : 2 < i) : 2 * i < i ^ 2 := by
  simpa [sq] using (mul_lt_mul_right (show 0 < i from pos_of_gt h)).mpr h

lemma succ_le_double_of_pos {a : M} (h : 0 < a) : a + 1 ≤ 2 * a := by
  simpa [two_mul] using pos_iff_one_le.mp h

lemma two_mul_add_one_lt_two_mul_of_lt (h : a < b) : 2 * a + 1 < 2 * b := calc
  2 * a + 1 < 2 * (a + 1) := by simp [mul_add]
  _         ≤ 2 * b       := by simp [←lt_iff_succ_le, h]

@[simp] lemma le_add_add_left (a b c : M) : a ≤ a + b + c := by simp [add_assoc]

@[simp] lemma le_add_add_right (a b c : M) : b ≤ a + b + c := by simp [add_right_comm a b c]

lemma add_le_cancel (a : M) : AddLECancellable a := by intro b c; simp

open FirstOrder FirstOrder.Semiterm

@[simp] lemma val_npow (k : ℕ) (a : M) :
    (Operator.npow ℒₒᵣ k).val ![a] = a ^ k := by
  induction k
  case zero =>
    simp [Operator.npow_zero, Operator.val_comp, Matrix.empty_eq]
  case succ k IH =>
    simp [Operator.npow_succ, Operator.val_comp]
    simp [Matrix.fun_eq_vec_two, pow_succ]
    simp [IH]

instance : Structure.Monotone ℒₒᵣ M := ⟨
  fun {k} f v₁ v₂ h ↦
  match k, f with
  | 0, Language.Zero.zero => by rfl
  | 0,   Language.One.one => by rfl
  | 2,   Language.Add.add => add_le_add (h 0) (h 1)
  | 2,   Language.Mul.mul => mul_le_mul (h 0) (h 1) (by simp) (by simp)⟩

@[simp] lemma zero_ne_add_one (x : M) : 0 ≠ x + (1 : M) := ne_of_lt (by simp)

@[simp] lemma nat_cast_inj {n m : ℕ} : (n : M) = (m : M) ↔ n = m := by
  induction' n with n ih
  · cases m <;> simp
  · cases m <;> simp

@[simp] lemma coe_coe_lt {n m : ℕ} : (n : M) < (m : M) ↔ n < m := by
  induction' n with n ih
  · cases m <;> simp
  · cases m <;> simp

lemma coe_add_one (x : ℕ) : ((x + 1 : ℕ) : M) = (x : M) + 1 := by simp

lemma eq_fin_of_lt_nat {n : ℕ} {x : M} (hx : x < (n : M)) : ∃ i : Fin n, x = i := by
  rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩
  exact ⟨⟨x, by simpa using hx⟩, by simp⟩

variable (M)

abbrev natCast : NatCast M := inferInstance

variable {M}

@[simp] lemma natCast_nat (n : ℕ) : @Nat.cast ℕ (natCast ℕ) n = n := by
  induction n
  · rfl
  · unfold natCast; rw [coe_add_one]; simp [*]

variable {T : ArithmeticTheory} [𝐏𝐀⁻ ⪯ T]

instance : 𝐑₀ ⪯ 𝐏𝐀⁻ := oRing_weakerThan_of.{0} _ _ fun _ _ _ ↦ inferInstance

instance : 𝐑₀ ⪱ 𝐏𝐀⁻ :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable
    R0.unprovable_addZero (Entailment.by_axm _ PeanoMinus.addZero)

instance (M : Type*) [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻] : M ⊧ₘ* 𝐑₀ := models_of_subtheory (T := 𝐏𝐀⁻) inferInstance

end PeanoMinus

end LO
