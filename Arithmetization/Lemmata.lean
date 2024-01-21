import Arithmetization.Vorspiel.Vorspiel
import Mathlib.Algebra.GCDMonoid.Basic

namespace LO.FirstOrder

namespace Semiterm

@[elab_as_elim]
def arithCases {n} {C : Semiterm ℒₒᵣ ξ n → Sort w}
  (hbvar : ∀ x : Fin n, C #x)
  (hfvar : ∀ x : ξ, C &x)
  (hzero : C ᵀ“0”)
  (hone  : C ᵀ“1”)
  (hadd  : ∀ (t u : Semiterm ℒₒᵣ ξ n), C ᵀ“!!t + !!u”)
  (hmul  : ∀ (t u : Semiterm ℒₒᵣ ξ n), C ᵀ“!!t * !!u”) :
    ∀ (t : Semiterm ℒₒᵣ ξ n), C t
  | #x                        => hbvar x
  | &x                        => hfvar x
  | func Language.Zero.zero _ => by
      simpa [Matrix.empty_eq, Operator.const, Operator.operator, Operator.numeral, Operator.Zero.term_eq] using hzero
  | func Language.One.one _   => by
      simpa [Matrix.empty_eq, Operator.const, Operator.operator, Operator.numeral, Operator.One.term_eq] using hone
  | func Language.Add.add v   => by
    simpa [Operator.operator, Operator.Add.term_eq, Rew.func, ←Matrix.fun_eq_vec₂] using hadd (v 0) (v 1)
  | func Language.Mul.mul v   => by
    simpa [Operator.operator, Operator.Mul.term_eq, Rew.func, ←Matrix.fun_eq_vec₂] using hmul (v 0) (v 1)

@[elab_as_elim]
def arithRec {n} {C : Semiterm ℒₒᵣ ξ n → Sort w}
  (hbvar : ∀ x : Fin n, C #x)
  (hfvar : ∀ x : ξ, C &x)
  (hzero : C ᵀ“0”)
  (hone  : C ᵀ“1”)
  (hadd  : ∀ {t u : Semiterm ℒₒᵣ ξ n}, C t → C u → C ᵀ“!!t + !!u”)
  (hmul  : ∀ {t u : Semiterm ℒₒᵣ ξ n}, C t → C u → C ᵀ“!!t * !!u”) :
    ∀ (t : Semiterm ℒₒᵣ ξ n), C t
  | #x                        => hbvar x
  | &x                        => hfvar x
  | func Language.Zero.zero _ => by
      simpa [Matrix.empty_eq, Operator.const, Operator.operator, Operator.numeral, Operator.Zero.term_eq] using hzero
  | func Language.One.one _   => by
      simpa [Matrix.empty_eq, Operator.const, Operator.operator, Operator.numeral, Operator.One.term_eq] using hone
  | func Language.Add.add v   => by
    have ih0 := arithRec hbvar hfvar hzero hone hadd hmul (v 0)
    have ih1 := arithRec hbvar hfvar hzero hone hadd hmul (v 1)
    simpa [Operator.operator, Operator.Add.term_eq, Rew.func, ←Matrix.fun_eq_vec₂] using hadd ih0 ih1
  | func Language.Mul.mul v   => by
    have ih0 := arithRec hbvar hfvar hzero hone hadd hmul (v 0)
    have ih1 := arithRec hbvar hfvar hzero hone hadd hmul (v 1)
    simpa [Operator.operator, Operator.Mul.term_eq, Rew.func, ←Matrix.fun_eq_vec₂] using hmul ih0 ih1
  termination_by arithRec _ _ _ _ _ _ t => t.complexity

end Semiterm

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

variable {a b c : M}

lemma lt_iff_succ_le : a < b ↔ a + 1 ≤ b := by simp [le_iff_lt_succ]

lemma pos_iff_one_le : 0 < a ↔ 1 ≤ a := by simp [lt_iff_succ_le]

lemma one_lt_iff_two_le : 1 < a ↔ 2 ≤ a := by simp [lt_iff_succ_le, one_add_one_eq_two]

@[simp] lemma not_nonpos (a : M) : ¬a < 0 := by simp

lemma lt_two_iff_le_one : a < 2 ↔ a ≤ 1 := by
  simp [lt_iff_succ_le,
    show a + 1 ≤ 2 ↔ a ≤ 1 from by
      rw[show (2 : M) = 1 + 1 from one_add_one_eq_two.symm]; exact add_le_add_iff_right 1]

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
   by rintro (rfl | rfl | rfl) <;> simp [one_le_two]⟩

lemma le_three_iff_eq_zero_or_one_or_two_or_three : a ≤ 3 ↔ a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 :=
  ⟨by intro h; rcases h with (rfl | lt)
      · simp
      · have : a ≤2 := by simpa [←le_iff_lt_succ, ←two_add_one_eq_three] using lt
        rcases this with (rfl| lt)
        · simp
        · rcases lt_two_iff_le_one.mp lt with (rfl | lt)
          · simp
          · simp [show a = 0 from by simpa using lt],
   by rintro (rfl | rfl | rfl | rfl) <;> simp [one_le_two, ←two_add_one_eq_three]⟩

lemma two_mul_two_eq_four : 2 * 2 = (4 : M) := by
  rw [←one_add_one_eq_two, mul_add, add_mul, mul_one, ←add_assoc,
    one_add_one_eq_two, two_add_one_eq_three, three_add_one_eq_four]

lemma two_pow_two_eq_four : 2 ^ 2 = (4 : M) := by
  simp [sq, two_mul_two_eq_four]

@[simp] lemma le_mul_self (a : M) : a ≤ a * a := by
  have : 0 ≤ a := by exact zero_le a
  rcases this with (rfl | pos) <;> simp [*, ←pos_iff_one_le]

@[simp] lemma le_sq (a : M) : a ≤ a^2 := by simp [sq]

lemma sq_le_sq_iff : a ≤ b ↔ a^2 ≤ b^2 := by simp [sq]; apply mul_self_le_mul_self_iff <;> simp

lemma sq_lt_sq_iff : a < b ↔ a^2 < b^2 := by simp [sq]; apply mul_self_lt_mul_self_iff <;> simp

lemma le_mul_of_pos_right (h : 0 < b) : a ≤ a * b := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp h)

lemma le_mul_of_pos_left (h : 0 < b) : a ≤ b * a := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp h)

@[simp] lemma le_two_mul_left : a ≤ 2 * a := le_mul_of_pos_left (by simp)

lemma lt_mul_of_pos_of_one_lt_right (pos : 0 < a) (h : 1 < b) : a < a * b := _root_.lt_mul_of_one_lt_right pos h

lemma lt_mul_of_pos_of_one_lt_left (pos : 0 < a) (h : 1 < b) : a < b * a := _root_.lt_mul_of_one_lt_left pos h

lemma mul_le_mul_left (h : b ≤ c) : a * b ≤ a * c := mul_le_mul_of_nonneg_left h (by simp)

lemma mul_le_mul_right (h : b ≤ c) : b * a ≤ c * a := mul_le_mul_of_nonneg_right h (by simp)

theorem lt_of_mul_lt_mul_left (h : a * b < a * c) : b < c := lt_of_mul_lt_mul_of_nonneg_left h (by simp)

theorem lt_of_mul_lt_mul_right (h : b * a < c * a) : b < c := lt_of_mul_lt_mul_of_nonneg_right h (by simp)

lemma pow_three (x : M) : x^3 = x * x * x := by simp [← two_add_one_eq_three, pow_add, sq]

lemma pow_four (x : M) : x^4 = x * x * x * x := by simp [← three_add_one_eq_four, pow_add, pow_three]

lemma pow_four_eq_sq_sq (x : M) : x^4 = (x^2)^2 := by simp [pow_four, sq, mul_assoc]

instance : CovariantClass M M (· * ·) (· ≤ ·) := ⟨by intro; exact mul_le_mul_left⟩

instance : CovariantClass M M (· + ·) (· ≤ ·) := ⟨by intro; simp⟩

@[simp] lemma one_lt_mul_self_iff {a : M} : 1 < a * a ↔ 1 < a :=
  ⟨(fun h ↦ by push_neg at h ⊢; exact mul_le_one' h h).mtr, fun h ↦ one_lt_mul'' h h⟩

@[simp] lemma one_lt_sq_iff {a : M} : 1 < a^2 ↔ 1 < a := by simp [sq]

@[simp] lemma mul_self_eq_one_iff {a : M} : a * a = 1 ↔ a = 1 :=
  not_iff_not.mp (by simp [ne_iff_lt_or_gt])

@[simp] lemma sq_eq_one_iff {a : M} : a^2 = 1 ↔ a = 1 := by simp [sq]

lemma lt_square_of_lt {a : M} (pos : 1 < a) : a < a^2 := lt_self_pow pos Nat.one_lt_two

lemma two_mul_le_sq {i : M} (h : 2 ≤ i) : 2 * i ≤ i ^ 2 := by simp [sq]; exact mul_le_mul_right h

lemma two_mul_lt_sq {i : M} (h : 2 < i) : 2 * i < i ^ 2 := by
  simp [sq]; exact (mul_lt_mul_right (show 0 < i from pos_of_gt h)).mpr h

lemma succ_le_double_of_pos {a : M} (h : 0 < a) : a + 1 ≤ 2 * a := by
  simpa [two_mul] using pos_iff_one_le.mp h

lemma polynomial_mono (t : Semiterm ℒₒᵣ ξ n) {e₁ e₂ : Fin n → M} {ε₁ ε₂ : ξ → M}
    (he : ∀ i, e₁ i ≤ e₂ i) (hε : ∀ i, ε₁ i ≤ ε₂ i) :
    t.val! M e₁ ε₁ ≤ t.val! M e₂ ε₂ := by
  induction t using Semiterm.arithRec <;> try simp [he, hε, Semiterm.val_func, *]
  case hadd iht ihu => exact add_le_add iht ihu
  case hmul iht ihu => exact mul_le_mul iht ihu (by simp) (by simp)

end Model

end

end Arith

end LO.FirstOrder
