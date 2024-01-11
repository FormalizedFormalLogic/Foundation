import Arithmetization.IOpen

namespace LO.FirstOrder

namespace Arith

noncomputable section

variable {M : Type} [Inhabited M] [DecidableEq M] [ORingSymbol M]
  [Structure ℒₒᵣ M] [Structure.ORing ℒₒᵣ M]
  [𝐏𝐀⁻.Mod M]

namespace Model

section ISigma₀

variable [𝐈𝚺₀.Mod M]

--lemma lt_of_pos {a : M} (pos : 0 < a) : a < 2*a := by exact lt_two_mul_self pos

lemma lt_square_of_lt {a : M} (pos : 1 < a) : a < a^2 := lt_self_pow pos Nat.one_lt_two

lemma IsPow2.mul {a b : M} (ha : IsPow2 a) (hb : IsPow2 b) : IsPow2 (a * b) := by
  wlog hab : a ≤ b
  · simpa [mul_comm] using this hb ha (by simp at hab; exact LT.lt.le hab)
  refine hierarchy_order_induction₀ M Σ 0
    (fun b ↦ ∀ a ≤ b, IsPow2 a → IsPow2 b → IsPow2 (a * b))
    ⟨⟨“∀[#0 < #1 + 1] (!pow2def [#0] → !pow2def [#1] → !pow2def [#0 * #1])”, by simp⟩,
     by intro v; simp [le_iff_lt_succ, Semiformula.eval_substs, Matrix.vecHead, pow2_defined.pval]⟩ ?_ b a hab ha hb
  simp; intro b H a hab ha hb
  have : a = 1 ∨ 1 < a ∧ ∃ a', a = 2 * a' ∧ IsPow2 a' := IsPow2.elim'.mp ha
  rcases this with (rfl | ⟨lta, a, rfl, ha⟩)
  · simpa using hb
  · have : b = 1 ∨ 1 < b ∧ ∃ b', b = 2 * b' ∧ IsPow2 b' := IsPow2.elim'.mp hb
    rcases this with (rfl | ⟨ltb, b, rfl, hb⟩)
    · simpa using ha
    · have ltb : b < 2 * b := by exact lt_two_mul_self (pos_iff_ne_zero.mpr $ by rintro rfl; simp at ltb)
      have hab : a ≤ b := le_of_mul_le_mul_left hab (by simp)
      have : IsPow2 (a * b) := H b ltb a hab (by assumption) (by assumption)
      suffices : IsPow2 (4 * a * b)
      · have : (2 * a) * (2 * b) = 4 * a * b := by simp [mul_assoc, mul_left_comm a 2 b, ←two_mul_two_eq_four]
        simpa [this]
      simpa [mul_assoc, pow2_mul_four] using this

@[simp] lemma IsPow2.mul_iff {a b : M} : IsPow2 (a * b) ↔ IsPow2 a ∧ IsPow2 b :=
  ⟨fun h ↦ ⟨h.of_dvd (by simp), h.of_dvd (by simp)⟩, by rintro ⟨ha, hb⟩; exact ha.mul hb⟩

@[simp] lemma IsPow2.sq {a : M} : IsPow2 (a^2) ↔ IsPow2 a := by
  simp [_root_.sq]

def ext (u z : M) : M := z /ₑ u mod u

def IsPPow2 (x : M) : Prop := sorry

def ppow2def : Σᴬ[0] 1 := sorry

lemma ppow2_defined : Σᴬ[0]-Predicate (IsPPow2 : M → Prop) ppow2def := sorry

namespace IsPPow2

lemma elim {a : M} : IsPPow2 a ↔ a = 2 ∨ ∃ b, a = b^2 ∧ IsPPow2 b := sorry

@[simp] lemma two : IsPPow2 (2 : M) := elim.mpr (Or.inl rfl)

@[simp] lemma not_zero : ¬IsPPow2 (0 : M) := sorry

@[simp] lemma not_one : ¬IsPPow2 (1 : M) := sorry

lemma elim' {a : M} : IsPPow2 a ↔ a = 2 ∨ 2 < a ∧ ∃ b, a = b^2 ∧ IsPPow2 b := by
  by_cases ha : 2 < a <;> simp [ha, ←elim]
  have : a = 0 ∨ a = 1 ∨ a = 2 := by simpa [le_two_iff_eq_zero_or_one_or_two] using ha
  rcases this with (rfl | rfl | rfl) <;> simp

lemma pow2 {a : M} (h : IsPPow2 a) : IsPow2 a := by
  refine hierarchy_order_induction₀ M Σ 0 (fun a ↦ IsPPow2 a → IsPow2 a)
    ⟨⟨“!ppow2def → !pow2def”, by simp⟩, by intro v; simp [pow2_defined.pval, ppow2_defined.pval]⟩ ?_ a h
  simp; intro x ih hx
  have : x = 2 ∨ 2 < x ∧ ∃ y, x = y^2 ∧ IsPPow2 y := IsPPow2.elim'.mp hx
  rcases this with (rfl | ⟨hx, y, rfl, hy⟩)
  · exact pow2_two
  · have : y < y^2 := lt_square_of_lt
      (by by_contra A
          have : y = 0 ∨ y = 1 := le_one_iff_eq_zero_or_one.mp (by simpa using A)
          rcases this with (rfl | rfl) <;> simp at hx)
    simpa using ih y this hy

end IsPPow2

/-

def ExpAux (x y X Y : M) : Prop :=
  (ext (2^2^0) X = 0 ∧ ext (2^2^0) Y = 1) ∧
  (∀ u < y, IsPPow2 u →
    (ext (u^2) X = 2 * ext u X     ∧ ext (u^2) Y = (ext u Y)^2    ) ∨
    (ext (u^2) X = 2 * ext u X + 1 ∧ ext (u^2) Y = 2 * (ext u Y)^2)) ∧
  ∃ u ≤ y^2 + 1, IsPPow2 u ∧ ext u X = x ∧ ext u Y = y

def Exp (x y : M) : Prop := ∃ X < y, ∃ Y < y^4 + 2, ExpAux x y X Y

lemma exp_zero : Exp (0 : M) 1 := by
  have : ExpAux (0 : M) 1 0 2 :=
    ⟨by simp [ext, one_lt_two],
     by intro u hu hp; simp [show u = 0 from lt_one_iff_eq_zero.mp hu] at hp; exact False.elim (not_ppow2_zero hp),
     ⟨2^2^0, by simp [one_add_one_eq_two], ppow2_two, by simp [ext, one_lt_two]⟩⟩
  exact ⟨0, by simp, 2, by simp, this⟩

lemma exp_succ {x y : M} : Exp x y → Exp (2 * x) (y^2) := by
  rintro ⟨X, hX, Y, hY, ⟨hXzero, hYzero⟩, H, u, _, hu, hx, hy⟩

-/

end ISigma₀

end Model

end

end Arith

end LO.FirstOrder
